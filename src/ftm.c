#include "hashtbli.h"
#include "vector.h"

enum l_kind { NONE=0, DB, TMH, PRIM, AP, LAM, IMP, ALL };

struct tm_struct {
  int16_t tag; int16_t maxv;
  uint16_t x; uint16_t y;
  union tm_or_no {
    struct tm_struct *l;
    int32_t no;
  } lno;
  struct tm_struct *r;
  uint64_t id;
  unsigned __int128 fv1;
  unsigned __int128 fv2;
};
typedef struct tm_struct* trm_p;

#define BLOCK_SIZE (1 << 16)

static struct tm_struct **tm;
static uint32_t x; // position of next tm (or length in current block)
static uint32_t y; // current block number
static uint32_t y_len; // allocated blocks
static uint32_t start_x; // Used by pre-hashed terms not cleared (DBs)

static uint8_t *id; // Hash of all used hashes
static uint32_t idmaxelem;

struct hashtbli2 imps, aps, lams, alls;
struct hashtbli3 uhsh, shsh;

static trm_p dbs[256];
static struct vector tmhs, prims;

enum t_kind { TNONE=0, TLAM, TALL, TAPR, TAPD, TIMPR, TIMPD };
struct ftask {
  int16_t ttag;
  trm_p t;
  int32_t i;
  int64_t h1, h2;
};

static uint32_t tasks_len;
static struct ftask *tasks;

static void print(trm_p t) {
  switch (t->tag) {
  case DB:
    printf("D%i", t->lno.no);
    break;
  case PRIM:
    printf("P%i", t->lno.no);
    break;
  case TMH:
    printf("T%i", t->lno.no);
    break;
  case AP:
    printf("("); print(t->lno.l); printf(" "); print(t->r); printf(")");
    break;
  case IMP:
    printf("("); print(t->lno.l); printf(" -> "); print(t->r); printf(")");
    break;
  case LAM:
    printf("(\\:%i.", t->lno.no); print(t->r); printf(")");
    break;
  case ALL:
    printf("(!."); print(t->r); printf(")");
    break;
  }
}

static trm_p tmp[1<<26];

static uint64_t tm_size(trm_p t) {
  int64_t r = 0; tmp[0] = t; int32_t tmp_l = 1;
  while (tmp_l > 0) {
    r++; tmp_l--; t=tmp[tmp_l];
    switch (t->tag) {
    case AP: case IMP: tmp[tmp_l] = t->lno.l; tmp_l++; // Intentional roll-over
    case LAM: case ALL: tmp[tmp_l] = t->r; tmp_l++;
    }
  }
  return r;
}

// TODO check if assignments only if different is faster?
static void double_id() {
  // printf("i"); fflush (stdout);
  uint32_t newmaxelem = (idmaxelem << 1) + 1;
  id=recalloc(id, idmaxelem + 1, newmaxelem + 1, sizeof(uint8_t));
  for (int i = 0; i <= y; ++i) {
    for (int j = 0; j < ((i == y) ? x : BLOCK_SIZE); ++j) {
      id[tm[i][j].id & idmaxelem]=0;
      id[tm[i][j].id & newmaxelem]=1;
    }
  }
  idmaxelem = newmaxelem;
}

static uint64_t new_id() {
  uint64_t r = rand();
  // make sure hashes are non-zero to allow having them as options
  while (id[r & idmaxelem] || r == 0)
    r = rand();
  id[r & idmaxelem] = 1;
  return r;
}

static void tm_id_clear() {
  for (int i = 0; i <= y; ++i) {
    for (int j = ((i == 0) ? start_x : 0); j < ((i == y) ? x : BLOCK_SIZE); ++j) {
      id[tm[i][j].id & idmaxelem]=0;
    }
  }
  y=0; x=start_x;
}

// Finds next position in blocks and returns a cell with x and y set.
static trm_p incr_xy() {
  if (x >= BLOCK_SIZE) {
    x = 0; y++;
    if (y >= y_len) {
      tm[y] = calloc(BLOCK_SIZE, sizeof(struct tm_struct));
      if (!tm[y]) { printf("incr_xy: Out of memory!\n"); fflush(stdout); }
      y_len++;
    }
    if ((y + 1) * BLOCK_SIZE > (idmaxelem >> 1)) // space for x to grow
      double_id();
  }
  tm[y][x].x=x; tm[y][x].y=y;
  return &tm[y][x++];
}

static trm_p add_tm_l(int16_t tag, int16_t maxv, trm_p l, trm_p r, unsigned __int128 fv1, unsigned __int128 fv2) {
  trm_p ret = incr_xy();
  ret->tag = tag; ret->maxv = maxv; ret->lno.l = l; ret->r = r; ret->id = new_id(); ret->fv1 = fv1; ret->fv2 = fv2;
  return ret;
}

static trm_p add_tm_no(int16_t tag, int16_t maxv, int64_t no, trm_p r, unsigned __int128 fv1, unsigned __int128 fv2) {
  trm_p ret = incr_xy();
  ret->tag = tag; ret->maxv = maxv; ret->lno.no = no; ret->r = r; ret->id = new_id(); ret->fv1 = fv1; ret->fv2 = fv2;
  return ret;
}

// vector of task vectors at depths
#define MAX_SUBST_DEPTH 16
struct ftask *stasks[MAX_SUBST_DEPTH];
uint32_t stasks_len[MAX_SUBST_DEPTH];

static void alloc_stasks(int32_t depth) {
// printf("Alloc stasks at depth: %i\n", depth);
  stasks_len[depth] = 1 << 16;
  stasks[depth] = calloc(stasks_len[depth], sizeof(struct ftask));
}

static void init_dbs() {
  tm = calloc(BLOCK_SIZE, sizeof(struct tm_struct *));
  x = 0; y = 0; y_len = 8;
  for (int i = 0; i < y_len; ++i)
    tm[i] = calloc(BLOCK_SIZE, sizeof(struct tm_struct));
  id = calloc(1 << 20, sizeof(uint8_t));
  idmaxelem = (1 << 20) - 1;
  hashtbli2_make(&imps,  1 << 19);
  hashtbli2_make(&aps,   1 << 19);
  hashtbli2_make(&lams,  1 << 16);
  hashtbli2_make(&alls,  1 << 18);
  for (int i = 0; i < 128; ++i)
    dbs[i] = add_tm_no(DB, i+1, i, NULL, 0, ((unsigned __int128)1)<<i);
  for (int i = 128; i < 256; ++i)
    dbs[i] = add_tm_no(DB, i+1, i, NULL, ((unsigned __int128)1)<<i, 0);
  vector_make(&tmhs, 1 << 12);
  vector_make(&prims, 1 << 12);
  tasks_len = 1 << 16; tasks = calloc(tasks_len, sizeof(struct ftask));
  alloc_stasks(0); alloc_stasks(1); alloc_stasks(2); alloc_stasks(3);
  start_x = x;
  hashtbli3_make(&uhsh, 1 << 18);
  hashtbli3_make(&shsh, 1 << 20);
}

static int32_t max32(int32_t a, int32_t b) {
  return ((a) > (b)) ? a : b;
}

static trm_p mk_imp(trm_p l, trm_p r) {
  uint32_t pos = hashtbli2_find_index(&imps, l->id, r->id);
  if (imps.d[pos].data) return imps.d[pos].data;
  return(hashtbli2_add_atpos(&imps, pos, l->id, r->id,
    add_tm_l(IMP, max32(l->maxv,r->maxv), l, r, l->fv1 | r->fv1, l->fv2 | r->fv2)));
}

static trm_p mk_ap(trm_p l, trm_p r) {
  uint32_t pos = hashtbli2_find_index(&aps, l->id, r->id);
  if (aps.d[pos].data) return aps.d[pos].data;
  return(hashtbli2_add_atpos(&aps, pos, l->id, r->id,
    add_tm_l(AP, max32(l->maxv,r->maxv), l, r, l->fv1 | r->fv1, l->fv2 | r->fv2)));
}

static trm_p mk_lam(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&lams, ((uint64_t)tyno)<<10, t->id);
  if (lams.d[pos].data) return lams.d[pos].data;
  return(hashtbli2_add_atpos(&lams, pos, ((uint64_t)tyno)<<10, t->id,
    add_tm_no(LAM, max32(0,t->maxv-1), tyno, t, t->fv1>>1, (t->fv2>>1) | ((t->fv1 & 1) << 127))));
}

static trm_p mk_all(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&alls, ((uint64_t)tyno)<<10, t->id);
  if (alls.d[pos].data) return alls.d[pos].data;
  return(hashtbli2_add_atpos(&alls, pos, ((uint64_t)tyno)<<10, t->id,
    add_tm_no(ALL, max32(0,t->maxv-1), tyno, t, t->fv1>>1, (t->fv2>>1) | ((t->fv1 & 1) << 127))));
}

static trm_p mk_db(uint32_t vno) {
  if (vno > 255 || vno < 0) {
    printf("mk_db called with %i!!!\nproceeding with incorrect DB number!!\n", vno);
    vno = 0;
    fflush(stdout);
  }
  return dbs[vno];
}

static trm_p mk_prim(uint32_t no) {
  while (prims.len <= no)
    vector_resize(&prims, prims.len << 1);
  if (prims.data[no]) return prims.data[no];
  prims.data[no] = add_tm_no(PRIM, 0, no, NULL, 0, 0);
  return prims.data[no];
}

static trm_p mk_tmh(uint32_t no) {
  while (tmhs.len <= no)
    vector_resize(&tmhs, tmhs.len << 1);
  if (tmhs.data[no]) return tmhs.data[no];
  tmhs.data[no] = add_tm_no(TMH, 0, no, NULL, 0, 0);
  return tmhs.data[no];
}

// TODO check if length of tasks is ok, or just make them vectors.
void add_task5(struct ftask* tsk, int16_t tag, trm_p t, int32_t i, int64_t h1, int64_t h2) {
  tsk->ttag=tag; tsk->t=t; tsk->i=i; tsk->h1=h1; tsk->h2=h2;
}

void add_task4(struct ftask* tsk, int16_t tag, int32_t i, int64_t h1, int64_t h2) {
  tsk->ttag=tag; tsk->i=i; tsk->h1=h1; tsk->h2=h2;
}

// #define CACHE_SUBST

#ifdef CACHE_SUBST
#define SAVE_SUBST(a,b,c,d,e) { hashtbli3_add(a,b,c,d,e);}
#else
#define SAVE_SUBST(a,b,c,d,e) ;
#endif

static trm_p uptrm_tt(trm_p t, int32_t i, int32_t j) {
  bool istm=true; int32_t tl=0; trm_p t2;
  while (true) {
    if (istm) {
      if (t->maxv <= i) {istm = false; continue; }
#ifdef CACHE_SUBST
      t2 = hashtbli3_find (&uhsh, t->id, i << 10, j << 20);
      if (t2) {istm = false; t = t2; continue; }
#endif
      if (tl >= tasks_len) {
        printf ("Extendings u-tasks to: %li MB\n", (tasks_len * sizeof(struct ftask)) >> 19);
        tasks=recalloc(tasks, tasks_len, tasks_len << 1, sizeof(struct ftask));
        tasks_len = tasks_len << 1;
      }
      switch (t->tag) {
        case AP:  add_task5(&tasks[tl], TAPR,  t->r, i, t->id, i << 10); t=t->lno.l; tl++; continue;
        case IMP: add_task5(&tasks[tl], TIMPR, t->r, i, t->id, i << 10); t=t->lno.l; tl++; continue;
        case DB: istm = false; if (t->lno.no >= i) t = mk_db(t->lno.no+j); continue;
        case ALL: add_task4(&tasks[tl], TALL, t->lno.no, t->id, i << 10); t=t->r; i++; tl++; continue;
        case LAM: add_task4(&tasks[tl], TLAM, t->lno.no, t->id, i << 10); t=t->r; i++; tl++; continue;
        default: istm = false;
      }
    } else {
      if (tl <= 0) return t;
      tl--;
      switch (tasks[tl].ttag) {
        case TAPR: istm=true; t2=t; t=tasks[tl].t; i=tasks[tl].i; tasks[tl].ttag=TAPD; tasks[tl].t=t2; tl++; continue;
        case TAPD: t=mk_ap(tasks[tl].t, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); continue;
        case TIMPR: istm=true; t2=t; t=tasks[tl].t; i=tasks[tl].i; tasks[tl].ttag=TIMPD; tasks[tl].t=t2; tl++; continue;
        case TIMPD: t=mk_imp(tasks[tl].t, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); continue;
        case TALL: t=mk_all(tasks[tl].i, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); continue;
        default: t=mk_lam(tasks[tl].i, t); SAVE_SUBST(&uhsh, tasks[tl].h1, tasks[tl].h2, j << 20, t); // TLAM
      }
    }
  }
}


/*
static trm_p uptrm_rec(trm_p t, int32_t i, int32_t j) {
  if (t->maxv <= i)
    return t;
  switch (t->tag) {
  case AP:
    return mk_ap(uptrm_rec(t->lno.l, i, j), uptrm_rec(t->r, i, j));
  case DB:
    {const int32_t k = t->lno.no;
    return mk_db( (k < i) ? k : k + j);}
  case IMP:
    return mk_imp(uptrm_rec(t->lno.l, i, j), uptrm_rec(t->r, i, j));
  case ALL:
    return mk_all(t->lno.no, uptrm_rec(t->r, (i + 1), j));
  case LAM:
    return mk_lam(t->lno.no, uptrm_rec(t->r, (i + 1), j));
  }
  return t;
}
*/

static trm_p uptrm(trm_p t, int32_t i, int32_t j) {
  if (j == 0) return t;
  return uptrm_tt(t, i, j);
}

static trm_p mk_norm_lam(uint32_t tyno, trm_p t) {
  uint32_t pos = hashtbli2_find_index(&lams, ((uint64_t)tyno)<<10, t->id);
  if (lams.d[pos].data) return lams.d[pos].data;
  if (t->tag!=AP || t->r->tag!=DB || t->r->lno.no!=0 || (t->lno.l->fv2 & 1) != 0)
    return(hashtbli2_add_atpos(&lams, pos, ((uint64_t)tyno)<<10, t->id,
      add_tm_no(LAM, max32(0,t->maxv-1), tyno, t, t->fv1>>1, (t->fv2>>1) | ((t->fv1 & 1) << 127))));
  trm_p nt = uptrm(t->lno.l, 0, -1); // Positions can change un uptrm, eg resize could happen
  return hashtbli2_add(&lams, ((uint64_t)tyno)<<10, t->id, nt);
}

static bool is_fv_0(trm_p t, int32_t j) {
  return (j < 128) ? (((t->fv2 >> j) & 1) == 0) : (((t->fv1 >> j) & 1) == 0);
}

static trm_p subst_tt(trm_p t, int32_t j, trm_p s, int32_t depth) {
  if (!stasks[depth])
    alloc_stasks(depth);
  struct ftask *tasks=stasks[depth];
  uint32_t tasks_len=stasks_len[depth];
  bool istm=true; int32_t tl=0; trm_p t2, t3;
  while (true) {
    if (istm) {
      if (t->maxv <= j) {istm = false; continue; }
      if (is_fv_0(t, j)) {t=uptrm(t, j, -1); istm = false; continue; }
#ifdef CACHE_SUBST
      t2 = hashtbli3_find (&shsh, t->id, j << 10, s->id);
      if (t2) {istm = false; t = t2; continue; }
#endif
      if (tl >= tasks_len) {
        printf ("Extendings s-tasks to: %li MB\n", (tasks_len * sizeof(struct ftask)) >> 20);
        stasks[depth]=recalloc(stasks[depth], stasks_len[depth], stasks_len[depth] << 1, sizeof(struct ftask));
        stasks_len[depth] = stasks_len[depth] << 1;
        tasks=stasks[depth]; tasks_len=stasks_len[depth];
      }
      switch (t->tag) {
        case AP:  add_task5(&tasks[tl], TAPR,  t->r, j, t->id, j << 10); t=t->lno.l; tl++; continue;
        case IMP: add_task5(&tasks[tl], TIMPR, t->r, j, t->id, j << 10); t=t->lno.l; tl++; continue;
        case DB: istm = false; t = uptrm(s, 0, j); continue;
        case ALL: add_task4(&tasks[tl], TALL, t->lno.no, t->id, j << 10); t=t->r; j++; tl++; continue;
        case LAM: add_task4(&tasks[tl], TLAM, t->lno.no, t->id, j << 10); t=t->r; j++; tl++; continue;
        default: istm = false;
      }
    } else {
      if (tl <= 0) return t;
      tl--;
      switch (tasks[tl].ttag) {
        case TAPR: istm=true; t2=t; t=tasks[tl].t; j=tasks[tl].i; tasks[tl].ttag=TAPD; tasks[tl].t=t2; tl++; continue;
        case TAPD:
          t2 = tasks[tl].t; // left side of the application
          uint32_t subst_ret_pos = hashtbli2_find_index (&aps, t2->id, t->id);
          if (aps.d[subst_ret_pos].data)
            t = aps.d[subst_ret_pos].data;
          else {
            if (t2->tag!=LAM) {
              t3 = add_tm_l(AP, max32(t2->maxv,t->maxv), t2, t, t2->fv1 | t->fv1, t2->fv2 | t->fv2);
              t = hashtbli2_add_atpos(&aps, subst_ret_pos, t2->id, t->id, t3);
            } else t = subst_tt(t2->r, 0, t, depth + 1); // outside call
          }
          SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); continue;
        case TIMPR: istm=true; t2=t; t=tasks[tl].t; j=tasks[tl].i; tasks[tl].ttag=TIMPD; tasks[tl].t=t2; tl++; continue;
        case TIMPD: t=mk_imp(tasks[tl].t, t); SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); continue;
        case TALL: t=mk_all(tasks[tl].i, t); SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); continue;
        default: t=mk_norm_lam(tasks[tl].i, t); SAVE_SUBST(&shsh, tasks[tl].h1, tasks[tl].h2, s->id, t); // TLAM
      }
    }
  }
}

/*
static trm_p mk_norm_ap(trm_p l, trm_p r);

static trm_p subst(trm_p t, int32_t j, trm_p s) {
  if (t->maxv <= j)
    return t;
  if (((t->fv >> j) & 1) == 0)
    return uptrm(t, j, -1);
  switch (t->tag) {
  case DB:
    return uptrm(s, 0, j);
  case AP:
    return mk_norm_ap(subst(t->lno.l, j, s), subst(t->r, j, s));
  case IMP:
    return mk_imp(subst(t->lno.l, j, s), subst(t->r, j, s));
  case LAM:
    return mk_norm_lam(t->lno.no, subst(t->r, (j + 1), s));
  case ALL:
    return mk_all(t->lno.no, subst(t->r, (j + 1), s));
  }
  return t;
}
*/

static trm_p mk_norm_ap(trm_p l, trm_p r) {
  uint32_t pos = hashtbli2_find_index(&aps, l->id, r->id);
  if (aps.d[pos].data) return aps.d[pos].data;
  if (l->tag!=LAM)
    return(hashtbli2_add_atpos(&aps, pos, l->id, r->id,
      add_tm_l(AP, max32(l->maxv,r->maxv), l, r, l->fv1 | r->fv1, l->fv2 | r->fv2)));
  trm_p nt = subst_tt(l->r, 0, r, 0);  // Positions can change in subst
  return (hashtbli2_add(&aps, l->id, r->id, nt));
}

#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>

#define Tm_val(i)     (&tm[Int_val(i) >> 16][Int_val(i) & 0xFFFF])
static value Val_tm(trm_p p) {return Val_int((p->y << 16) | p->x);}

value c_mk_imp(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_imp(Tm_val(l), Tm_val(r))));
}

value c_mk_ap(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_ap(Tm_val(l), Tm_val(r))));
}

value c_mk_norm_ap(value l, value r) {
  CAMLparam2(l,r);
  CAMLreturn(Val_tm(mk_norm_ap(Tm_val(l), Tm_val(r))));
}

value c_mk_lam(value n, value r) {
  CAMLparam2(n,r);
  CAMLreturn(Val_tm(mk_lam(Int_val(n), Tm_val(r))));
}

value c_mk_norm_lam(value n, value r) {
  CAMLparam2(n,r);
  CAMLreturn(Val_tm(mk_norm_lam(Int_val(n), Tm_val(r))));
}

value c_mk_all(value n, value r) {
  CAMLparam2(n,r);
  CAMLreturn(Val_tm(mk_all(Int_val(n), Tm_val(r))));
}

void c_init_dbs(value unit) {
  CAMLparam1(unit);
  init_dbs();
  CAMLreturn0;
}

value c_mk_db(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_db(Int_val(n))));
}

value c_mk_prim(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_prim(Int_val(n))));
}

value c_mk_tmh(value n) {
  CAMLparam1(n);
  CAMLreturn(Val_tm(mk_tmh(Int_val(n))));
}

value c_uptrm(value t, value i, value j) {
  CAMLparam3(t,i,j);
  CAMLreturn(Val_tm(uptrm(Tm_val(t),Int_val(i),Int_val(j))));
}

value c_subst(value t, value i, value s) {
  CAMLparam3(t,i,s);
  CAMLreturn(Val_tm(subst_tt(Tm_val(t),Int_val(i),Tm_val(s), 0)));
}

value c_get_tag(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_int(Tm_val(t)->tag));
}

value c_get_no(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_long(Tm_val(t)->lno.no));
}

value c_get_l(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_tm(Tm_val(t)->lno.l));
}

value c_get_r(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_tm(Tm_val(t)->r));
}

value c_get_maxv(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_long(Tm_val(t)->maxv));
}

value c_get_fv0_0(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_bool((Tm_val(t)->fv2 & 1) == 0));
}

void c_hash_clear(value unit) {
  CAMLparam1(unit);
  vector_clear(&prims);
  vector_clear(&tmhs);
  hashtbli2_clear(&imps);
  hashtbli2_clear(&aps);
  hashtbli2_clear(&lams);
  hashtbli2_clear(&alls);
  tm_id_clear();
  hashtbli3_clear(&uhsh);
  hashtbli3_clear(&shsh);
  CAMLreturn0;
}

void c_print(value t) {
  CAMLparam1(t);
  print(Tm_val(t)); printf("\n"); fflush(stdout);
  CAMLreturn0;
}

value c_size(value t) {
  CAMLparam1(t);
  CAMLreturn(Val_long(tm_size(Tm_val(t))));
}
