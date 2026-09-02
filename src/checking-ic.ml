(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2016 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hashaux
open Hash
open Logic
open Mathdata

let curritem = ref ""
let counterbound = 150000000
exception CheckingBd
let cnt counter = (incr counter; if false (* !counter >= counterbound *) then raise CheckingBd)
let dbbound = 256

(* <<<<<<<<<<<<<<<<<<<<<<<< *)

let ty_no_h=(Hashtbl.create 1000 : (stp, int) Hashtbl.t);;
let no_ty_h=(Hashtbl.create 1000 : (int, stp) Hashtbl.t);;
let ty_num=ref 0;;

let ty_f ty =
  try Hashtbl.find ty_no_h ty
  with Not_found ->
    incr ty_num;
    Hashtbl.add ty_no_h ty !ty_num;
    Hashtbl.add no_ty_h !ty_num ty;
    !ty_num
and ty_f_rev = Hashtbl.find no_ty_h;;

let hv_no=(Hashtbl.create 1000 : (hashval, int) Hashtbl.t);;
let no_hv=(Hashtbl.create 1000 : (int, hashval) Hashtbl.t);;
let hh_num=ref 0;;

let hh_no s =
  try Hashtbl.find hv_no s
  with Not_found ->
    incr hh_num;
    Hashtbl.add hv_no s !hh_num;
    Hashtbl.add no_hv !hh_num s;
    !hh_num
and hh_no_rev = Hashtbl.find no_hv;;

external ftrm_hash_clear : unit -> unit = "c_hash_clear" [@@noalloc];;

let ftrm_hash_clear () =
  ftrm_hash_clear ();
  Hashtbl.reset ty_no_h;
  Hashtbl.reset no_ty_h;
  Hashtbl.reset hv_no;
  Hashtbl.reset no_hv;
  ty_num := 0;
  hh_num := 0;;

type ftp=int;;
type ftm=int;;

external init_dbs : unit -> unit = "c_init_dbs";;
init_dbs ();;

external mk_db : int -> ftm = "c_mk_db" [@@noalloc];;
let mk_db i =
  if i >= dbbound then (Printf.printf "mk_db too high: %d\n" i; flush stdout; raise CheckingBd);
  mk_db i;;
external mk_tmh_internal : int -> ftm = "c_mk_tmh" [@@noalloc];;
let mk_tmh s = mk_tmh_internal (hh_no s);;
external mk_prim : int -> ftm = "c_mk_prim" [@@noalloc];;
external mk_ap : ftm -> ftm -> ftm = "c_mk_norm_ap" [@@noalloc];;
external mk_imp : ftm -> ftm -> ftm = "c_mk_imp" [@@noalloc];;
external mk_lam : ftp -> ftm -> ftm = "c_mk_norm_lam" [@@noalloc];;
external mk_all : ftp -> ftm -> ftm = "c_mk_all" [@@noalloc];;

type ftm_tag =
| FT_None
| FT_DB
| FT_TmH
| FT_Prim
| FT_Ap
| FT_Lam
| FT_Imp
| FT_All;;

external get_tag : ftm -> ftm_tag = "c_get_tag" [@@noalloc];;

external get_no : ftm -> int = "c_get_no" [@@noalloc];;
external get_l : ftm -> ftm = "c_get_l" [@@noalloc];;
external get_r : ftm -> ftm = "c_get_r" [@@noalloc];;
external get_maxv : ftm -> int = "c_get_maxv" [@@noalloc];;
external get_fv0_0 : ftm -> bool = "c_get_fv0_0" [@@noalloc];;

external uptrm : ftm -> int -> int -> ftm = "c_uptrm" [@@noalloc];;
external subst : ftm -> int -> ftm -> ftm = "c_subst" [@@noalloc];;

external print : ftm -> unit = "c_print" [@@noalloc];;
external size : ftm -> int = "c_size" [@@noalloc];;

let mk_ex a t1 =
  let t2 = uptrm t1 1 1 in
  mk_all (ty_f Prop) (mk_imp (mk_all a (mk_imp t2 (mk_db 1))) (mk_db 0));;

let mk_eq a t1 t2 =
  let t1b = uptrm t1 0 1 in
  let t2b = uptrm t2 0 1 in
  let at = ty_f_rev a in
  let ty_aap = ty_f (TpArr(at,TpArr(at,Prop))) in
  mk_all ty_aap (mk_imp (mk_ap (mk_ap (mk_db 0) t1b) t2b) (mk_ap (mk_ap (mk_db 0) t2b) t1b));;

let ftrm_trm counter m = failwith "ftrm_trm: unimplemented";;
let ftrma_trm counter (m,_,_,_) = failwith "ftrma_trm: unimplemented";;

let rec trm_ftrma m =
  match m with
  | TmH(_,h) -> mk_tmh h
  | DB(_,i) -> mk_db i
  | Prim(_,i) -> mk_prim i
  | Ap(_,m1,m2) -> mk_ap (trm_ftrma m1) (trm_ftrma m2)
  | Lam(_,a,m1) -> mk_lam (ty_f a) (trm_ftrma m1)
  | Imp(_,m1,m2) -> mk_imp (trm_ftrma m1) (trm_ftrma m2)
  | All(_,a,m1) -> mk_all (ty_f a) (trm_ftrma m1)
  | Ex(_,a,m1) -> mk_ex (ty_f a) (trm_ftrma m1)
  | Eq(_,a,m1,m2) -> mk_eq (ty_f a) (trm_ftrma m1) (trm_ftrma m2)

(* >>>>>>>>>>>>>>>>>>>>>>> *)
(* <<<<<<<<<<<<<<<<<<<<<<< *)

let rec get_stp_trm_raise counter ctx tys t thy =
  cnt counter;
  match t with
  | DB(pos,i) -> (try List.nth ctx i with exc -> if !debug then Printf.printf "%sdangling DB at pos %d; %s\n" !curritem pos (Printexc.to_string exc); raise exc);
  | TmH(pos,h) -> (try Hashtbl.find tys h with exc -> if !debug then Printf.printf "%sunknown TmH at pos %d; %s\n" !curritem pos (Printexc.to_string exc); raise exc);
  | Prim(pos,i) -> (try List.nth thy i with exc -> if !debug then Printf.printf "%sdangling Prim at pos %d; %s\n" !curritem pos (Printexc.to_string exc); raise exc);
  | Ap (pos, t1, t2) ->
     let s = get_stp_trm_raise counter ctx tys t1 thy in
     (match s with
      | TpArr (b, alpha) ->
         let b2 = get_stp_trm_raise counter ctx tys t2 thy in
         if b2 = b then alpha else (if !debug then Printf.printf "%sAp arg type mismatch at %d\n" !curritem pos; raise Not_found)
      | _ -> (if !debug then Printf.printf "%sAp func not arrow type at %d\n" !curritem pos; raise Not_found))
  | Lam (_, a1, t1) ->
     TpArr (a1, get_stp_trm_raise counter (a1 :: ctx) tys t1 thy)
  | Imp (pos, t1, t2) ->
     let a = get_stp_trm_raise counter ctx tys t1 thy in
     let b = get_stp_trm_raise counter ctx tys t2 thy in
     if a = Prop then
       if b = Prop then
         Prop
       else
         (if !debug then Printf.printf "%sconclusion of imp at %d is not type Prop\n" !curritem pos; raise Not_found)
     else
       (if !debug then Printf.printf "%santecedent of imp at %d is not type Prop\n" !curritem pos; raise Not_found)
  | All (pos, b, t1) | Ex (pos, b, t1) ->
     if get_stp_trm_raise counter (b :: ctx) tys t1 thy = Prop then
       Prop
     else
       (if !debug then Printf.printf "%sbody of All or Ex at %d is not type Prop\n" !curritem pos; raise Not_found)
  | Eq (pos, b, t1, t2) ->
     let b1 = get_stp_trm_raise counter ctx tys t1 thy
     and b2 = get_stp_trm_raise counter ctx tys t2 thy in
     if b1 = b && b2 = b then
       Prop
     else
       (if !debug then Printf.printf "%stype mismatch in Eq at %d\n" !curritem pos; raise Not_found);;

let head_args t =
  let rec ha args tt =
    match get_tag tt with
    | FT_Ap -> ha ((get_r tt)::args) (get_l tt)
    | _ -> (tt,args)
  in
  ha [] t;;

let delta defs h args =
  match Hashtbl.find defs (hh_no_rev (get_no h)) with
  | (_, def) -> Some (List.fold_left mk_ap def args)
  | exception Not_found -> None;;

(*
let rec conv defs m n =
  m == n ||
  match (head_args m), (head_args n) with
  | (mh, (_ :: _ as ma)), (nh, (_ :: _ as na)) when
     (mh == nh && List.length ma = List.length na && List.for_all2 (conv defs) ma na) -> true
  | (F_TmH mhd, ma), _ when Hashtbl.mem defs mhd ->
     (match delta defs mhd ma with Some m' -> conv defs m' n | None -> false)
  | _, (F_TmH nhd, na) ->
     (match delta defs nhd na with Some n' -> conv defs m n' | None -> false)
  | (F_Imp(m1,m2), _), (F_Imp(n1,n2), _) -> conv defs m1 n1 && conv defs m2 n2
  | (F_All(a1,m1), _), (F_All(b1,n1), _)
  | (F_Lam(a1,m1), _), (F_Lam(b1,n1), _) -> a1 = b1 && conv defs m1 n1
  | _ -> false;;
*)

(* List version to translate to imperative code. *)
let rec conv defs l =
  match l with
  | [] -> true
  | (m, n) :: t ->
     if m == n then conv defs t else
     let (mh, ma) = head_args m and (nh, na) = head_args n in
     match ma, na with (_ :: _, _ :: _) when
       (mh == nh && List.length ma = List.length na && conv defs (List.combine ma na)) -> conv defs t
     | _ ->
       match get_tag mh, get_tag nh with
     | FT_TmH, _ when Hashtbl.mem defs (hh_no_rev (get_no mh)) ->
        (match delta defs mh ma with Some m' -> conv defs ((m', n) :: t) | None -> false)
     | _, FT_TmH ->
        (match delta defs nh na with Some n' -> conv defs ((m, n') :: t) | None -> false)
     | FT_Imp, FT_Imp -> conv defs ((get_l m, get_l n) :: (get_r m, get_r n) :: t)
     | FT_All, FT_All
     | FT_Lam, FT_Lam -> get_no m = get_no n && conv defs ((get_r m, get_r n) :: t)
     | _ -> false;;

let rec headnorm defs t =
  let th, ta = head_args t in
  match get_tag th with
  | FT_TmH ->
     (match Hashtbl.find defs (hh_no_rev (get_no th)) with
     | (_, def) -> headnorm defs (List.fold_left mk_ap def ta)
     | exception Not_found -> t)
  | _ -> t;;


let rec get_prop_pf_raise counter ctx phi tys defs kl p thy : ftm =
  cnt counter;
  match p with
  | Known (pos, h) -> (try snd (Hashtbl.find kl h) with Not_found -> if !debug then Printf.printf "%sUnknown Known %s at %d\n" !curritem (hashval_hexstring h) pos; raise Not_found);
  | Hyp (pos, i) ->
     begin
       try
         let x = List.nth phi i in
         let (i, t) = !x in
         if i = 0 then t else (let t' = uptrm t 0 i in x := (0, t'); t')
       with exc ->
             if !debug then Printf.printf "%sdangling Hyp at %d; %s\n" !curritem pos (Printexc.to_string exc);
             raise exc
     end
  | PrAp (pos,p1, p2) ->
     let t = headnorm defs (get_prop_pf_raise counter ctx phi tys defs kl p1 thy) in
     if get_tag t <> FT_Imp then (if !debug then Printf.printf "%sPrAp not Imp at %d\n" !curritem pos; raise Not_found);
     let t1 = get_l t and t2 = get_r t in
     if not (conv defs [get_prop_pf_raise counter ctx phi tys defs kl p2 thy, t1]) then (if !debug then Printf.printf "%sPrAp mismatch at %d\n" !curritem pos; raise Not_found);
     t2
  | TmAp (pos, p1, t1) ->
     let t = headnorm defs (get_prop_pf_raise counter ctx phi tys defs kl p1 thy) in
     if get_tag t <> FT_All then (if !debug then Printf.printf "%sTmAp not All at %d\n" !curritem pos; raise Not_found);
     let a = get_no t and m = get_r t in
     let cx = get_maxv m in
     if ty_f (get_stp_trm_raise counter ctx tys t1 thy) <> a then (if !debug then Printf.printf "%sTmAp mismatch at %d\n" !curritem pos; raise Not_found);
     if cx <= 0 then m else
     if get_fv0_0 m then uptrm m 0 (-1) else
     let t1b = trm_ftrma t1 in
     subst m 0 t1b
  | PrLa (pos, s, p1) ->
     if get_stp_trm_raise counter ctx tys s thy <> Prop then (if !debug then Printf.printf "%sPrLa bound not Prop at %d\n" !curritem pos; raise Not_found);
     let q = trm_ftrma s in
     mk_imp q (get_prop_pf_raise counter ctx ((ref (0, q)) :: phi) tys defs kl p1 thy)
  | TmLa (_, a1, p1) ->
     let phi2 = List.map (fun x -> let (i, t) = !x in ref (i + 1, t)) phi in
     mk_all (ty_f a1) (get_prop_pf_raise counter (a1 :: ctx) phi2 tys defs kl p1 thy)
  | Ext (_, a, b) ->
     let ta = ty_f a and tb = ty_f b and taab = ty_f (TpArr(a,b)) in
     mk_all taab (mk_all taab (mk_imp
       (mk_all ta (mk_eq tb (mk_ap (mk_db 2) (mk_db 0)) (mk_ap (mk_db 1) (mk_db 0))))
       (mk_eq taab (mk_db 1) (mk_db 0))))

(** val correct_pf_f : int ref ->
    stp list -> trm list -> gsign -> pf -> trm -> stp list -> bool **)
let correct_pf_f counter ctx phi tys defs kl p t thy =
(*  match (p,t) with
  | (TmLa(a1,p1),(F_All(a2,t2),_,_,_)) -> (** assume the a2 = a1, to test savings of making a1 optional here **)
     correct_pf_f counter (ty_f_rev a2 :: ctx) (List.map (fun x -> let (i, t) = !x in ref (i + 1, t)) phi) tys defs kl p1 t2 thy
  | (PrLa(s, p1),(F_Imp(q1, q2),_,_,_)) -> (** do not check the s converts to q1, to test savings of making s optional here **)
     correct_pf_f counter ctx ((ref (0, q1)) :: phi) tys defs kl p1 q2 thy
  | _ ->*)
     match get_prop_pf_raise counter ctx phi tys defs kl p thy with
     | pp -> conv defs [pp, t]
     | exception Not_found -> Printf.printf "not found\n"; false (* List.find *)
     | exception Failure fs -> Printf.printf "failure %s\n" fs; false (* List.nth *)

(*
let hashroots = Array.make 10000000 None;;

let rec tm_hashroot_fun sf (id : int) m =
  match hashroots.(id) with
  | Some r -> r
  | None ->
    let ret =
    match sf,m with
    | _, TmH(h) -> h
    | _, Prim(x) -> hashtag (hashint32 (Int32.of_int x)) 96l
    | _, DB(x) -> hashtag (hashint32 (Int32.of_int x)) 97l
    | [hm; hn], Ap(m,n) -> hashtag (hashpair hm hn) 98l
    | [hm; hn], Imp(m,n) -> hashtag (hashpair hm hn) 100l
    | [hm], Lam(a,m) -> hashtag (hashpair (hashtp a) hm) 99l
    | [hm], All(a,m) -> hashtag (hashpair (hashtp a) hm) 101l
    | [hm], Ex(a,m) -> hashtag (hashpair (hashtp a) hm) 102l
    | [hm; hn], Eq(a,m,n) -> hashtag (hashpair (hashpair (hashtp a) hm) hn) 103l
    | _ -> failwith "tm_hashroot_fun"
    in
    hashroots.(id) <- Some ret;
    ret;;

let tm_hashroot t = Utm.fold_id (Obj.magic tm_hashroot_fun) (Obj.magic t);;
*)

(** val free_trm_trm : int ref -> trm -> int -> bool **)

let rec free_trm_trm counter t i =
  cnt counter;
  match t with
  | DB (_, j) -> i = j
  | Ap (_, m1, m2) -> (||) (free_trm_trm counter m1 i) (free_trm_trm counter m2 i)
  | Lam (_, _, m1) -> free_trm_trm counter m1 ((+) i 1)
  | Imp (_, m1, m2) -> (||) (free_trm_trm counter m1 i) (free_trm_trm counter m2 i)
  | All (_, _, m1) -> free_trm_trm counter m1 ((+) i 1)
  | Ex (_, _, m1) -> free_trm_trm counter m1 ((+) i 1)
  | Eq (_, _, m1, m2) -> (||) (free_trm_trm counter m1 i) (free_trm_trm counter m2 i)
  | _ -> false

(** val is_norm : int ref -> trm -> bool **)

let rec is_norm counter m =
  cnt counter;
  match m with
  | Ap (_, Lam (_, _, _), m2) -> false
  | Ap (_, m1, m2) -> is_norm counter m1 && is_norm counter m2
  | Lam (_, _, Ap (_, f, DB (_, 0))) when not (free_trm_trm counter f 0) -> false
  | Lam (_, _, m1) -> is_norm counter m1
  | Imp (_, m1, m2) -> is_norm counter m1 && is_norm counter m2
  | All (_, _, m1) -> is_norm counter m1
  | Ex (_, _, _) -> false
  | Eq (_, _, _, _) -> false
  | _ -> true

let rec tm_tp_f gvtp tys th h a =
  try let b = Hashtbl.find tys h in a = b
  with Not_found ->
        try
          gvtp th h a
        with Not_found ->
          Printf.printf "Unknown object %s\n" (hashval_hexstring h);
          raise Not_found;;

(** val check_doc_f : int ref ->
    (hashval option -> hashval -> stp -> bool) -> (hashval option -> hashval
    -> bool) -> hashval option -> theory -> stree option -> doc ->
    (gsign_f * hashval list) option
 where gsign_f is
  ((hashval * stp) * trm option * ftrma option) list * (hashval * trm * ftrma) list
 **)

let rec check_doc_f counter gvtp gvkn th thy d =
  let tys = Hashtbl.create 100 and defs = Hashtbl.create 100 and kl = Hashtbl.create 100 in
  let check_doc_f1 d0 () =
    match d0 with
    | Docparam (pos, h, a) ->
       if !debug then curritem := Printf.sprintf "Param at %d\n" pos;
       if not (tm_tp_f gvtp tys th h a) then raise Exit else
       Hashtbl.add tys h a
    | Docdef (pos, _, TmH _) ->
       if !debug then curritem := Printf.sprintf "Trivial Def at %d\n" pos
    | Docdef (pos, a, m) ->
       if !debug then curritem := Printf.sprintf "Def at %d\n" pos;
       if not (is_norm counter m) then raise Exit else
       let h = tm_hashroot m in
       let m2 = trm_ftrma m in
       Hashtbl.add tys h a;
       Hashtbl.add defs h (m, m2)
    | Docknown (pos, p) ->
       if !debug then curritem := Printf.sprintf "Known at %d\n" pos;
       if not (is_norm counter p) then raise Exit else
       if get_stp_trm_raise counter [] tys p (fst thy) <> Prop then raise Exit else
       let k = tm_hashroot p in
       let exists_fun x = (x = k) in
       begin
         try
           if not (List.exists exists_fun (snd thy)) &&
                not (Hashtbl.mem kl k || gvkn th k) then raise Exit else
             let p2 = trm_ftrma p in
             Hashtbl.add kl k (p, p2)
         with Not_found ->
               if !debug then Printf.printf "%sUnknown known %s\n" !curritem (hashval_hexstring k)
       end
    | Docpfof (pos, p, d) ->
       if !debug then curritem := Printf.sprintf "Pfof at %d\n" pos;
       if not (is_norm counter p) then raise Exit;
       if get_stp_trm_raise counter [] tys p (fst thy) <> Prop then raise Exit;
       let p2 = trm_ftrma p in
       if not (correct_pf_f counter [] [] tys defs kl d p2 (fst thy)) then raise Exit else
       let k = tm_hashroot p in
       Hashtbl.add kl k (p, p2)
    | Docconj (pos, p) ->
       if !debug then curritem := Printf.sprintf "Conj at %d\n" pos;
       if not (is_norm counter p) then raise Exit else
       if get_stp_trm_raise counter [] tys p (fst thy) <> Prop then raise Exit else ()
    | Docsigna (_, h) -> raise (Failure "signatures are not allowed")
  in
  try
    List.fold_right check_doc_f1 d ();
    let fdef_to_def h =
      match Hashtbl.find defs h with
      | (d, _) -> Some d
      | exception Not_found -> None in
    let tmtpl = Hashtbl.fold (fun h ty sf -> ((h, ty), fdef_to_def h) :: sf) tys [] in
    let kl = Hashtbl.fold (fun k (p, _) sf -> (k, p) :: sf) kl [] in
    Some (tmtpl, kl)
  with Exit -> None;;

let check_doc counter gvtp gvkn th thy d =
  ftrm_hash_clear();
  (** must be cleared before checking docs or can get mixed with transparent defs from previous docs; must not be cleared within docs since the intermediate signatures have ftrms **)
  check_doc_f counter gvtp gvkn th thy d;;

                       (** term annotated with information about
                           free vars and normality
                           **)
type atrm =
  | A_DB of int
  | A_TmH of hashval
  | A_Prim of int
  | A_Ap of (atrm * (int * int * int) * int * bool) * (atrm * (int * int * int) * int * bool)
  | A_Lam of stp * (atrm * (int * int * int) * int * bool)
  | A_Imp of (atrm * (int * int * int) * int * bool) * (atrm * (int * int * int) * int * bool)
  | A_All of stp * (atrm * (int * int * int) * int * bool)
  | A_Ex of stp * (atrm * (int * int * int) * int * bool)
  | A_Eq of stp * (atrm * (int * int * int) * int * bool) * (atrm * (int * int * int) * int * bool)

type atrma = atrm * (int * int * int) * int * bool

let rec atrm_str m =
  match m with
  | A_DB(i) -> Printf.sprintf "?%d" i
  | A_TmH(h) -> hashval_hexstring h
  | A_Prim(i) -> Printf.sprintf "_%d" i
  | A_Ap(m1,m2) -> Printf.sprintf "Ap %s %s" (atrma_str m1) (atrma_str m2)
  | A_Lam(a,m1) -> Printf.sprintf "Lam %s" (atrma_str m1)
  | A_Imp(m1,m2) -> Printf.sprintf "Imp %s %s" (atrma_str m1) (atrma_str m2)
  | A_All(a,m1) -> Printf.sprintf "All %s" (atrma_str m1)
  | A_Ex(a,m1) -> Printf.sprintf "Ex %s" (atrma_str m1)
  | A_Eq(a,m1,m2) -> Printf.sprintf "Eq %s %s" (atrma_str m1) (atrma_str m2)
and atrma_str (m,(fv2,fv1,fv0),cx,n) =
  if n then
    Printf.sprintf "{%x:%x:%x:%d:%s}" fv2 fv1 fv0 cx (atrm_str m)
  else
    Printf.sprintf "[%x:%x:%x:%d:%s]" fv2 fv1 fv0 cx (atrm_str m)

let bit_90n = [| (0,0,1);(0,0,2);(0,0,4);(0,0,8);(0,0,16);(0,0,32);(0,0,64);(0,0,128);(0,0,256);(0,0,512);(0,0,1024);(0,0,2048);(0,0,4096);(0,0,8192);(0,0,16384);(0,0,32768);(0,0,65536);(0,0,131072);(0,0,262144);(0,0,524288);(0,0,1048576);(0,0,2097152);(0,0,4194304);(0,0,8388608);(0,0,16777216);(0,0,33554432);(0,0,67108864);(0,0,134217728);(0,0,268435456);(0,0,536870912);(0,1,0);(0,2,0);(0,4,0);(0,8,0);(0,16,0);(0,32,0);(0,64,0);(0,128,0);(0,256,0);(0,512,0);(0,1024,0);(0,2048,0);(0,4096,0);(0,8192,0);(0,16384,0);(0,32768,0);(0,65536,0);(0,131072,0);(0,262144,0);(0,524288,0);(0,1048576,0);(0,2097152,0);(0,4194304,0);(0,8388608,0);(0,16777216,0);(0,33554432,0);(0,67108864,0);(0,134217728,0);(0,268435456,0);(0,536870912,0);(1,0,0);(2,0,0);(4,0,0);(8,0,0);(16,0,0);(32,0,0);(64,0,0);(128,0,0);(256,0,0);(512,0,0);(1024,0,0);(2048,0,0);(4096,0,0);(8192,0,0);(16384,0,0);(32768,0,0);(65536,0,0);(131072,0,0);(262144,0,0);(524288,0,0);(1048576,0,0);(2097152,0,0);(4194304,0,0);(8388608,0,0);(16777216,0,0);(33554432,0,0);(67108864,0,0);(134217728,0,0);(268435456,0,0);(536870912,0,0) |]

let zero_90n = (0,0,0)
let or_90n (x2,x1,x0) (y2,y1,y0) = (x2 lor y2,x1 lor y1,x0 lor y0)

let bit0_0_90n (_,_,x0) = x0 land 1 = 0

let bit_0_90n (x2,x1,x0) j =
  match j with
  |  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9
  | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
  | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 -> x0 land (1 lsl j) = 0
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39
  | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 | 48 | 49
  | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 | 58 | 59 -> x1 land (1 lsl (j - 30)) = 0
  | _ -> x2 land (1 lsl (j - 60)) = 0
    
let shift_right_logical_90n_1 (x2,x1,x0) =
  (x2 lsr 1,((x2 land 1) lsl 29) lor (x1 lsr 1),((x1 land 1) lsl 29) lor (x0 lsr 1))

let adb i =
  if i >= dbbound then (Printf.printf "db too high"; raise CheckingBd);
  (A_DB(i),bit_90n.(i),i+1,true)

let atmh h = (A_TmH(h),zero_90n,0,true)

let aprim i = (A_Prim(i),zero_90n,0,true)

let aap (m1,fv1,cx1,n1) (m2,fv2,cx2,n2) =
  if (n1 && n2) then
    begin
      match m1 with
      | A_Lam(_,_) ->
         (A_Ap((m1,fv1,cx1,n1),(m2,fv2,cx2,n2)),or_90n fv1 fv2,max cx1 cx2,false)
      | _ ->
         (A_Ap((m1,fv1,cx1,n1),(m2,fv2,cx2,n2)),or_90n fv1 fv2,max cx1 cx2,true)
    end
  else
    (A_Ap((m1,fv1,cx1,n1),(m2,fv2,cx2,n2)),or_90n fv1 fv2,max cx1 cx2,false)

let aimp (m1,fv1,cx1,n1) (m2,fv2,cx2,n2) =
  (A_Imp((m1,fv1,cx1,n1),(m2,fv2,cx2,n2)),or_90n fv1 fv2,max cx1 cx2,n1 && n2)

let aeq a (m1,fv1,cx1,n1) (m2,fv2,cx2,n2) =
  (A_Eq(a,(m1,fv1,cx1,n1),(m2,fv2,cx2,n2)),or_90n fv1 fv2,max cx1 cx2,false)
    
let alam a (m1,fv1,cx1,n1) =
  let fvnew =
    shift_right_logical_90n_1 fv1
  in
  if n1 then
    begin
      match m1 with
      | A_Ap((m2,fv2,cx2,n2),(A_DB(j),_,_,_)) when j = 0 && bit0_0_90n fv2 -> (** eta **)
         (A_Lam(a,(m1,fv1,cx1,n1)),fvnew,max 0 (cx1 - 1),false)
      | _ ->
         (A_Lam(a,(m1,fv1,cx1,n1)),fvnew,max 0 (cx1 - 1),true)
    end
  else
    (A_Lam(a,(m1,fv1,cx1,n1)),fvnew,max 0 (cx1 - 1),false)

let aall a (m1,fv1,cx1,n1) =
  let fvnew =
    shift_right_logical_90n_1 fv1
  in
  (A_All(a,(m1,fv1,cx1,n1)),fvnew,max 0 (cx1 - 1),n1)

let aex a (m1,fv1,cx1,n1) =
  let fvnew =
    shift_right_logical_90n_1 fv1
  in
  (A_Ex(a,(m1,fv1,cx1,n1)),fvnew,max 0 (cx1 - 1),false)

let rec atrm_trm counter m =
  cnt counter;
  match m with
  | A_DB(i) -> DB(0,i)
  | A_TmH(h) -> TmH(0,h)
  | A_Prim(i) -> Prim(0,i)
  | A_Ap(m1,m2) -> Ap(0,atrma_trm counter m1,atrma_trm counter m2)
  | A_Lam(a,m1) -> Lam(0,a,atrma_trm counter m1)
  | A_Imp(m1,m2) -> Imp(0,atrma_trm counter m1,atrma_trm counter m2)
  | A_All(a,m1) -> All(0,a,atrma_trm counter m1)
  | A_Ex(a,m1) -> Ex(0,a,atrma_trm counter m1)
  | A_Eq(a,m1,m2) -> Eq(0,a,atrma_trm counter m1,atrma_trm counter m2)
and atrma_trm counter (m,_,_,_) = atrm_trm counter m

let rec uptrm_a counter (m,fv,cx,n) i j =
  cnt counter;
  if cx <= i || j = 0 then (** in these cases we know the term won't change **)
    (m,fv,cx,n)
  else
    match m with
    | A_DB k -> if (<) k i then adb k else let k2 = ((+) k j) in adb k2
    | A_Ap (t1, t2) -> aap (uptrm_a counter t1 i j) (uptrm_a counter t2 i j)
    | A_Lam (a1, t1) -> alam a1 (uptrm_a counter t1 ((+) i 1) j)
    | A_Imp (t1, t2) -> aimp (uptrm_a counter t1 i j) (uptrm_a counter t2 i j)
    | A_All (b, t1) -> aall b (uptrm_a counter t1 ((+) i 1) j)
    | A_Ex (b, t1) -> aex b (uptrm_a counter t1 ((+) i 1) j)
    | A_Eq (b, t1, t2) -> aeq b (uptrm_a counter t1 i j) (uptrm_a counter t2 i j)
    | _ -> (m,fv,cx,n)

let rec subst_trmtrm_a counter (m1,fv1,cx1,n1) j s =
  cnt counter;
  if cx1 <= j then (** all free variables below j, so no change at all **)
    (m1,fv1,cx1,n1)
  else if bit_0_90n fv1 j then (** j is not free in m1, but need to shift those after j down **)
    uptrm_a counter (m1,fv1,cx1,n1) j (-1)
  else
    match m1 with
    | A_DB k when k = j -> uptrm_a counter s 0 j
    | A_DB k when j < k -> adb (k - 1)
    | A_DB k -> adb k
    | A_Ap (t1, t2) -> aap (subst_trmtrm_a counter t1 j s) (subst_trmtrm_a counter t2 j s)
    | A_Lam (a1, t1) -> alam a1 (subst_trmtrm_a counter t1 ((+) j 1) s)
    | A_Imp (t1, t2) -> aimp (subst_trmtrm_a counter t1 j s) (subst_trmtrm_a counter t2 j s)
    | A_All (b, t1) -> aall b (subst_trmtrm_a counter t1 ((+) j 1) s)
    | A_Ex (b, t1) -> aex b (subst_trmtrm_a counter t1 ((+) j 1) s)
    | A_Eq (b, t1, t2) -> aeq b (subst_trmtrm_a counter t1 j s) (subst_trmtrm_a counter t2 j s)
    | _ -> (m1,fv1,cx1,n1)

let rec beta_eta_norm1_a counter (m,fv,cx,n) =
  if n then
    (m,fv,cx,n)
  else
    beta_eta_norm1_b counter (m,fv,cx,n)
and beta_eta_norm1_b counter (m,fv,cx,n) =
  match m with
  | A_Ap((A_Lam(_,m2),_,_,_),m3) -> (** beta **)
     let m4 = beta_eta_norm1_a counter m2 in
     let m5 = beta_eta_norm1_a counter m3 in
     subst_trmtrm_a counter m4 0 m5
  | A_Ap(m2,m3) ->
     let m4 = beta_eta_norm1_a counter m2 in
     let m5 = beta_eta_norm1_a counter m3 in
     aap m4 m5
  | A_Lam(a,(A_Ap((m2,fv2,cx2,n2),(A_DB(j),_,_,_)),_,_,_)) when j = 0 && bit0_0_90n fv2 -> (** eta **)
     uptrm_a counter (m2,fv2,cx2,n2) 0 (-1)
  | A_Lam(a,m2) ->
     let m3 = beta_eta_norm1_a counter m2 in
     alam a m3
  | A_Imp(m2,m3) ->
     let m4 = beta_eta_norm1_a counter m2 in
     let m5 = beta_eta_norm1_a counter m3 in
     aimp m4 m5
  | A_All(a,m2) ->
     let m3 = beta_eta_norm1_a counter m2 in
     aall a m3
  | A_Ex(a,m2) ->
     let m3 = beta_eta_norm1_a counter m2 in
     let m4 = uptrm_a counter m3 1 1 in
     aall Prop (aimp (aall a (aimp m4 (adb 1))) (adb 0))
  | A_Eq(a,m2,m3) ->
     let m4 = beta_eta_norm1_a counter m2 in
     let m5 = beta_eta_norm1_a counter m3 in
     let m6 = uptrm_a counter m4 0 1 in
     let m7 = uptrm_a counter m5 0 1 in
     aall (TpArr(a,TpArr(a,Prop))) (aimp (aap (aap (adb 0) m6) m7) (aap (aap (adb 0) m7) m6))
  | _ -> raise (Failure "bug in atrma arg of beta_eta_norm1_a") (** this should not happen since it means the annotated term was normal but the annotation said it wasn't **)

let beta_eta_norm_a counter m =
  let mr = ref m in
  while (let (_,_,_,n) = !mr in not n) do
    mr := beta_eta_norm1_b counter !mr
  done;
  !mr

let rec find counter f l =
  cnt counter;
  match l with
  | [] -> None
  | x :: tl -> if f x then Some x else find counter f tl

let rec trm_atrma counter tmtpl m =
  cnt counter;
  match m with
  | TmH(_,h) ->
     begin
       match find counter (fun ((k,_),_,_) -> k = h) tmtpl with
       | Some(_,_,Some(d)) -> d
       | _ -> atmh h
     end
  | DB(_,i) -> adb i
  | Prim(_,i) -> aprim i
  | Ap(_,m1,m2) -> aap (trm_atrma counter tmtpl m1) (trm_atrma counter tmtpl m2)
  | Lam(_,a,m1) -> alam a (trm_atrma counter tmtpl m1)
  | Imp(_,m1,m2) -> aimp (trm_atrma counter tmtpl m1) (trm_atrma counter tmtpl m2)
  | All(_,a,m1) -> aall a (trm_atrma counter tmtpl m1)
  | Ex(_,a,m1) -> aex a (trm_atrma counter tmtpl m1)
  | Eq(_,a,m1,m2) -> aeq a (trm_atrma counter tmtpl m1) (trm_atrma counter tmtpl m2)

let beta_eta_norm_fixed counter m =
  try
    Some(atrma_trm counter (beta_eta_norm_a counter (trm_atrma counter [] m)))
  with
  | CheckingBd -> Printf.printf "checking bound reached in beta_eta\n"; None
