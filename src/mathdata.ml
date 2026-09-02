(* Copyright (c) 2021 The Proofgold Lava developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2016 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Sha256
open Hash
open Logic

let debug = ref false
let printlist l = List.iter (fun ((x, y), z) -> Printf.printf "%s " (hashval_hexstring x)) l

(** ** tp serialization ***)
let rec seo_tp o m c =
  match m with
  | TpArr(m0,m1) -> (*** 0 0 ***)
    let c = o 2 0 c in
    let c = seo_tp o m0 c in
    let c = seo_tp o m1 c in
    c
  | Prop -> (*** 0 1 ***)
    o 2 2 c
  | Base(x) when x < 65536 -> (*** 1 ***)
    let c = o 1 1 c in
    seo_varintb o x c
  | Base(_) -> raise (Failure("Invalid base type"))

let tp_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_tp seosb m (c,None));
  Buffer.contents c

let hashtp m = hashtag (sha256str_hashval (tp_to_str m)) 64l

let rec sei_tp i c =
  let (b,c) = i 1 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (m0,c) = sei_tp i c in
      let (m1,c) = sei_tp i c in
      (TpArr(m0,m1),c)
    else
      (Prop,c)
  else
    let (x,c) = sei_varintb i c in
    (Base(x),c)

(** ** tp list serialization ***)
let seo_tpl o al c = seo_list seo_tp o al c
let sei_tpl i c = sei_list sei_tp i c

let tpl_to_str al =
  let c = Buffer.create 1000 in
  seosbf (seo_tpl seosb al (c,None));
  Buffer.contents c

let hashtpl al =
  if al = [] then
    None
  else
    Some(hashtag (sha256str_hashval (tpl_to_str al)) 65l)

(** ** tm serialization ***)
let rec seo_tm o m c =
  match m with
  | TmH(_,h) -> (*** 000 ***)
    let c = o 3 0 c in
    let c = seo_hashval o h c in
    c
  | DB(_,x) when x >= 0 && x <= 65535 -> (*** 001 ***)
    let c = o 3 1 c in
    seo_varintb o x c
  | DB(_,x) ->
    raise (Failure "seo_tm - de Bruijn out of bounds");
  | Prim(_,x) when x >= 0 && x <= 65535 -> (*** 010 ***)
    let c = o 3 2 c in
    let c = seo_varintb o x c in
    c
  | Prim(_,x) ->
    raise (Failure "seo_tm - Prim out of bounds");
  | Ap(_,m0,m1) -> (*** 011 ***)
    let c = o 3 3 c in
    let c = seo_tm o m0 c in
    let c = seo_tm o m1 c in
    c
  | Lam(_,m0,m1) -> (*** 100 ***)
    let c = o 3 4 c in
    let c = seo_tp o m0 c in
    let c = seo_tm o m1 c in
    c
  | Imp(_,m0,m1) -> (*** 101 ***)
    let c = o 3 5 c in
    let c = seo_tm o m0 c in
    let c = seo_tm o m1 c in
    c
  | All(_,m0,m1) -> (*** 110 ***)
    let c = o 3 6 c in
    let c = seo_tp o m0 c in
    let c = seo_tm o m1 c in
    c
  | Ex(_,a,m1) -> (*** 111 0 ***)
    let c = o 4 7 c in
    let c = seo_tp o a c in
    let c = seo_tm o m1 c in
    c
  | Eq(_,a,m1,m2) -> (*** 111 1 ***)
    let c = o 4 15 c in
    let c = seo_tp o a c in
    let c = seo_tm o m1 c in
    let c = seo_tm o m2 c in
    c

let tm_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_tm seosb m (c,None));
  Buffer.contents c

let hashtm m = hashtag (sha256str_hashval (tm_to_str m)) 66l

let rec sei_tm i c =
  let (x,c) = i 3 c in
  if x = 0 then
    let (h,c) = sei_hashval i c in
    (TmH(0,h),c)
  else if x = 1 then
    let (z,c) = sei_varintb i c in
    (DB(0,z),c)
  else if x = 2 then
    let (z,c) = sei_varintb i c in
    (Prim(0,z),c)
  else if x = 3 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_tm i c in
    (Ap(0,m0,m1),c)
  else if x = 4 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_tm i c in
    (Lam(0,m0,m1),c)
  else if x = 5 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_tm i c in
    (Imp(0,m0,m1),c)
  else if x = 6 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_tm i c in
    (All(0,m0,m1),c)
  else
    let (y,c) = i 1 c in
    if y = 0 then
      let (a,c) = sei_tp i c in
      let (m0,c) = sei_tm i c in
      (Ex(0,a,m0),c)
    else
      let (a,c) = sei_tp i c in
      let (m0,c) = sei_tm i c in
      let (m1,c) = sei_tm i c in
      (Eq(0,a,m0,m1),c)

(** ** pf serialization ***)
let rec seo_pf o m c =
  match m with
  | Hyp(_,x) when x >= 0 && x <= 65535 -> (*** 001 ***)
    let c = o 3 1 c in
    seo_varintb o x c
  | Hyp(_,x) ->
    raise (Failure "seo_pf - Hypothesis out of bounds");
  | Known(_,h) -> (*** 010 ***)
    let c = o 3 2 c in
    let c = seo_hashval o h c in
    c
  | TmAp(_,m0,m1) -> (*** 011 ***)
    let c = o 3 3 c in
    let c = seo_pf o m0 c in
    let c = seo_tm o m1 c in
    c
  | PrAp(_,m0,m1) -> (*** 100 ***)
    let c = o 3 4 c in
    let c = seo_pf o m0 c in
    let c = seo_pf o m1 c in
    c
  | PrLa(_,m0,m1) -> (*** 101 ***)
    let c = o 3 5 c in
    let c = seo_tm o m0 c in
    let c = seo_pf o m1 c in
    c
  | TmLa(_,m0,m1) -> (*** 110 ***)
    let c = o 3 6 c in
    let c = seo_tp o m0 c in
    let c = seo_pf o m1 c in
    c
  | Ext(_,a,b) -> (*** 111 ***)
    let c = o 3 7 c in
    let c = seo_tp o a c in
    let c = seo_tp o b c in
    c

let pf_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_pf seosb m (c,None));
  Buffer.contents c

let hashpf m = hashtag (sha256str_hashval (pf_to_str m)) 67l

let rec sei_pf i c =
  let (x,c) = i 3 c in
  if x = 0 then
    failwith "GPA"
  else if x = 1 then
    let (z,c) = sei_varintb i c in
    (Hyp(0,z),c)
  else if x = 2 then
    let (z,c) = sei_hashval i c in
    (Known(0,z),c)
  else if x = 3 then
    let (m0,c) = sei_pf i c in
    let (m1,c) = sei_tm i c in
    (TmAp(0,m0,m1),c)
  else if x = 4 then
    let (m0,c) = sei_pf i c in
    let (m1,c) = sei_pf i c in
    (PrAp(0,m0,m1),c)
  else if x = 5 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_pf i c in
    (PrLa(0,m0,m1),c)
  else if x = 6 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_pf i c in
    (TmLa(0,m0,m1),c)
  else
    let (a,c) = sei_tp i c in
    let (b,c) = sei_tp i c in
    (Ext(0,a,b),c)

(** ** theoryspec serialization ***)
let seo_theoryitem o m c =
  match m with
  | Thyprim(a) -> (* 0 0 *)
    let c = o 2 0 c in
    seo_tp o a c
  | Thydef(a,m) -> (* 0 1 *)
    let c = o 2 2 c in
    let c = seo_tp o a c in
    seo_tm o m c
  | Thyaxiom(m) -> (* 1 *)
    let c = o 1 1 c in
    seo_tm o m c

let sei_theoryitem i c =
  let (b,c) = i 1 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (a,c) = sei_tp i c in
      (Thyprim(a),c)
    else
      let (a,c) = sei_tp i c in
      let (m,c) = sei_tm i c in
      (Thydef(a,m),c)
  else
    let (m,c) = sei_tm i c in
    (Thyaxiom(m),c)

let seo_theoryspec o dl c = seo_list seo_theoryitem o dl c
let sei_theoryspec i c = sei_list sei_theoryitem i c

let theoryspec_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_theoryspec seosb m (c,None));
  Buffer.contents c

(** ** signaspec serialization ***)
let seo_signaitem o m c =
  match m with
  | Signasigna(h) -> (** 00 **)
    let c = o 2 0 c in
    seo_hashval o h c
  | Signaparam(h,a) -> (** 01 **)
    let c = o 2 1 c in
    let c = seo_hashval o h c in
    seo_tp o a c
  | Signadef(a,m) -> (** 10 **)
    let c = o 2 2 c in
    let c = seo_tp o a c in
    seo_tm o m c
  | Signaknown(m) -> (** 11 **)
    let c = o 2 3 c in
    seo_tm o m c

let sei_signaitem i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (h,c) = sei_hashval i c in
    (Signasigna(h),c)
  else if b = 1 then
    let (h,c) = sei_hashval i c in
    let (a,c) = sei_tp i c in
    (Signaparam(h,a),c)
  else if b = 2 then
    let (a,c) = sei_tp i c in
    let (m,c) = sei_tm i c in
    (Signadef(a,m),c)
  else
    let (m,c) = sei_tm i c in
    (Signaknown(m),c)

let seo_signaspec o dl c = seo_list seo_signaitem o dl c
let sei_signaspec i c = sei_list sei_signaitem i c

let signaspec_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_signaspec seosb m (c,None));
  Buffer.contents c

(** ** doc serialization ***)
let seo_docitem o m c =
  match m with
  | Docsigna(_,h) -> (** 00 0 **)
    let c = o 3 0 c in
    seo_hashval o h c
  | Docparam(_,h,a) -> (** 00 1 **)
    let c = o 3 4 c in
    let c = seo_hashval o h c in
    seo_tp o a c
  | Docdef(_,a,m) -> (** 01 **)
    let c = o 2 1 c in
    let c = seo_tp o a c in
    seo_tm o m c
  | Docknown(_,m) -> (** 10 0 **)
    let c = o 3 2 c in
    seo_tm o m c
  | Docconj(_,m) -> (** 10 1 **)
    let c = o 3 6 c in
    seo_tm o m c
  | Docpfof(_,m,d) -> (** 11 **)
    let c = o 2 3 c in
    let c = seo_tm o m c in
    seo_pf o d c

let sei_docitem i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (h,c) = sei_hashval i c in
      (Docsigna(0,h),c)
    else
      let (h,c) = sei_hashval i c in
      let (a,c) = sei_tp i c in
      (Docparam(0,h,a),c)
  else if b = 1 then
    let (a,c) = sei_tp i c in
    let (m,c) = sei_tm i c in
    (Docdef(0,a,m),c)
  else if b = 2 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (m,c) = sei_tm i c in
      (Docknown(0,m),c)
    else
      let (m,c) = sei_tm i c in
      (Docconj(0,m),c)
  else
    let (m,c) = sei_tm i c in
    let (d,c) = sei_pf i c in
    (Docpfof(0,m,d),c)

let seo_doc o dl c = seo_list seo_docitem o dl c
let sei_doc i c = sei_list sei_docitem i c

let doc_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_doc seosb m (c,None));
  Buffer.contents c

let hashdoc m = hashtag (sha256str_hashval (doc_to_str m)) 70l

(** ** serialization of theories ***)
let seo_theory o (al,kl) c =
  let c = seo_tpl o al c in
  seo_list seo_hashval o kl c

let sei_theory i c =
  let (al,c) = sei_tpl i c in
  let (kl,c) = sei_list sei_hashval i c in
  ((al,kl),c)

let theory_to_str thy =
  let c = Buffer.create 1000 in
  seosbf (seo_theory seosb thy (c,None));
  Buffer.contents c

(*module DbTheory = Dbmbasic (struct type t = theory let basedir = "theory" let seival = sei_theory seis let seoval = seo_theory seosb end)

module DbTheoryTree =
  Dbmbasic
    (struct
      type t = hashval option * hashval list
      let basedir = "theorytree"
      let seival = sei_prod (sei_option sei_hashval) (sei_list sei_hashval) seis
      let seoval = seo_prod (seo_option seo_hashval) (seo_list seo_hashval) seosb
    end)
*)

(** * computation of hash roots ***)
let rec tm_hashroot m =
  match m with
  | TmH(_,h) -> h
  | Prim(_,x) -> hashtag (hashint32 (Int32.of_int x)) 96l
  | DB(_,x) -> hashtag (hashint32 (Int32.of_int x)) 97l
  | Ap(_,m,n) -> hashtag (hashpair (tm_hashroot m) (tm_hashroot n)) 98l
  | Lam(_,a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 99l
  | Imp(_,m,n) -> hashtag (hashpair (tm_hashroot m) (tm_hashroot n)) 100l
  | All(_,a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 101l
  | Ex(_,a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 102l
  | Eq(_,a,m,n) -> hashtag (hashpair (hashpair (hashtp a) (tm_hashroot m)) (tm_hashroot n)) 103l

let rec pf_hashroot d =
  match d with
  | Known(_,h) -> hashtag h 128l
  | Hyp(_,x) -> hashtag (hashint32 (Int32.of_int x)) 129l
  | TmAp(_,d,m) -> hashtag (hashpair (pf_hashroot d) (tm_hashroot m)) 130l
  | PrAp(_,d,e) -> hashtag (hashpair (pf_hashroot d) (pf_hashroot e)) 131l
  | PrLa(_,m,d) -> hashtag (hashpair (tm_hashroot m) (pf_hashroot d)) 132l
  | TmLa(_,a,d) -> hashtag (hashpair (hashtp a) (pf_hashroot d)) 133l
  | Ext(_,a,b) -> hashtag (hashpair (hashtp a) (hashtp b)) 134l

let rec docitem_hashroot d =
  match d with
  | Docsigna(_,h) -> hashtag h 172l
  | Docparam(_,h,a) -> hashtag (hashpair h (hashtp a)) 173l
  | Docdef(_,a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 174l
  | Docknown(_,m) -> hashtag (tm_hashroot m) 175l
  | Docconj(_,m) -> hashtag (tm_hashroot m) 176l
  | Docpfof(_,m,d) -> hashtag (hashpair (tm_hashroot m) (pf_hashroot d)) 177l

let rec doc_hashroot dl =
  match dl with
  | [] -> hashint32 180l
  | d::dr -> hashtag (hashpair (docitem_hashroot d) (doc_hashroot dr)) 181l

let hashtheory (al,kl) =
  hashopair
    (ohashlist (List.map hashtp al))
    (ohashlist kl)

let hashgsigna (tl,kl) =
  hashpair
    (hashlist
       (List.map (fun z ->
	          match z with
	          | ((h,a),None) -> hashtag (hashpair h (hashtp a)) 160l
	          | ((h,a),Some(m)) -> hashtag (hashpair h (hashpair (hashtp a) (hashtm m))) 161l)
	         tl))
    (hashlist (List.map (fun (k,p) -> (hashpair k (hashtm p))) kl))

let hashsigna (sl,(tl,kl)) = hashpair (hashlist sl) (hashgsigna (tl,kl))

let seo_gsigna o s c =
  seo_prod
    (seo_list (seo_prod_prod seo_hashval seo_tp (seo_option seo_tm)))
    (seo_list (seo_prod seo_hashval seo_tm))
    o s c

let sei_gsigna i c =
  sei_prod
    (sei_list (sei_prod_prod sei_hashval sei_tp (sei_option sei_tm)))
    (sei_list (sei_prod sei_hashval sei_tm))
    i c

let seo_signa o s c =
  seo_prod (seo_list seo_hashval) seo_gsigna o s c

let sei_signa i c =
  sei_prod (sei_list sei_hashval) sei_gsigna i c

let signa_to_str s =
  let c = Buffer.create 1000 in
  seosbf (seo_signa seosb s (c,None));
  Buffer.contents c

(*
module DbSigna = Dbmbasic (struct type t = hashval option * signa let basedir = "signa" let seival = sei_prod (sei_option sei_hashval) sei_signa seis let seoval = seo_prod (seo_option seo_hashval) seo_signa seosb end)

module DbSignaTree =
  Dbmbasic
    (struct
      type t = hashval option * hashval list
      let basedir = "signatree"
      let seival = sei_prod (sei_option sei_hashval) (sei_list sei_hashval) seis
      let seoval = seo_prod (seo_option seo_hashval) (seo_list seo_hashval) seosb
    end)
*)

let rec print_tp t base_types =
  match t with
  | Base i -> Printf.printf "base %d %d " i base_types
  | TpArr (t1, t2) -> (Printf.printf "tparr "; print_tp t1 base_types; print_tp t2 base_types)
  | Prop -> Printf.printf "prop "

let rec print_trm ctx sgn t thy =
  match t with
  | DB(pos,i) -> Printf.printf "(DB [%d] %d %d )" pos (List.length ctx) i
  | TmH(pos,h) ->
    printlist (fst sgn);
      Printf.printf "\n";
      Printf.printf "(TmH [%d] %s)" pos (hashval_hexstring h)
  | Prim(pos,i) -> Printf.printf "(Prim [%d] %d %d )" pos (List.length thy) i
  | Ap (pos, t1, t2) -> (Printf.printf "ap [%d] " pos; print_trm ctx sgn t1 thy; print_trm ctx sgn t2 thy)
  | Lam (pos, a1, t1) -> (Printf.printf "lam [%d] " pos; print_tp a1 (List.length thy); print_trm ctx sgn t1 thy)
  | Imp (pos, t1, t2) -> (Printf.printf "imp [%d] " pos; print_trm ctx sgn t1 thy; print_trm ctx sgn t2 thy)
  | All (pos, b, t1) -> (Printf.printf "all [%d] " pos; print_tp b (List.length thy); print_trm ctx sgn t1 thy)
  | Ex (pos, b, t1) -> (Printf.printf "ex [%d] " pos; print_tp b (List.length thy); print_trm ctx sgn t1 thy)
  | Eq (pos, b, t1, t2) -> (Printf.printf "eq [%d] " pos; print_tp b (List.length thy); print_trm ctx sgn t1 thy; print_trm ctx sgn t2 thy)

let rec print_pf ctx phi sg p thy =
  match p with
  | Known (pos, h) -> Printf.printf "known [%d] %s " pos (hashval_hexstring h)
  | Hyp (pos, i) -> Printf.printf "hypoth [%d] %d\n" pos i
  | PrAp (pos, p1, p2) ->
    Printf.printf "proof ap [%d] (" pos;
    print_pf ctx phi sg p1 thy;
    print_pf ctx phi sg p2 thy;
    Printf.printf ")"
  | TmAp (pos, p1, t1) ->
    Printf.printf "trm ap [%d] (" pos;
    print_pf ctx phi sg p1 thy;
    print_trm ctx sg t1 thy;
    Printf.printf ")"
  | PrLa (pos, s, p1) ->
    Printf.printf "proof lam [%d] (" pos;
    print_pf ctx (s :: phi) sg p1 thy;
    print_trm ctx sg s thy;
    Printf.printf ")"
  | TmLa (pos, a1, p1) ->
    Printf.printf "trm lam [%d] (" pos;
    print_pf (a1::ctx) phi sg p1 thy; (* (List.map (fun x -> uptrm x 0 1) phi) *)
    print_tp a1 (List.length thy);
    Printf.printf ")"
  | Ext (pos, a, b) ->
    Printf.printf "ext [%d] (" pos;
    print_tp a (List.length thy);
    print_tp b (List.length thy);
    Printf.printf ")"

exception CheckingFailure

(** * conversion of theoryspec to theory and signaspec to signa **)
let rec theoryspec_primtps_r dl =
  match dl with
  | [] -> []
  | Thyprim(a)::dr -> a::theoryspec_primtps_r dr
  | _::dr -> theoryspec_primtps_r dr
  
let theoryspec_primtps dl = List.rev (theoryspec_primtps_r dl)

let rec theoryspec_hashedaxioms dl =
  match dl with
  | [] -> []
  | Thyaxiom(m)::dr -> tm_hashroot m::theoryspec_hashedaxioms dr
  | _::dr -> theoryspec_hashedaxioms dr

let theoryspec_theory thy = (theoryspec_primtps thy,theoryspec_hashedaxioms thy)

let hashtheory (al,kl) =
  hashopair
    (ohashlist (List.map hashtp al))
    (ohashlist kl)

let rec signaspec_signas s =
  match s with
  | [] -> []
  | Signasigna(h)::r -> h::signaspec_signas r
  | _::r -> signaspec_signas r

let rec signaspec_trms s =
  match s with
  | [] -> []
  | Signaparam(h,a)::r -> ((h, a), None)::signaspec_trms r
  | Signadef(a,m)::r -> ((tm_hashroot m, a), Some(m))::signaspec_trms r
  | _::r -> signaspec_trms r

let rec signaspec_knowns s =
  match s with
  | [] -> []
  | Signaknown(p)::r -> (tm_hashroot p,p)::signaspec_knowns r
  | _::r -> signaspec_knowns r

let signaspec_signa s = (signaspec_signas s, (signaspec_trms s, signaspec_knowns s))

let theory_burncost thy =
  Int64.mul 2100000000L (Int64.of_int (String.length (theory_to_str thy)))
  
let theoryspec_burncost s = theory_burncost (theoryspec_theory s)

let signa_burncost s =
  Int64.mul 2100000000L (Int64.of_int (String.length (signa_to_str s)))

let signaspec_burncost s = signa_burncost (signaspec_signa s)

(** * extract which objs/props are used/created by signatures and documents, as well as full_needed needed to globally verify terms have a certain type/knowns are known **)

let adj x l = if List.mem x l then l else x::l

let rec signaspec_uses_objs_aux (dl:signaspec) r : (hashval * hashval) list =
  match dl with
  | Signaparam(h,a)::dr -> signaspec_uses_objs_aux dr (adj (h,hashtp a) r)
  | _::dr -> signaspec_uses_objs_aux dr r
  | [] -> r

let signaspec_uses_objs (dl:signaspec) : (hashval * hashval) list = signaspec_uses_objs_aux dl []

let rec signaspec_uses_props_aux (dl:signaspec) r : hashval list =
  match dl with
  | Signaknown(p)::dr -> signaspec_uses_props_aux dr (adj (tm_hashroot p) r)
  | _::dr -> signaspec_uses_props_aux dr r
  | [] -> r

let signaspec_uses_props (dl:signaspec) : hashval list = signaspec_uses_props_aux dl []

let rec doc_uses_objs_aux (dl:doc) r : (hashval * hashval) list =
  match dl with
  | Docparam(_,h,a)::dr -> doc_uses_objs_aux dr (adj (h,hashtp a) r)
  | _::dr -> doc_uses_objs_aux dr r
  | [] -> r

let doc_uses_objs (dl:doc) : (hashval * hashval) list = doc_uses_objs_aux dl []

let rec doc_uses_props_aux (dl:doc) r : hashval list =
  match dl with
  | Docknown(_,p)::dr -> doc_uses_props_aux dr (adj (tm_hashroot p) r)
  | _::dr -> doc_uses_props_aux dr r
  | [] -> r

let doc_uses_props (dl:doc) : hashval list = doc_uses_props_aux dl []

let rec doc_creates_objs_aux (dl:doc) r : (hashval * hashval) list =
  match dl with
  | Docdef(_,a,m)::dr -> doc_creates_objs_aux dr (adj (tm_hashroot m,hashtp a) r)
  | _::dr -> doc_creates_objs_aux dr r
  | [] -> r

let doc_creates_objs (dl:doc) : (hashval * hashval) list = doc_creates_objs_aux dl []

let rec doc_creates_props_aux (dl:doc) r : hashval list =
  match dl with
  | Docpfof(_,p,d)::dr -> doc_creates_props_aux dr (adj (tm_hashroot p) r)
  | _::dr -> doc_creates_props_aux dr r
  | [] -> r

let doc_creates_props (dl:doc) : hashval list = doc_creates_props_aux dl []

let falsehashprop = tm_hashroot (All(0,Prop,DB(0,0)))
let neghashprop = tm_hashroot (Lam(0,Prop,Imp(0,DB(0,0),TmH(0,falsehashprop))))

let invert_neg_prop p =
  match p with
  | Imp(_,np,f) when tm_hashroot f = falsehashprop -> np
  | Ap(_,n,np) when tm_hashroot n = neghashprop -> np
  | _ -> raise Not_found

let rec doc_creates_neg_props_aux (dl:doc) r : hashval list =
  match dl with
  | Docpfof(_,p,d)::dr ->
      begin
	try
	  let np = invert_neg_prop p in
	  doc_creates_neg_props_aux dr (adj (tm_hashroot np) r)
	with Not_found -> doc_creates_neg_props_aux dr r
      end
  | _::dr -> doc_creates_neg_props_aux dr r
  | [] -> r

let doc_creates_neg_props (dl:doc) : hashval list = doc_creates_neg_props_aux dl []

