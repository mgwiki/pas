(* Copyright (c) 2022 The Proofgold Lava developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash;;
open Mathdata;;

let whitespace_p c = c = ' ' || c = '\t' || c = '\r' || c = '\n';;

let skip_whitespace ch =
  try
    while true do
      let c = input_char ch in
      if c = '%' then
	begin
	  try
	    while true do
	      let c = input_char ch in
	      if c = '\r' || c = '\n' then raise Exit
	    done
	  with Exit -> ()
	end
      else if not (whitespace_p c) then raise Exit
    done
  with Exit ->
    seek_in ch (pos_in ch - 1);;

let input_token ch =
  skip_whitespace ch;
  let tokb = Buffer.create 10 in
  try
    while true do
      let c = input_char ch in
      if whitespace_p c || c = '%' then
	raise Exit
      else
	Buffer.add_char tokb c
    done;
    ""
  with Exit ->
    Buffer.contents tokb;;

let input_token_rev_list ch =
  let rec input_token_rev_list_r acc =
    let tok = input_token ch in
    if tok = "]" then
      acc
    else
      input_token_rev_list_r (tok::acc)
  in
  let stok = input_token ch in
  if stok = "[" then
    input_token_rev_list_r []
  else
    raise (Failure (Printf.sprintf "expected [ but found %s" stok))

let pos x l =
  let rec posr x l i =
    match l with
    | [] -> raise Not_found
    | y::r when x = y -> i
    | _::r -> posr x r (i+1)
  in
  posr x l 0;;

let rec input_stp bash ch tvl =
  let l = input_token ch in
  if l = "TpArr" then
    let a = input_stp bash ch tvl in
    let b = input_stp bash ch tvl in
    Logic.TpArr(a,b)
  else if l = "Prop" then
    Logic.Prop
  else
    try
      let i = Hashtbl.find bash l in
      Logic.Base(i)
    with Not_found ->
      raise (Failure (Printf.sprintf "Unknown type %s" l));;

let rec input_trm bash trmh ch tvl vl =
  let ps = Int64.to_int (In_channel.pos ch) in
  let l = input_token ch in
  if l = "Ap" then
    let m1 = input_trm bash trmh ch tvl vl in
    let m2 = input_trm bash trmh ch tvl vl in
    Logic.Ap(ps,m1,m2)
  else if l = "Lam" then
    let x = input_token ch in
    let a = input_stp bash ch tvl in
    let m2 = input_trm bash trmh ch tvl (x::vl) in
    Logic.Lam(ps,a,m2)
  else if l = "Imp" then
    let m1 = input_trm bash trmh ch tvl vl in
    let m2 = input_trm bash trmh ch tvl vl in
    Logic.Imp(ps,m1,m2)
  else if l = "All" then
    let x = input_token ch in
    let a = input_stp bash ch tvl in
    let m2 = input_trm bash trmh ch tvl (x::vl) in
    Logic.All(ps,a,m2)
  else if l = "Ex" then
    let x = input_token ch in
    let a = input_stp bash ch tvl in
    let m2 = input_trm bash trmh ch tvl (x::vl) in
    Logic.Ex(ps,a,m2)
  else if l = "Eq" then
    let a = input_stp bash ch tvl in
    let m2 = input_trm bash trmh ch tvl vl in
    let m3 = input_trm bash trmh ch tvl vl in
    Logic.Eq(ps,a,m2,m3)
  else if l = "Prim" then
    let x = input_token ch in
    let i = int_of_string x in
    if i >= 0 then
      Logic.Prim(ps,i)
    else
      raise (Failure "negative primitive?")
  else
    try
      let i = pos l vl in
      Logic.DB(ps,i)
    with Not_found ->
      try
        let (_,m) = Hashtbl.find trmh l in
        m
      with Not_found ->
	raise (Failure (Printf.sprintf "Unknown term %s" l));;

let rec input_pf bash trmh proph ch tvl vl hl =
  let ps = Int64.to_int (In_channel.pos ch) in
  let l = input_token ch in
  if l = "PrAp" then
    let d1 = input_pf bash trmh proph ch tvl vl hl in
    let d2 = input_pf bash trmh proph ch tvl vl hl in
    Logic.PrAp(ps,d1,d2)
  else if l = "TmAp" then
    let d1 = input_pf bash trmh proph ch tvl vl hl in
    let m2 = input_trm bash trmh ch tvl vl in
    Logic.TmAp(ps,d1,m2)
  else if l = "PrLa" then
    let x = input_token ch in
    let p1 = input_trm bash trmh ch tvl vl in
    let d2 = input_pf bash trmh proph ch tvl vl (x::hl) in
    Logic.PrLa(ps,p1,d2)
  else if l = "TmLa" then
    let x = input_token ch in
    let a1 = input_stp bash ch tvl in
    let d2 = input_pf bash trmh proph ch tvl (x::vl) hl in
    Logic.TmLa(ps,a1,d2)
  else if l = "Ext" then
    let a1 = input_stp bash ch tvl in
    let a2 = input_stp bash ch tvl in
    Logic.Ext(ps,a1,a2)
  else
    try
      let h = Hashtbl.find proph l in
      Logic.Known(ps,h)
    with Not_found ->
      try
	let i = pos l hl in
	Logic.Hyp(ps,i)
      with Not_found ->
	raise (Failure (Printf.sprintf "Unknown known or hyp ref %s" l))

let input_theoryspec ch =
  let basec = ref 0 in
  let baseh : (string,int) Hashtbl.t = Hashtbl.create 10 in
  let primc = ref 0 in
  let trmh : (string,Logic.stp * Logic.trm) Hashtbl.t = Hashtbl.create 100 in
  let proph : (string,hashval) Hashtbl.t = Hashtbl.create 100 in
  let prophrev : (hashval,string) Hashtbl.t = Hashtbl.create 100 in
  let propownsh : (hashval,payaddr) Hashtbl.t = Hashtbl.create 100 in
  let proprightsh : (bool * hashval,payaddr * (int64 option)) Hashtbl.t = Hashtbl.create 100 in
  let thyspec = ref [] in
  let nonce = ref None in
  let gamma = ref None in
  let pr l f =
    try
      f()
    with End_of_file ->
      raise (Failure (Printf.sprintf "Incomplete %s" l))
  in
  try
    while true do
      let l = input_token ch in
      if l = "Nonce" then
	pr l
	  (fun () ->
	    let h = input_token ch in
	    match !nonce with
	    | None -> nonce := Some(hexstring_hashval h)
	    | Some(_) -> raise (Failure "two nonces where at most one is expected"))
      else if l = "Publisher" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
            ())
      else if l = "NewOwner" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
            ())
      else if l = "NewRights" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
	    let _ = input_token ch in
            ())
      else if l = "NewPureRights" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
	    let _ = input_token ch in
            ())
      else if l = "NewTheoryRights" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
	    let _ = input_token ch in
            ())
      else if l = "Base" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    Hashtbl.add baseh nm !basec;
	    incr basec)
      else if l = "Prim" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for type of Prim");
	    let a = input_stp baseh ch [] in
	    Hashtbl.add trmh nm (a,Logic.Prim(0,!primc));
	    incr primc;
	    thyspec := Logic.Thyprim(a)::!thyspec)
      else if l = "Def" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for type of Def");
	    let a = input_stp baseh ch [] in
	    if not (input_token ch = ":=") then raise (Failure "bad format for term of Def");
	    let m = input_trm baseh trmh ch [] [] in
	    match Checking.beta_eta_norm_fixed (ref 0) m with
	    | Some(m) ->
		Hashtbl.add trmh nm (a,Logic.TmH(0,Mathdata.tm_hashroot m));
		thyspec := Logic.Thydef(a,m)::!thyspec
	    | None -> raise (Failure (Printf.sprintf "trouble normalizing Def %s" nm)))
      else if l = "Axiom" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for prop of Axiom");
	    let m = input_trm baseh trmh ch [] [] in
	    match Checking.beta_eta_norm_fixed (ref 0) m with
	    | Some(m) ->
		let h = Mathdata.tm_hashroot m in
		Hashtbl.add proph nm h;
		Hashtbl.add prophrev h nm;
		thyspec := Logic.Thyaxiom(m)::!thyspec
	    | None -> raise (Failure (Printf.sprintf "trouble normalizing Axiom %s" nm)))
      else
	raise (Failure (Printf.sprintf "Unknown theory spec item %s" l))
    done;
    (!thyspec,!nonce,!gamma,proph,prophrev,propownsh,proprightsh)
  with
  | End_of_file -> close_in_noerr ch; (!thyspec,!nonce,!gamma,proph,prophrev,propownsh,proprightsh)
  | e -> close_in_noerr ch; raise e;;

let input_doc_2 ch th =
  let basec = ref 0 in
  let baseh : (string,int) Hashtbl.t = Hashtbl.create 10 in
  let paramh : (string,Logic.stp * hashval) Hashtbl.t = Hashtbl.create 100 in
  let objhrev : (hashval,string) Hashtbl.t = Hashtbl.create 100 in
  let defh : (string,hashval) Hashtbl.t = Hashtbl.create 100 in
  let trmh : (string,Logic.stp * Logic.trm) Hashtbl.t = Hashtbl.create 100 in
  let proph : (string,hashval) Hashtbl.t = Hashtbl.create 100 in
  let prophrev : (hashval,string) Hashtbl.t = Hashtbl.create 100 in
  let conjh : (string,hashval) Hashtbl.t = Hashtbl.create 100 in
  let thmh : (string,hashval) Hashtbl.t = Hashtbl.create 100 in
  let objownsh : (hashval,payaddr) Hashtbl.t = Hashtbl.create 100 in
  let objrightsh : (bool * hashval,payaddr * (int64 option)) Hashtbl.t = Hashtbl.create 100 in
  let propownsh : (hashval,payaddr) Hashtbl.t = Hashtbl.create 100 in
  let proprightsh : (bool * hashval,payaddr * (int64 option)) Hashtbl.t = Hashtbl.create 100 in
  let bountyh : (hashval,int64 * (payaddr * int64) option) Hashtbl.t = Hashtbl.create 100 in
  let doc = ref [] in
  let nonce = ref None in
  let gamma = ref None in
  let pr l f =
    try
      f()
    with
    | End_of_file ->
      raise (Failure (Printf.sprintf "Incomplete %s" l))
  in
  try
    while true do
      let ps = Int64.to_int (In_channel.pos ch) in
      let l = input_token ch in
      if l = "DocumentEnd" then
        raise Exit
      else if l = "Nonce" then
	pr l
	  (fun () ->
	    let h = input_token ch in
	    match !nonce with
	    | None -> nonce := Some(hexstring_hashval h)
	    | Some(_) -> raise (Failure "two nonces where at most one is expected"))
      else if l = "Publisher" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
            ())
      else if l = "Include" then
	pr l
	  (fun () ->
	    let _ = hexstring_hashval (input_token ch) in
            raise (Failure "refusing to check documents that import signatures"))
      else if l = "NewOwner" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
            ())
      else if l = "NewRights" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
            ())
      else if l = "NewPureRights" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
	    let _ = input_token ch in
            ())
      else if l = "NewTheoryRights" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
	    let _ = input_token ch in
            ())
      else if l = "Bounty" then
	pr l
	  (fun () ->
	    let _ = input_token ch in
	    let _ = input_token ch in
	    let lkh = input_token ch in (** potential lock height for reclaiming bounty without proof **)
	    if lkh = "NoTimeout" then
              ()
	    else
	      let _ = input_token ch in
              ())
      else if l = "Base" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    Hashtbl.add baseh nm !basec;
	    incr basec)
      else if l = "Let" then (** not part of the document, but just to ease writing terms **)
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for type of Let");
	    let a = input_stp baseh ch [] in
	    if not (input_token ch = ":=") then raise (Failure "bad format for term of Let");
	    let m = input_trm baseh trmh ch [] [] in
	    Hashtbl.add trmh nm (a,m))
      else if l = "Param" then
	pr l
	  (fun () ->
	    let h = input_token ch in
	    let h = hexstring_hashval h in
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for type of Prim");
	    let a = input_stp baseh ch [] in
	    Hashtbl.add trmh nm (a,Logic.TmH(0,h));
	    Hashtbl.add paramh nm (a,h);
	    Hashtbl.add objhrev h nm;
	    doc := Logic.Docparam(ps,h,a)::!doc)
      else if l = "Def" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for type of Def");
	    let a = input_stp baseh ch [] in
	    if not (input_token ch = ":=") then raise (Failure "bad format for term of Def");
	    let m = input_trm baseh trmh ch [] [] in
	    match Checking.beta_eta_norm_fixed (ref 0) m with
	    | Some(m) ->
		let h = Mathdata.tm_hashroot m in
		Hashtbl.add trmh nm (a,Logic.TmH(0,h));
		Hashtbl.add defh nm h; (* definition; if this is "new" then an owner and rights will be given *)
		Hashtbl.add objhrev h nm;
		doc := Logic.Docdef(ps,a,m)::!doc
	    | None -> raise (Failure (Printf.sprintf "trouble normalizing Def %s" nm)))
      else if l = "Known" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for prop of Known");
	    let m = input_trm baseh trmh ch [] [] in
	    match Checking.beta_eta_norm_fixed (ref 0) m with
	    | Some(m) ->
		let h = Mathdata.tm_hashroot m in
		Hashtbl.add proph nm h;
		Hashtbl.add prophrev h nm;
		doc := Logic.Docknown(ps,m)::!doc
	    | None -> raise (Failure (Printf.sprintf "trouble normalizing Axiom %s" nm)))
      else if l = "Conj" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for prop of Conj");
	    let m = input_trm baseh trmh ch [] [] in
	    match Checking.beta_eta_norm_fixed (ref 0) m with
	    | Some(m) ->
 	        let h = Mathdata.tm_hashroot m in
		Hashtbl.add conjh nm h; (* conjecture: a bounty can be declared *)
		Hashtbl.add prophrev h nm;
		doc := Logic.Docconj(ps,m)::!doc
	    | None -> raise (Failure (Printf.sprintf "trouble normalizing Axiom %s" nm)))
      else if l = "Thm" then
	pr l
	  (fun () ->
	    let nm = input_token ch in
	    if not (input_token ch = ":") then raise (Failure "bad format for prop of Thm");
	    let m = input_trm baseh trmh ch [] [] in
	    if not (input_token ch = ":=") then raise (Failure "bad format for proof of Thm");
	    let d = input_pf baseh trmh proph ch [] [] [] in
	    match Checking.beta_eta_norm_fixed (ref 0) m with
	    | Some(m) ->
		let h = Mathdata.tm_hashroot m in
		Hashtbl.add proph nm h;
		Hashtbl.add prophrev h nm;
		Hashtbl.add thmh nm h; (* theorem: if this is a newly proven proposition, then an owner and rights will be declared *)
		doc := Logic.Docpfof(ps,m,d)::!doc
	    | None -> raise (Failure (Printf.sprintf "trouble normalizing Axiom %s" nm)))
      else
	raise (Failure (Printf.sprintf "Unknown document item %s" l))
    done;
    (!doc,!nonce,!gamma,paramh,objhrev,proph,prophrev,conjh,objownsh,objrightsh,propownsh,proprightsh,bountyh)
  with
  | End_of_file -> (!doc,!nonce,!gamma,paramh,objhrev,proph,prophrev,conjh,objownsh,objrightsh,propownsh,proprightsh,bountyh)
  | Exit -> (!doc,!nonce,!gamma,paramh,objhrev,proph,prophrev,conjh,objownsh,objrightsh,propownsh,proprightsh,bountyh)
  | e -> close_in_noerr ch; raise e;;

