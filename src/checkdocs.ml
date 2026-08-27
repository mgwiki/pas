open Hash;;
open Mathdata;;
open Inputdraft;;

let checkdocs2_main oc h hr =
  let locgvtph : (hashval * Logic.stp,unit) Hashtbl.t = Hashtbl.create 100 in
  let locgvknh : (hashval,unit) Hashtbl.t = Hashtbl.create 100 in
  let locgvtp _ h1 a =
    Hashtbl.mem locgvtph (h1,a)
  in
  let locgvkn =
    (fun _ k -> Hashtbl.mem locgvknh k)
  in
  let f = open_in_bin h in
  let thyspec : Logic.theoryspec = Marshal.from_channel f in
  close_in f;
  let ((pl,kl) as thy) = theoryspec_theory thyspec in
  List.iter (fun k -> Hashtbl.add locgvknh k ()) kl;
  let th = hashtheory thy in
  let cnt = ref 0 in
  let tm = Unix.gettimeofday() in
  let prevtm = ref tm in
  let prevcnt = ref !cnt in
  let checkdocs2 h f =
    begin
      try
        while true do
          let d : Logic.doc = Marshal.from_channel f in
          incr cnt;
          match Checking.check_doc (ref 0) locgvtp locgvkn th thy d with
          | None -> raise (Failure (Printf.sprintf "Doc %d failed\n" !cnt))
          | Some(gsl,kl) ->
             (** now, export types of hashes of (potentially) new defns and export hashes of (potentially) new knowns **)
             List.iter (fun ((h,a),_) -> Hashtbl.replace locgvtph (h,a) ()) gsl;
             List.iter (fun (k,_) -> Hashtbl.replace locgvknh k ()) kl
        done
      with End_of_file ->
        close_in f;
        let nowtm = Unix.gettimeofday() in
        Printf.fprintf oc "Done with %s\nDocs: %d (%d)\nTime: %f (%f)\n%!" h (!cnt - !prevcnt) !cnt (nowtm -. !prevtm)  (nowtm -. tm);
        prevcnt := !cnt;
        prevtm := nowtm;
    end
  in
  List.iter (fun h -> let f = open_in_bin h in checkdocs2 h f) hr;;

let checkpfgdocs_main oc mar h hr =
  let locgvtph : (hashval * Logic.stp,unit) Hashtbl.t = Hashtbl.create 100 in
  let locgvknh : (hashval,unit) Hashtbl.t = Hashtbl.create 100 in
  let locgvtp _ h1 a =
    Hashtbl.mem locgvtph (h1,a)
  in
  let locgvkn =
    (fun _ k -> Hashtbl.mem locgvknh k)
  in
  let f = open_in h in
  let moc = ref (if mar then Some(open_out_bin (Printf.sprintf "%s.bin" h)) else None) in
  let l = input_token f in
  if not (l = "Theory") then (close_in f; raise (Failure "Theory file does not begin with Theory"));
  let (thyspec,nonce,gamma,_,prophrev,propownsh,proprightsh) = input_theoryspec f in
  (match !moc with Some(moc2) -> Marshal.to_channel moc2 thyspec [ ]; close_out moc2 | None -> ());
  close_in f;
  let ((pl,kl) as thy) = theoryspec_theory thyspec in
  List.iter (fun k -> Hashtbl.add locgvknh k ()) kl;
  let th = hashtheory thy in
  let cnt = ref 0 in
  let tm = Unix.gettimeofday() in
  let prevtm = ref tm in
  let prevcnt = ref !cnt in
  let checkdocs2 h f =
    begin
      try
        while true do
	  let l = input_token f in
	  if not (l = "Document") then (close_in f; raise (Failure "Document does not begin with Document"));
	  let thyid = input_token f in
	  let th2 = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
          if not (th = th2) then (close_in f; raise (Failure "Document is in a different theory."));
	  let (d,nonce,gamma,_,objhrev,_,prophrev,conjh,objownsh,objrightsh,propownsh,proprightsh,bountyh) = input_doc_2 f th in
          (match !moc with Some(moc2) -> Marshal.to_channel moc2 d [ ] | None -> ());
          incr cnt;
          match Checking.check_doc (ref 0) locgvtp locgvkn th thy d with
          | None -> raise (Failure (Printf.sprintf "Doc %d failed\n" !cnt))
          | Some(gsl,kl) ->
             (** now, export types of hashes of (potentially) new defns and export hashes of (potentially) new knowns **)
             List.iter (fun ((h,a),_) -> Hashtbl.replace locgvtph (h,a) ()) gsl;
             List.iter (fun (k,_) -> Hashtbl.replace locgvknh k ()) kl
        done
      with End_of_file ->
        close_in f;
        (match !moc with Some(moc2) -> close_out moc2 | None -> ());
        let nowtm = Unix.gettimeofday() in
        Printf.fprintf oc "Done with %s\nDocs: %d (%d)\nTime: (%f) %f\n%!" h (!cnt - !prevcnt) !cnt (nowtm -. !prevtm) (nowtm -. tm);
        prevtm := nowtm;
        prevcnt := !cnt;
    end
  in
  List.iter
    (fun h ->
      let f = open_in_bin h in
      moc := (if mar then Some(open_out_bin (Printf.sprintf "%s.bin" h)) else None);
      checkdocs2 h f)
    hr;;

begin
  match Array.to_list Sys.argv with
  | (_::h::hr) ->
     if h = "-pfg" then
       begin
         match hr with
         | (h::hr) -> checkpfgdocs_main stdout false h hr
         | _ -> Printf.printf "Expected: checkdocs [-pfg|-marshal] <theoryfile> [<docsfile1> ... <docsfilen>]\nNo files given.\n"
       end
     else if h = "-marshal" then
       begin
         match hr with
         | (h::hr) -> checkpfgdocs_main stdout true h hr
         | _ -> Printf.printf "Expected: checkdocs [-pfg|-marshal] <theoryfile> [<docsfile1> ... <docsfilen>]\nNo files given.\n"
       end
     else
       checkdocs2_main stdout h hr
  | _ -> Printf.printf "Expected: checkdocs [-pfg|-marshal] <theoryfile> [<docsfile1> ... <docsfilen>]\nNo files given.\n"
end;;
