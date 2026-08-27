(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2016 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Logic
open Mathdata

val check_doc : int ref ->
  (hashval option -> hashval -> stp -> bool) -> (hashval option -> hashval ->
  bool) -> hashval option -> theory -> doc ->
  gsign option

val beta_eta_norm_fixed : int ref -> trm -> trm option
