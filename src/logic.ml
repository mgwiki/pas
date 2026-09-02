(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2016 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash

type stp =
| Base of int
| TpArr of stp * stp
| Prop

type trm =
| DB of int * int
| TmH of int * hashval
| Prim of int * int
| Ap of int * trm * trm
| Lam of int * stp * trm
| Imp of int * trm * trm
| All of int * stp * trm
| Ex of int * stp * trm
| Eq of int * stp * trm * trm

type pf =
| Known of int * hashval
| Hyp of int * int
| PrAp of int * pf * pf
| TmAp of int * pf * trm
| PrLa of int * trm * pf
| TmLa of int * stp * pf
| Ext of int * stp * stp

type gsign = ((hashval * stp) * trm option) list * (hashval * trm) list

type theoryitem =
| Thyprim of stp
| Thyaxiom of trm
| Thydef of stp * trm

type theoryspec = theoryitem list

type theory = stp list * hashval list

type signaitem =
| Signasigna of hashval
| Signaparam of hashval * stp
| Signadef of stp * trm
| Signaknown of trm

type signaspec = signaitem list

type signa = hashval list * gsign

type docitem =
| Docsigna of int * hashval
| Docparam of int * hashval * stp
| Docdef of int * stp * trm
| Docknown of int * trm
| Docpfof of int * trm * pf
| Docconj of int * trm

type doc = docitem list

