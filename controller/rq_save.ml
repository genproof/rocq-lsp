(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Document Symbols Request               *)
(*************************************************************************)

(** Several todos here in terms of usability *)

let request ~token ~doc =
  let open Coq.Protect.E.O in
  let lines = Fleche.Doc.lines doc in
  let f () =
    (* XXX: What do do with feedback, return to user? *)
    let+ () = Fleche.Doc.save ~token ~doc in
    Ok `Null
  in
  Request.R.of_execution ~lines ~name:"save" ~f ()

(* Like [request] but writes the Flèche [.vof] document snapshot (every span and
   state) instead of a Coq [.vo].  Used by the [coq/saveVof] request to persist
   a warm document so a fresh server can reload it via [coq/loadVof] instead of
   re-checking. *)
let request_vof ~token ~doc =
  let open Coq.Protect.E.O in
  let lines = Fleche.Doc.lines doc in
  let f () =
    let+ () = Fleche.Doc.save_vof ~token ~doc in
    Ok `Null
  in
  Request.R.of_execution ~lines ~name:"save_vof" ~f ()
