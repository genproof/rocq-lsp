(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Hover Request                          *)
(*************************************************************************)

type format =
  | Pp
  | Str
  | Box

(** [goals ~pp_format ?pretac ?pretac_timeout] Serve goals at point; users can
    request pre-processing and formatting using the provided parameters.
    [pretac_timeout] (seconds) bounds the whole [pretac] run with a single
    wall-clock budget so a slow/diverging speculative tactic fails cleanly
    instead of wedging the server. *)
val goals :
     pp_format:format
  -> compact:bool
  -> mode:Fleche.Info.approx
  -> pretac:string option
  -> ?pretac_timeout:float
  -> unit
  -> (Yojson.Safe.t, string) Request.position

(** For printing of goals in [coq/getDocument] *)
val pp : pp_format:format -> Yojson.Safe.t Fleche.Info.Goals.printer
