(************************************************************************)
(* Coq Language Server Protocol -- Per-sentence perf data (pull)        *)
(* Copyright 2025 genproof contributors -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)

(** [request] serves [coq/getPerfData]: the per-sentence performance data
    ([$/coq/filePerfData]'s payload) for the checked part of the document,
    on demand.  Postponed until checking reaches the requested position,
    so it can profile a prefix without elaborating the tail. *)
val request : (Yojson.Safe.t, string) Request.position
