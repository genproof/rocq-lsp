(************************************************************************)
(* Coq Language Server Protocol -- Extract goal to lemma                 *)
(* coq-lsp contributors                                                 *)
(************************************************************************)

(** [extract ~name ()] serves [coq/extract]: closes the open goal at the
    requested position into a standalone [Definition <name>_Goal] (always
    regenerated) plus a proof-skeleton [<name>_proof] (created only if absent),
    and returns the generated paths and the [eapply <name>_proof] to use. *)
val extract :
  name:string -> unit -> (Yojson.Safe.t, string) Request.position
