(************************************************************************)
(* Coq Language Server Protocol -- Per-sentence perf data (pull)        *)
(* Copyright 2025 genproof contributors -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)

(* [coq/getPerfData] custom request: return the per-sentence performance
   data ([Fleche.Perf.t], as in the [$/coq/filePerfData] notification) on
   demand.

   The push notification only fires when a document *completes* checking
   (reaches EOF); this pull variant serves the same payload for a
   partially-checked document, so a client can profile a prefix -- check
   up to a position -- without ever elaborating an expensive tail.  The
   stats come straight from the nodes' [info.stats] populated at
   elaboration time; nothing is re-executed.

   Like [proof/goals] this is a postponed position request: it is
   answered when checking reaches the requested point, so the request
   itself drives the check that far (and no further, in
   [check_only_on_request] mode).  The returned [timings] cover every
   node checked so far, which may extend past the point on a warm
   document; clients filter by range as needed. *)

let request ~token:_ ~(doc : Fleche.Doc.t) ~point:_ =
  let { Fleche.Doc.uri; version; _ } = doc in
  let textDocument =
    Fleche_lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version }
  in
  let { Fleche.Perf.summary; timings } = Fleche.Perf_analysis.make doc in
  Fleche_lsp.JFleche.DocumentPerfData.(
    to_yojson { textDocument; summary; timings })
  |> Result.ok
