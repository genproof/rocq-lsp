(************************************************************************)
(* Coq Petanque                                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(************************************************************************)

module Lsp = Fleche_lsp
module Dbg = Petanque_json.Dbg
open Petanque_json.Interp
open Protocol_shell

(* Free the global Flèche memoization tables.

   pet inherits the same unbounded ``Fleche.Memo.{Intern, Interp, Admit,
   Init, Require}`` hashtables that coq-lsp does — every executed
   sentence's post-state is cached and never reclaimed.  Without a way
   to release that state, a long-running pet process can accumulate
   tens of GB of resident memory.

   Mirrors ``controller/nt_cache_trim.ml``'s ``cache_trim`` so the same
   five tables that ``coq/trimCaches`` clears on the LSP side are
   reachable from the pet side.

   The int↔State.t mapping in ``petanque/json/obj_map.ml`` is a
   separate hashtable and is NOT cleared here — so client-held
   state_ids remain valid across a trim. *)
let trim_caches () =
  if not (Dbg.enabled ()) then (
    Fleche.Memo.Intern.clear ();
    Fleche.Memo.Interp.clear ();
    Fleche.Memo.Admit.clear ();
    Fleche.Memo.Init.clear ();
    Fleche.Memo.Require.clear ();
    Gc.full_major ())
  else begin
    let rss0 = Dbg.rss_kb () in
    let t0 = Dbg.now () in
    let g0 = Gc.quick_stat () in
    Fleche.Memo.Intern.clear ();
    Fleche.Memo.Interp.clear ();
    Fleche.Memo.Admit.clear ();
    Fleche.Memo.Init.clear ();
    Fleche.Memo.Require.clear ();
    let t_clear = Dbg.now () in
    Gc.full_major ();
    let t_gc = Dbg.now () in
    let g1 = Gc.quick_stat () in
    let rss1 = Dbg.rss_kb () in
    (* heap_words are in machine words; *8 bytes /1024 = kB on 64-bit.
       Only heap_words/top_heap_words are populated by quick_stat. *)
    let wkb w = w * 8 / 1024 in
    Dbg.log
      (Printf.sprintf
         "trimCaches: clear=%.3fs gc=%.3fs | rss %dkB -> %dkB (d=%+dkB) | \
          heap %dkB -> %dkB top=%dkB"
         (t_clear -. t0) (t_gc -. t_clear) rss0 rss1 (rss1 - rss0)
         (wkb g0.Gc.heap_words) (wkb g1.Gc.heap_words)
         (wkb g1.Gc.top_heap_words))
  end

let do_handle ~fn ~token action =
  match action with
  | Action.Now handler -> handler ~token
  | Action.Doc { uri; handler } ->
    let open Coq.Compat.Result.O in
    let* doc = fn ~token ~uri |> of_pet_err in
    handler ~token ~doc
  | Action.Pos { uri; point; handler } ->
    let open Coq.Compat.Result.O in
    let* doc = fn ~token ~uri |> of_pet_err in
    handler ~token ~doc ~point

(* Duplicate with lsp_core *)
let feedback_to_message fb =
  Lsp.JFleche.Message.(
    of_coq_message fb |> map ~f:Pp.string_of_ppcmds
    |> to_yojson (fun s -> `String s))

let feedback_to_data fbs =
  match fbs with
  | [] -> None
  | fbs -> Some (`List (List.map feedback_to_message fbs))

let request ~fn ~token ~id ~method_ ~params =
  let unhandled ~token ~method_ =
    match method_ with
    | s when String.equal SetWorkspace.method_ s ->
      do_handle ~fn ~token (do_request (module SetWorkspace) ~params)
    | s when String.equal TableOfContents.method_ s ->
      do_handle ~fn ~token (do_request (module TableOfContents) ~params)
    | _ ->
      (* JSON-RPC method not found *)
      let code = -32601 in
      let message = Format.asprintf "method %s not found" method_ in
      Error (Request.Error.make code message)
  in
  let do_handle = do_handle ~fn in
  match handle_request ~do_handle ~unhandled ~token ~method_ ~params with
  | Ok result -> Lsp.Base.Response.mk_ok ~id ~result
  | Error Request.Error.{ code; payload; feedback } ->
    (* for now *)
    let message = payload in
    let data = feedback_to_data feedback in
    Lsp.Base.Response.mk_error ~id ~code ~message ~data

type doc_handler =
     token:Coq.Limits.Token.t
  -> uri:Lang.LUri.File.t
  -> Fleche.Doc.t Petanque.Agent.R.t

let interp_raw ~fn ~token (r : Lsp.Base.Message.t) :
    Lsp.Base.Message.t option =
  match r with
  | Request { id; method_; params } ->
    let response = request ~fn ~token ~id ~method_ ~params in
    Some (Lsp.Base.Message.response response)
  | Notification { method_; params = _ } when String.equal method_ "petanque/trimCaches" ->
    (* Free Flèche's global memoization tables.  No response; state_ids
       outstanding on the client side stay valid because obj_map is
       untouched. *)
    trim_caches ();
    None
  | Notification { method_; params = _ } ->
    let message = "unhandled notification: " ^ method_ in
    let log = Lsp.Base.mk_logTrace ~message ~verbose:None in
    Some (Lsp.Base.Message.Notification log)
  | Response (Ok { id; _ }) | Response (Error { id; _ }) ->
    let message = "unhandled response: " ^ string_of_int id in
    let log = Lsp.Base.mk_logTrace ~message ~verbose:None in
    Some (Lsp.Base.Message.Notification log)

(* Per-RPC instrumentation: log the method, wall duration, and RSS
   before/after each message so memory movement can be attributed to a
   specific operation.  Transparent (and zero-overhead) when logging is off. *)
let interp ~fn ~token (r : Lsp.Base.Message.t) : Lsp.Base.Message.t option =
  if not (Dbg.enabled ()) then interp_raw ~fn ~token r
  else begin
    let method_ =
      match r with
      | Request { method_; _ } -> method_
      | Notification { method_; _ } -> "notif:" ^ method_
      | Response (Ok { id; _ }) | Response (Error { id; _ }) ->
        Printf.sprintf "response#%d" id
    in
    let rss0 = Dbg.rss_kb () in
    let t0 = Dbg.now () in
    Dbg.log (Printf.sprintf "RPC >> %-28s rss=%dkB" method_ rss0);
    let res = interp_raw ~fn ~token r in
    let rss1 = Dbg.rss_kb () in
    Dbg.log
      (Printf.sprintf "RPC << %-28s %.3fs rss=%dkB (d=%+dkB)" method_
         (Dbg.now () -. t0) rss1 (rss1 - rss0));
    res
  end
