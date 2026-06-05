(* [confirm_extraction "<hash>"]: a coqc-loadable tactic that recomputes the
   digest of the closed goal at the current position the SAME way coq-lsp's
   extractor does (see coq/state.ml: close over the proof-LOCAL hypotheses with
   [it_mkNamedProd_or_LetIn], leaving the ambient section variables free; print
   fully explicit with notations off; hash the printed string). If the recorded
   hash differs from the live one the extraction is stale -> the tactic fails,
   so [coqc] errors at exactly the extraction site.

   The closing/printing/hash MUST stay in lockstep with coq/state.ml. *)

(* Print an EConstr fully explicit (implicits on, notations off). Mirrors
   coq/state.ml:print_explicit. *)
let print_explicit env sigma c =
  let open Constrextern in
  let si, sn = (!print_implicits, !print_no_symbol) in
  print_implicits := true;
  print_no_symbol := true;
  let finally () =
    print_implicits := si;
    print_no_symbol := sn
  in
  match Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c) with
  | s ->
    finally ();
    s
  | exception e ->
    finally ();
    raise e

(* Mirrors coq/state.ml:statement_hash. *)
let statement_hash s = String.sub (Digest.to_hex (Digest.string s)) 0 12

let confirm (expected : string) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let hyps = Proofview.Goal.hyps gl in
      let genv = Global.env () in
      let id_of = Context.Named.Declaration.get_id in
      (* ambient section variables are the named context of the global env;
         leave them free, quantify only the proof-local hypotheses *)
      let sec_ids =
        List.map id_of (Environ.named_context genv) |> Names.Id.Set.of_list
      in
      let local =
        List.filter (fun d -> not (Names.Id.Set.mem (id_of d) sec_ids)) hyps
      in
      let closed = EConstr.it_mkNamedProd_or_LetIn sigma concl local in
      let h = statement_hash (print_explicit genv sigma closed) in
      if String.equal h expected then Proofview.tclUNIT ()
      else
        Tacticals.tclZEROMSG
          (Pp.str
             (Printf.sprintf
                "confirm_extraction: STALE extraction (recorded hash %s, \
                 current goal hashes to %s). Regenerate the extracted lemma \
                 and update this hash."
                expected h)))
