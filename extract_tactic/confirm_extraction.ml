(* [confirm_extraction "<hash>"]: a coqc-loadable tactic that recomputes the
   digest of the closed goal at the current position the SAME way coq-lsp's
   extractor does (see coq/state.ml: close over the proof-LOCAL hypotheses with
   [it_mkNamedProd_or_LetIn], leaving the ambient section variables free; print
   fully explicit with notations off; hash the printed string). If the recorded
   hash differs from the live one the extraction is stale -> the tactic fails,
   so [coqc] errors at exactly the extraction site. On a match it [give_up]s
   (admits) the goal, so the recorded site reads just [confirm_extraction "<h>"]
   -- no separate [admit.] -- and the goal is discharged (the enclosing proof
   must be [Admitted], exactly as for the [admit] it replaces).

   The closing/printing/hash MUST stay in lockstep with coq/state.ml. *)

(* Print an EConstr fully explicit (implicits on, notations off). Mirrors
   coq/state.ml:print_explicit. *)
let print_explicit env sigma c =
  (* Rocq 9.2: the flag refs moved into the options table; see
     coq/state.ml:print_explicit for the same dance. *)
  let o_impl = [ "Printing"; "Implicit" ] and o_notn = [ "Printing"; "Notations" ] in
  let get k =
    match Goptions.get_option_value k with
    | Some f -> (
      match f () with
      | Goptions.BoolValue b -> b
      | _ -> false)
    | None -> false
  in
  let set k b = Goptions.set_bool_option_value k b in
  let si, sn = (get o_impl, get o_notn) in
  set o_impl true;
  set o_notn false;
  let finally () =
    set o_impl si;
    set o_notn sn
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
      if String.equal h expected then Proofview.give_up
      else
        Tacticals.tclZEROMSG
          (Pp.str
             (Printf.sprintf
                "confirm_extraction: STALE extraction (recorded hash %s, \
                 current goal hashes to %s). Regenerate the extracted lemma \
                 and update this hash."
                expected h)))
