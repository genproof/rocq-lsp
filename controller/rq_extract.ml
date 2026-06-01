(************************************************************************)
(* Coq Language Server Protocol -- Extract goal to lemma                 *)
(* coq-lsp contributors                                                 *)
(************************************************************************)

(* [coq/extract] custom request: close the open goal at a position into a
   standalone [Definition <name>_Goal], emit a proof-skeleton file, and report
   how to discharge the original goal (an [eapply <name>_proof]). The goal file
   is always regenerated; the proof file is created only if absent (it may hold
   real work). See the design notes in the session log. *)

open Fleche

let write_file path s =
  let oc = open_out path in
  output_string oc s;
  close_out oc

(* Collect the import preamble (Require/From/Import/Export/Open Scope) up to the
   cursor line, so the generated files have the globals in scope. *)
let collect_requires ~(contents : Contents.t) ~upto_line =
  let lines = contents.lines in
  let n = min (Array.length lines) (upto_line + 1) in
  let pfx p s =
    String.length s >= String.length p && String.sub s 0 (String.length p) = p
  in
  let buf = Buffer.create 256 in
  for i = 0 to n - 1 do
    let l = lines.(i) in
    let s = String.trim l in
    if
      pfx "Require" s || pfx "From " s || pfx "Import " s || pfx "Export " s
      || pfx "Open Scope" s
    then (
      Buffer.add_string buf l;
      Buffer.add_char buf '\n')
  done;
  Buffer.contents buf

let module_name_of_path path =
  match Lang.LUri.(File.of_uri (of_string ("file://" ^ path))) with
  | Ok uri -> Names.DirPath.to_string (Coq.Workspace.dirpath_of_uri ~uri)
  | Error _ -> Filename.(remove_extension (basename path))

let starts_with p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

let any_prefix ps s = List.exists (fun p -> starts_with p s) ps

(* Vernac commands begin at column 0; matching the RAW (un-trimmed) line avoids
   being fooled by indented prose inside multi-line comments. *)
let proof_kw =
  [ "Lemma "; "Theorem "; "Fact "; "Corollary "; "Remark "; "Proposition "
  ; "Goal "; "Goal:"; "Example "; "Property " ]

(* The enclosing [Section <name>] at [upto] (line index), tracking nesting,
   using column-0 detection. *)
let enclosing_section ~(lines : string array) ~upto =
  let last = min (Array.length lines - 1) upto in
  let stack = ref [] in
  for i = 0 to last do
    let l = lines.(i) in
    if starts_with "Section " l then (
      match String.split_on_char ' ' (String.trim l) with
      | _ :: nm :: _ ->
        let nm =
          match String.index_opt nm '.' with
          | Some k -> String.sub nm 0 k
          | None -> nm
        in
        stack := (i, nm) :: !stack
      | _ -> ())
    else if starts_with "End " l then
      match !stack with _ :: rest -> stack := rest | [] -> ()
  done;
  match !stack with top :: _ -> Some top | [] -> None

(* Start line of the proof enclosing [upto] (the lemma we're extracting from):
   the last column-0 proof command at/before [upto]. *)
let enclosing_lemma_line ~(lines : string array) ~upto =
  let last = min (Array.length lines - 1) upto in
  let res = ref upto in
  for i = 0 to last do
    if any_prefix proof_kw lines.(i) then res := i
  done;
  !res

(* Copy the section setup verbatim in [a, b). We keep helper lemmas WITH their
   proofs: the extracted goal can reference them (e.g. VST helper lemmas), so
   dropping proofs is unsound. The enclosing heavy lemma itself is excluded
   (it starts at [b]). *)
let copy_preamble ~(lines : string array) ~a ~b =
  let buf = Buffer.create 8192 in
  for i = a to min (Array.length lines - 1) (b - 1) do
    Buffer.add_string buf lines.(i);
    Buffer.add_char buf '\n'
  done;
  Buffer.contents buf

let generate ~(doc : Doc.t) ~point ~name (ex : Coq.State.Extract.t) =
  let main_path = Lang.LUri.File.to_string_file doc.uri in
  let dir = Filename.dirname main_path in
  let goal_path = Filename.concat dir (name ^ "_goal.v") in
  let proof_path = Filename.concat dir (name ^ "_proof.v") in
  let upto = fst point in
  let lines = doc.contents.lines in
  let sec = enclosing_section ~lines ~upto in
  (* Real imports precede any Section; bounding the scan there avoids capturing
     prose inside in-proof comments (e.g. a line starting "From H35: ..."). *)
  let req_bound = match sec with Some (l, _) -> l | None -> upto in
  let requires = collect_requires ~contents:doc.contents ~upto_line:req_bound in
  let goal_mod = module_name_of_path goal_path in
  (* If the goal lives in a Section, reconstruct that section (its variables AND
     definitions) so that both the goal AND any moved proof's references to
     section-local helpers resolve standalone. We do this whenever inside a
     section, even with no section variables. *)
  let body =
    match sec with
    | Some (sec_line, sec_name) ->
      let lemma_line = enclosing_lemma_line ~lines ~upto in
      let preamble = copy_preamble ~lines ~a:(sec_line + 1) ~b:lemma_line in
      Printf.sprintf
        "Section %s.\n%s\nDefinition %s_Goal : Prop :=\n%s.\nEnd %s.\n" sec_name
        preamble name ex.statement sec_name
    | None ->
      Printf.sprintf "Definition %s_Goal : Prop :=\n%s.\n" name ex.statement
  in
  (* Goal file: always regenerated. *)
  let goal_src =
    Printf.sprintf
      "(* GENERATED by coq-lsp extract -- do not edit, regenerated on each \
       extract *)\n\
       %s\n\
       %s"
      requires body
  in
  write_file goal_path goal_src;
  (* Proof file: created only if absent (may contain real work). *)
  let created_proof = not (Sys.file_exists proof_path) in
  if created_proof then (
    let intros =
      match ex.intro_names with
      | [] -> "idtac"
      | l -> "intros " ^ String.concat " " l
    in
    (* Section discharge turns [<name>_Goal] into a function of the section
       vars, so the lemma proves [forall <svs>, <name>_Goal <svs>]. *)
    let goal_app =
      match ex.section_vars with
      | [] -> name ^ "_Goal"
      | svs ->
        let s = String.concat " " svs in
        Printf.sprintf "forall %s, %s_Goal %s" s name s
    in
    let proof_src =
      Printf.sprintf
        "%s\n\
         Require Import %s.\n\n\
         Lemma %s_proof : %s.\n\
         Proof.\n\
        \  %s.\n\
        \  (* VST: try [unfold abbreviate in *.] to restore the display *)\n\
         Admitted.\n"
        requires goal_mod name goal_app intros
    in
    write_file proof_path proof_src);
  `Assoc
    [ ("goal_file", `String goal_path)
    ; ("proof_file", `String proof_path)
    ; ("goal_module", `String goal_mod)
    ; ("n_binders", `Int (List.length ex.intro_names))
    ; ("regenerated_goal", `Bool true)
    ; ("created_proof", `Bool created_proof)
    ; ("apply_with", `String (Printf.sprintf "eapply %s_proof" name))
    ]

let extract ~name () ~token ~doc ~point =
  let inner () =
    let node = Info.LC.node ~doc ~point Info.Prev in
    match node with
    | None ->
      Coq.Protect.E.ok (Error (Request.Error.make 1 "extract: no node at point"))
    | Some node ->
      let st = Doc.Node.state node in
      let open Coq.Protect.E.O in
      let+ ex = Coq.State.extract_goal ~token ~st in
      Ok (generate ~doc ~point ~name ex)
  in
  let lines = Fleche.Doc.lines doc in
  Request.R.of_execution ~lines ~name:"extract" ~f:inner ()
