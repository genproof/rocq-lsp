(************************************************************************)
(* Debug logging for the pet RAM / RPC investigation.  See dbg.mli.     *)
(************************************************************************)

let t0 = Unix.gettimeofday ()
let now () = Unix.gettimeofday ()

(* Resolve the log sink once.  [None] => disabled. *)
let oc : out_channel option Lazy.t =
  lazy
    (let path =
       match Sys.getenv_opt "PET_DEBUG_LOG" with
       | Some p when String.length p > 0 -> Some p
       | _ -> (
         match Sys.getenv_opt "PET_DEBUG" with
         | Some v when not (String.equal v "0" || String.equal v "") ->
           Some "/tmp/pet-dbg.log"
         | _ -> None)
     in
     match path with
     | None -> None
     | Some p -> (
       try Some (open_out_gen [ Open_append; Open_creat; Open_wronly ] 0o644 p)
       with Sys_error _ -> None))

let enabled () = match Lazy.force oc with Some _ -> true | None -> false

let log (msg : string) : unit =
  match Lazy.force oc with
  | None -> ()
  | Some oc ->
    Printf.fprintf oc "[%10.3f pid=%d] %s\n%!" (now () -. t0) (Unix.getpid ())
      msg

let rss_kb () : int =
  match open_in "/proc/self/status" with
  | exception _ -> 0
  | ic ->
    let rec scan () =
      match input_line ic with
      | line ->
        if String.length line >= 6 && String.equal (String.sub line 0 6) "VmRSS:"
        then (
          match Scanf.sscanf line "VmRSS: %d" (fun kb -> kb) with
          | kb -> kb
          | exception _ -> 0)
        else scan ()
      | exception End_of_file -> 0
    in
    let r = (try scan () with _ -> 0) in
    close_in_noerr ic;
    r
