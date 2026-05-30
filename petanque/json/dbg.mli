(** Lightweight debug logging for the pet RAM / RPC investigation.

    Writes timestamped lines to a dedicated log file, selected by environment:

    - [PET_DEBUG_LOG=<path>] logs to that file;
    - otherwise [PET_DEBUG=1] (or any non-empty, non-"0" value) logs to
      [/tmp/pet-dbg.log];
    - otherwise logging is disabled with zero overhead.

    The file is opened lazily on first use, in append mode, and each line is
    flushed immediately so [tail -f] follows a live session. *)

val enabled : unit -> bool
(** [enabled ()] is [true] iff a log sink was configured (cheap after the first
    call). Hot paths should guard expensive log-argument computation with it. *)

val log : string -> unit
(** [log msg] appends one timestamped, pid-tagged line. No-op when disabled. *)

val now : unit -> float
(** Monotonic-ish wall clock (seconds), for measuring durations. *)

val rss_kb : unit -> int
(** Current resident set size in kB, from [/proc/self/status] (Linux). Returns
    [0] when unavailable. *)
