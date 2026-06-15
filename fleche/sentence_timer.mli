(************************************************************************)
(* Copyright 2025      CNRS                    -- LGPL 2.1+ / GPL3+     *)
(* Written by: rocq-lsp contributors                                    *)
(************************************************************************)

(** Per-sentence wall-clock watchdog state, shared between the document check
    loop and the native watchdog thread.  See [sentence_timer.ml] for the
    rationale (why the bare interrupt flag rather than a token). *)

(** [bump ()] records "a new sentence just started" (heartbeat = now) and clears
    any previous timeout.  Called by the check loop before each sentence. *)
val bump : unit -> unit

(** [idle ()] disarms the watchdog (heartbeat = 0); called when the check loop
    stops executing sentences. *)
val idle : unit -> unit

(** Wall-clock time the current sentence started, or [0.0] when idle. *)
val started_at : unit -> float

(** [fire ()] records a timeout, disarms, and raises Coq's interrupt so the
    running sentence aborts.  Called by the watchdog on budget overrun. *)
val fire : unit -> unit

(** Whether the last interruption was a watchdog timeout (vs a cancellation). *)
val timed_out_p : unit -> bool

(** Clear the timeout flag after it has been consumed. *)
val clear : unit -> unit
