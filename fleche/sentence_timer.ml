(************************************************************************)
(* Copyright 2025      CNRS                    -- LGPL 2.1+ / GPL3+     *)
(* Written by: rocq-lsp contributors                                    *)
(************************************************************************)
(* Per-sentence wall-clock watchdog for document checking.              *)
(************************************************************************)

(* Shared state between the document check loop (which runs on the checker
   thread and bumps the heartbeat before each sentence) and the native watchdog
   thread (which trips Coq's interrupt when a single sentence overruns its
   budget).  The interrupt reuses Coq's polled [Control.interrupt] flag -- the
   very mechanism a cancellation uses -- via [Coq.Limits.interrupt], so a
   diverging sentence is aborted at its next check-for-interrupt point.

   We deliberately do NOT use a cancellation token here: a token's [set] is
   sticky, so it would poison every subsequent sentence sharing the check's
   token.  Raising the bare interrupt flag aborts only the in-flight sentence;
   the next sentence's [Limits.limit] resets the flag and runs normally, which
   is what lets checking CONTINUE past a timed-out sentence (reified as a
   recoverable "Timeout!" error in [Doc]). *)

(* [beat] is the wall-clock time the current sentence started, or [0.0] when the
   checker is idle / between checks (so the watchdog never fires against a stale
   heartbeat). *)
let beat = ref 0.0

(* Per-sentence budget override (seconds); 0.0 = none (the watchdog uses
   [Config.sentence_timeout]).  Set for proof-closing commands when
   [Config.qed_timeout] > 0: instead of disarming entirely, the sentence
   runs under its own -- typically much larger -- budget. *)
let override = ref 0.0

(* Set by the watchdog when it trips the interrupt; read by [Doc] to tell a
   timeout interruption apart from a genuine cancellation (both surface as
   [Coq.Protect.R.Interrupted]). *)
let timed_out = ref false

(* Called by the check loop right before executing each sentence. *)
let bump () =
  timed_out := false;
  override := 0.0;
  beat := Unix.gettimeofday ()

(* Re-arm the CURRENT sentence under its own budget (proof-closing
   commands with [qed_timeout] > 0); keeps the heartbeat. *)
let set_budget b = override := b
let budget_override () = !override

(* Called when the check loop stops executing sentences (done / stopped), so the
   watchdog disarms. *)
let idle () =
  override := 0.0;
  beat := 0.0

let started_at () = !beat

(* Called by the watchdog every tick while the current sentence is over budget:
   record the timeout and (re-)raise Coq's interrupt so the running sentence
   aborts at its next [check_for_interrupt] point.  We re-arm rather than fire
   once because a single flag set can be consumed by an unrelated
   [check_for_interrupt] before the diverging tactic's own poll; re-setting each
   tick guarantees the tactic eventually observes it.  [Doc] disarms (via
   [idle]) the instant it reifies the timeout, so error recovery -- which runs
   Coq again -- is not itself interrupted. *)
let fire () =
  timed_out := true;
  Coq.Limits.interrupt ()

let timed_out_p () = !timed_out
let clear () = timed_out := false
