import CodeCalculus.Soundness
import CodeCalculus.KernelObligations
import CodeCalculus.ExactDistance

namespace CodeCalculus

/-!
# Annotated-term soundness over the evaluation of a closed term

`judgment_soundness` (`Soundness.lean`) takes the chain of states as a
hypothesis: any list of states related step by step by `Eval`. This module
supplies the chain from the evaluation itself, which is the `Eval` conjunct
of `spec/OPERATIONAL_SEMANTICS.md` §4.11.

`Trace m s cs t` says that the command `m`, run from the state `s`, passes
through the states `cs` in order and ends at `t`, with one state per
primitive step: a command that is not a sequence contributes its output
state, and `m₁ ; m₂` contributes the states of `m₁` followed by those of
`m₂`. The chain of the evaluation is `s :: cs`.

* `trace_of_eval` and `Trace.eval`: a command has a trace from `s` to `t`
  exactly when `Eval m s t` (`eval_iff_trace`).
* `Trace.unique`: the trace is determined by the command and the input
  state, through `eval_deterministic`.
* `Trace.chain`, `Trace.getLast`, `Trace.length`: the trace is a `Chain`
  from `s` to `t` with one state per primitive step of `m`.
* `judgment_soundness_of_trace`: every annotation derivable over the trace
  of an evaluation from a well-formed input is true of it.
  `judgment_soundness_of_eval` and `judgment_soundness_of_term` state the
  same from `Eval m s t` and from `EvalTerm`, and the `_exact` forms
  instantiate the measure with the exact distance, leaving no measure
  hypothesis.

What stays a hypothesis: the well-formedness of the state the term's
expression evaluates to. `EvalExpr` on `StateExpr.base` returns the base
state as given, so no theorem about `EvalExpr` alone can supply it.
-/

/-- A command is a sequence. -/
def Command.isSeq : Command → Bool
  | .seq _ _ => true
  | _ => false

/-- The number of primitive steps of a command: its leaves that are not
    sequences. -/
def Command.steps : Command → Nat
  | .seq m1 m2 => m1.steps + m2.steps
  | _ => 1

theorem Command.steps_of_not_seq {m : Command} (hm : m.isSeq = false) : m.steps = 1 := by
  cases m with
  | seq m1 m2 => cases hm
  | _ => rfl

/-- `Trace m s cs t`: the command `m`, run from `s`, passes through the
    states `cs` in order and ends at `t`, one state per primitive step. -/
inductive Trace : Command → CodeState → List CodeState → CodeState → Prop where
  | step {m : Command} {s t : CodeState} (hm : m.isSeq = false) (hstep : Eval m s t) :
      Trace m s [t] t
  | seq {m1 m2 : Command} {s u t : CodeState} {cs ds : List CodeState}
      (h1 : Trace m1 s cs u) (h2 : Trace m2 u ds t) :
      Trace (Command.seq m1 m2) s (cs ++ ds) t

/-- A trace is an evaluation of its command. -/
theorem Trace.eval {m : Command} {s t : CodeState} {cs : List CodeState}
    (h : Trace m s cs t) : Eval m s t := by
  induction h with
  | step _ hstep => exact hstep
  | seq _ _ ih1 ih2 => exact Eval.seq ih1 ih2

/-- Every evaluation has a trace. -/
theorem trace_of_eval : ∀ (m : Command) {s t : CodeState}, Eval m s t →
    ∃ cs, Trace m s cs t := by
  intro m
  induction m with
  | seq m1 m2 ih1 ih2 =>
      intro s t h
      cases h with
      | seq h1 h2 =>
          obtain ⟨cs, hcs⟩ := ih1 h1
          obtain ⟨ds, hds⟩ := ih2 h2
          exact ⟨cs ++ ds, Trace.seq hcs hds⟩
  | _ =>
      intro s t h
      exact ⟨[t], Trace.step rfl h⟩

/-- A command has a trace from `s` to `t` exactly when it evaluates from `s`
    to `t`. -/
theorem eval_iff_trace {m : Command} {s t : CodeState} :
    Eval m s t ↔ ∃ cs, Trace m s cs t :=
  ⟨trace_of_eval m, fun ⟨_, h⟩ => h.eval⟩

/-- The trace is determined by the command and the input state. -/
theorem Trace.unique {m : Command} {s t t' : CodeState} {cs cs' : List CodeState}
    (h : Trace m s cs t) (h' : Trace m s cs' t') : cs = cs' ∧ t = t' := by
  induction h generalizing cs' t' with
  | @step m s t hm hstep =>
      cases h' with
      | step _ hstep' =>
          have ht := eval_deterministic m s _ _ hstep hstep'
          subst ht
          exact ⟨rfl, rfl⟩
      | seq _ _ => cases hm
  | @seq m1 m2 s u t cs ds h1 h2 ih1 ih2 =>
      cases h' with
      | step hm _ => cases hm
      | seq h1' h2' =>
          obtain ⟨hcs, hu⟩ := ih1 h1'
          subst hcs
          subst hu
          obtain ⟨hds, ht⟩ := ih2 h2'
          subst hds
          subst ht
          exact ⟨rfl, rfl⟩

/-- The last state of a list that ends where a second list starts. -/
theorem getLast?_glue {u t : CodeState} {ds : List CodeState} :
    ∀ {cs : List CodeState} {s : CodeState}, (s :: cs).getLast? = some u →
      (u :: ds).getLast? = some t → (s :: (cs ++ ds)).getLast? = some t
  | [], s, h1, h2 => by
      have hs : s = u := by
        simpa only [List.getLast?_singleton, Option.some.injEq] using h1
      subst hs
      exact h2
  | y :: cs, s, h1, h2 => by
      have h1' : (y :: cs).getLast? = some u := by
        simpa only [List.getLast?_cons_cons] using h1
      show (s :: y :: (cs ++ ds)).getLast? = some t
      rw [List.getLast?_cons_cons]
      exact getLast?_glue h1' h2

/-- Two chains compose when the first ends where the second starts. -/
theorem chain_glue {u : CodeState} {ds : List CodeState} :
    ∀ {cs : List CodeState} {s : CodeState}, Chain (s :: cs) →
      (s :: cs).getLast? = some u → Chain (u :: ds) → Chain (s :: (cs ++ ds))
  | [], s, _, hlast, h2 => by
      have hs : s = u := by
        simpa only [List.getLast?_singleton, Option.some.injEq] using hlast
      subst hs
      exact h2
  | y :: cs, s, h1, hlast, h2 => by
      have hlast' : (y :: cs).getLast? = some u := by
        simpa only [List.getLast?_cons_cons] using hlast
      cases h1 with
      | cons hstep hrest =>
          show Chain (s :: y :: (cs ++ ds))
          exact Chain.cons hstep (chain_glue hrest hlast' h2)

/-- The trace ends at the output state. -/
theorem Trace.getLast {m : Command} {s t : CodeState} {cs : List CodeState}
    (h : Trace m s cs t) : (s :: cs).getLast? = some t := by
  induction h with
  | step _ _ => rfl
  | seq _ _ ih1 ih2 => exact getLast?_glue ih1 ih2

/-- The trace of an evaluation, with its input state, is a chain. -/
theorem Trace.chain {m : Command} {s t : CodeState} {cs : List CodeState}
    (h : Trace m s cs t) : Chain (s :: cs) := by
  induction h with
  | step _ hstep => exact Chain.cons hstep (Chain.single _)
  | seq h1 _ ih1 ih2 => exact chain_glue ih1 h1.getLast ih2

/-- The trace has one state per primitive step of the command. -/
theorem Trace.length {m : Command} {s t : CodeState} {cs : List CodeState}
    (h : Trace m s cs t) : cs.length = m.steps := by
  induction h with
  | step hm _ => rw [Command.steps_of_not_seq hm]; rfl
  | seq _ _ ih1 ih2 =>
      rw [List.length_append, ih1, ih2]
      rfl

/-- Soundness (§4.11) over the trace of an evaluation: every annotation
    derivable over the chain the command unfolds through, from a well-formed
    input, is true of that chain. The chain is not a hypothesis. -/
theorem judgment_soundness_of_trace (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {m : Command} {s t : CodeState}
    {cs : List CodeState} (htrace : Trace m s cs t) (hwf : EncodingWellFormed s) :
    ∀ a, Derives dMeasure (s :: cs) a → Models dMeasure (s :: cs) a :=
  judgment_soundness_of_head dMeasure hmono (s :: cs) htrace.chain
    (fun x hx => by
      have hxs : s = x := Option.some.inj hx
      rw [← hxs]
      exact hwf)

/-- Soundness (§4.11) from an evaluation: the evaluation has a trace, which
    is its only one (`Trace.unique`), and every annotation derivable over it
    is true of it. -/
theorem judgment_soundness_of_eval (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {m : Command} {s t : CodeState}
    (heval : Eval m s t) (hwf : EncodingWellFormed s) :
    ∃ cs, Trace m s cs t ∧
      ∀ a, Derives dMeasure (s :: cs) a → Models dMeasure (s :: cs) a := by
  obtain ⟨cs, hcs⟩ := trace_of_eval m heval
  exact ⟨cs, hcs, judgment_soundness_of_trace dMeasure hmono hcs hwf⟩

/-- Soundness (§4.11) for a closed term: the term's expression evaluates to a
    state `s`, its command has a trace from `s` to the term's value, and
    every annotation derivable over that trace is true of it. The
    well-formedness of `s` is the FD1 hypothesis. -/
theorem judgment_soundness_of_term (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {term : ClosedTerm} {t : CodeState}
    (heval : EvalTerm term t)
    (hwf : ∀ s, EvalExpr term.expr s → EncodingWellFormed s) :
    ∃ s cs, EvalExpr term.expr s ∧ Trace term.command s cs t ∧
      ∀ a, Derives dMeasure (s :: cs) a → Models dMeasure (s :: cs) a := by
  cases heval with
  | eval hexpr hcmd =>
      obtain ⟨cs, hcs, hsound⟩ :=
        judgment_soundness_of_eval dMeasure hmono hcmd (hwf _ hexpr)
      exact ⟨_, cs, hexpr, hcs, hsound⟩

/-- `judgment_soundness_of_trace` for the exact distance. -/
theorem judgment_soundness_of_trace_exact {m : Command} {s t : CodeState}
    {cs : List CodeState} (htrace : Trace m s cs t) (hwf : EncodingWellFormed s) :
    ∀ a, Derives exactMeasure (s :: cs) a → Models exactMeasure (s :: cs) a :=
  judgment_soundness_of_trace exactMeasure measureMonotone_exactMeasure htrace hwf

/-- `judgment_soundness_of_eval` for the exact distance. -/
theorem judgment_soundness_of_eval_exact {m : Command} {s t : CodeState}
    (heval : Eval m s t) (hwf : EncodingWellFormed s) :
    ∃ cs, Trace m s cs t ∧
      ∀ a, Derives exactMeasure (s :: cs) a → Models exactMeasure (s :: cs) a :=
  judgment_soundness_of_eval exactMeasure measureMonotone_exactMeasure heval hwf

/-- `judgment_soundness_of_term` for the exact distance. -/
theorem judgment_soundness_of_term_exact {term : ClosedTerm} {t : CodeState}
    (heval : EvalTerm term t)
    (hwf : ∀ s, EvalExpr term.expr s → EncodingWellFormed s) :
    ∃ s cs, EvalExpr term.expr s ∧ Trace term.command s cs t ∧
      ∀ a, Derives exactMeasure (s :: cs) a → Models exactMeasure (s :: cs) a :=
  judgment_soundness_of_term exactMeasure measureMonotone_exactMeasure heval hwf

end CodeCalculus
