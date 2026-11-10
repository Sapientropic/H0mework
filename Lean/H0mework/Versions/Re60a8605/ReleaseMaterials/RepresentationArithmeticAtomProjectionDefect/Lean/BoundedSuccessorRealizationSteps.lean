import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.SuccessorRealizationGapPersistence

/-!
# Bounded successor realization steps

This module lowers target-shell finite descent one more layer:

```text
for every j < bound:
  atom-pair realization at j -> atom-pair realization at j+1
```

The bounded pair/code-mediated transports should be treated as sources of
these positive steps, not as the primitive negative `gap_descends` mechanism.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Positive realization-successor steps below a target shell.

This is weaker and more mechanism-facing than bounded pair-object transport:
it asks only for existential atom-pair realizations to lift from `k` to
`k + 1`, for `k < bound`. -/
structure BoundedAtomPairRealizationSuccessorSteps
    (Atomic : Nat -> Prop) (n bound : Nat) where
  lift_realization :
    ∀ {k : Nat},
      k < bound ->
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k) ->
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k + 1)

/-- Restrict bounded realization-successor steps to a smaller target shell. -/
theorem boundedAtomPairRealizationSuccessorStepsRestrict
    {Atomic : Nat -> Prop} {n lower upper : Nat}
    (steps : BoundedAtomPairRealizationSuccessorSteps Atomic n upper)
    (hBound : lower ≤ upper) :
    BoundedAtomPairRealizationSuccessorSteps Atomic n lower := by
  exact {
    lift_realization := by
      intro k hk hRealized
      exact
        steps.lift_realization
          (k := k) (Nat.lt_of_lt_of_le hk hBound) hRealized
  }

/-- Bounded pair-object transport supplies bounded positive realization
successor steps. -/
theorem boundedAtomPairRealizationSuccessorStepsOfPairTransport
    {Atomic : Nat -> Prop} {n bound : Nat}
    (T : BoundedAtomPairEnergySuccessorTransport Atomic n bound) :
    BoundedAtomPairRealizationSuccessorSteps Atomic n bound := by
  exact {
    lift_realization := by
      intro k hk hRealized
      exact
        bounded_realization_transport_lift_of_pair_transport
          T hk hRealized
  }

/-- One-step defect descent using bounded positive realization-successor
steps below the target shell. -/
theorem atom_projection_defect_descend_of_bounded_successor_realization_steps
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound k : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (steps : BoundedAtomPairRealizationSuccessorSteps Atomic n bound)
    (hk : k < bound) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  atom_projection_defect_descend_of_successor_realization_step
    source
    (steps.lift_realization (k := k) hk)

/-- To exclude a target-shell defect, it is enough to have positive
realization-successor steps below that target shell plus the terminal
no-third-sink contradiction. -/
theorem no_atom_projection_defect_at_bound_by_successor_realization_steps
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n) :
    ∀ bound : Nat,
      BoundedAtomPairRealizationSuccessorSteps Atomic n bound ->
        ¬ Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n bound) := by
  intro bound
  induction bound with
  | zero =>
      intro _ hDefect
      exact
        (no_terminal_atom_projection_defect_of_no_third_sink terminal)
        hDefect
  | succ k ih =>
      intro steps hDefect
      have hPrev :
          Nonempty
            (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
        atom_projection_defect_descend_of_bounded_successor_realization_steps
          source steps (Nat.lt_succ_self k) hDefect
      exact
        ih
          (boundedAtomPairRealizationSuccessorStepsRestrict
            steps (Nat.le_succ k))
          hPrev

/-- Demand-level target-shell readout from bounded positive realization
successor steps.  This is still double-negated and does not extract a witness. -/
theorem not_not_atom_realization_of_demand_at_bound_by_successor_realization_steps
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (steps : BoundedAtomPairRealizationSuccessorSteps Atomic n bound)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound := by
  intro hMissing
  exact
    (no_atom_projection_defect_at_bound_by_successor_realization_steps
      terminal source bound steps)
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩

/-- Traced one-step defect descent using bounded positive
realization-successor steps below the target shell. -/
theorem traced_feasible_atom_projection_defect_descend_of_bounded_successor_realization_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n bound k : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (steps : BoundedAtomPairRealizationSuccessorSteps Atomic n bound)
    (hk : k < bound) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  traced_feasible_atom_projection_defect_descend_of_successor_realization_step
    source step_path trace_descent
    (steps.lift_realization (k := k) hk)

/-- Traced target-shell finite descent from bounded positive
realization-successor steps. -/
theorem no_traced_feasible_atom_projection_defect_at_bound_by_successor_realization_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n) :
    ∀ bound : Nat,
      BoundedAtomPairRealizationSuccessorSteps Atomic n bound ->
        ¬ Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n bound) := by
  intro bound
  induction bound with
  | zero =>
      intro _ hDefect
      exact
        (no_terminal_traced_feasible_atom_projection_defect_of_no_third_sink
          terminal)
        hDefect
  | succ k ih =>
      intro steps hDefect
      have hPrev :
          Nonempty
            (TracedFeasibleAtomProjectionDefect
              SourcePath PhaseTrace SigmaTag ProducerTrace
              Atomic SourceEvidence Residual Source n k) :=
        traced_feasible_atom_projection_defect_descend_of_bounded_successor_realization_steps
          source step_path trace_descent steps (Nat.lt_succ_self k) hDefect
      exact
        ih
          (boundedAtomPairRealizationSuccessorStepsRestrict
            steps (Nat.le_succ k))
          hPrev

/-- Traced demand-level readout from bounded positive realization-successor
steps. -/
theorem not_not_atom_realization_of_traced_feasible_demand_at_bound_by_successor_realization_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n bound : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (steps : BoundedAtomPairRealizationSuccessorSteps Atomic n bound)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound := by
  intro hMissing
  exact
    (no_traced_feasible_atom_projection_defect_at_bound_by_successor_realization_steps
      terminal source step_path trace_descent bound steps)
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩

/-- Bounded pair transport is only one way to supply the positive-step family
needed by traced finite descent. -/
theorem no_traced_feasible_atom_projection_defect_at_bound_by_bounded_pair_transport_via_successor_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n bound : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n bound) :=
  no_traced_feasible_atom_projection_defect_at_bound_by_successor_realization_steps
    terminal source step_path trace_descent bound
    (boundedAtomPairRealizationSuccessorStepsOfPairTransport pair_transport)


end RepresentationArithmeticAtomProjectionDefect
