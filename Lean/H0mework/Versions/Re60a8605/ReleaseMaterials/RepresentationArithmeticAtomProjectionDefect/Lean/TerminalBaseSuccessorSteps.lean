import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.BoundedSuccessorRealizationSteps

/-!
# Terminal-base successor steps

This module separates the terminal contradiction from the bounded positive
successor-realization mechanism:

```text
no defect at shell 0
+ realization at k -> realization at k+1 below the bound
-> no defect at the target shell
```

It is useful for sigma-style terminal discharge routes whose terminal
contradiction is not packaged as `AtomProjectionTerminalNoThirdSink`, but as a
separately proved source/code no-third-sink discharge.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Target-shell finite descent from a terminal-base contradiction and bounded
positive realization-successor steps. -/
theorem no_atom_projection_defect_at_bound_by_terminal_base_successor_steps
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal0 :
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n 0))
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
      exact terminal0 hDefect
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

/-- Demand-level target-shell readout from a terminal-base contradiction and
bounded positive realization-successor steps. -/
theorem not_not_atom_realization_of_demand_at_bound_by_terminal_base_successor_steps
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    (terminal0 :
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n 0))
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (steps : BoundedAtomPairRealizationSuccessorSteps Atomic n bound)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound := by
  intro hMissing
  exact
    (no_atom_projection_defect_at_bound_by_terminal_base_successor_steps
      terminal0 source bound steps)
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩

/-- Traced target-shell finite descent from a terminal-base contradiction and
bounded positive realization-successor steps. -/
theorem no_traced_feasible_atom_projection_defect_at_bound_by_terminal_base_successor_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (terminal0 :
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n 0))
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
      exact terminal0 hDefect
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

/-- Traced demand-level readout from a terminal-base contradiction and bounded
positive realization-successor steps. -/
theorem not_not_atom_realization_of_traced_feasible_demand_at_bound_by_terminal_base_successor_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n bound : Nat}
    (terminal0 :
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n 0))
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
    (no_traced_feasible_atom_projection_defect_at_bound_by_terminal_base_successor_steps
      terminal0 source step_path trace_descent bound steps)
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩


end RepresentationArithmeticAtomProjectionDefect
