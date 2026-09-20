import H0mework.Arithmetic.ProjectionDefect.BoundedPersistentTraceExtraction
import H0mework.Arithmetic.SourceAtoms.SourceHolonomyLoop

/-!
# Source-side holonomy gap descent

This file refines the hard gate one step further.

It does not assume:

```text
atom-pair realization at k -> atom-pair realization at k+1
```

Instead it exposes a source-side holonomy mechanism:

```text
upper projection defect at k+1
+ lower atom-pair realization at k
-> closed strict source residual holonomy
-> contradiction
-> lower projection defect at k
```

So gap persistence is derived from forbidden source holonomy, not from an
atom-pair successor-realization operator.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Bounded non-traced source-side holonomy gap descent.

The field `lower_realization_to_source_loop` is the hard mathematical socket:
a future source/GT/crystal/branching theorem must show that an upper defect
together with a lower arithmetic realization would close a strict residual
holonomy loop in the source category. -/
structure BoundedSourceSideHolonomyGapDescent
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    AtomProjectionTerminalNoThirdSink
      Atomic SourceEvidence Residual n
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  lower_realization_to_source_loop :
    ∀ {k : Nat},
      k < target ->
        (defect :
          AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            SourceClosedStrictResidualHolonomyAt
              SourceEvidence Residual Source
              (source := defect.demand.evidence)

namespace BoundedSourceSideHolonomyGapDescent

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- The holonomy socket gives one-step defect descent without an atom-pair
successor-realization premise. -/
theorem descend_below
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    {k : Nat}
    (hk : k < target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact ⟨{
    demand := lowerDemandOfSourceStep D.source_descent defect.demand
    noAtomRealization := by
      intro hLowerRealization
      exact
        no_source_closed_strict_residual_holonomy_at
          ⟨D.lower_realization_to_source_loop
            hk defect hLowerRealization⟩
  }⟩

/-- Convert source-side holonomy gap descent to the bounded hard-gate
instability certificate. -/
def toBoundedSourceSideDefectDescent
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    BoundedSourceSideAtomProjectionDefectDescent
      Atomic SourceEvidence Residual n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_path_or_holonomy_structure := True
  source_path_or_holonomy_witness := trivial
  descend_below := by
    intro k hk _ hDefect
    exact D.descend_below hk hDefect

/-- Source-side holonomy gap descent excludes the target projection defect. -/
theorem terminal_defect_of_target_defect
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  D.toBoundedSourceSideDefectDescent
    |>.terminal_defect_of_target_defect

/-- Source-side holonomy gap descent excludes the target projection defect. -/
theorem no_target_arithmetic_projection_defect
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  D.toBoundedSourceSideDefectDescent.no_target_arithmetic_projection_defect

/-- A bounded persistent defect trace is impossible under source-side
holonomy gap descent. -/
theorem no_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  D.toBoundedSourceSideDefectDescent
    |>.no_persistent_arithmetic_projection_defect_trace trace

/-- A target defect extracts a first-class bounded persistent defect trace by
source-side holonomy descent. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  D.toBoundedSourceSideDefectDescent
    |>.persistentTraceOfTargetDefect target_defect

/-- A first-class bounded persistent defect trace is impossible under
source-side holonomy descent. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  trace.false_of_bounded_descent D.toBoundedSourceSideDefectDescent

/-- Source-side holonomy descent excludes a target defect through the explicit
bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) := by
  intro target_defect
  exact
    D.no_bounded_persistent_arithmetic_projection_defect_trace
      (D.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
        target_defect)

/-- Demand-level readout from source-side holonomy gap descent.

The conclusion is only double-negated.  No endpoint witness is extracted. -/
theorem not_not_atom_realization_of_target_demand
    (D :
      BoundedSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toBoundedSourceSideDefectDescent
    |>.not_not_atom_realization_of_target_demand demand

end BoundedSourceSideHolonomyGapDescent

/-- Bounded traced source-side holonomy gap descent.

This is the preferred socket for the current research target: the defect
keeps sourcePath / phaseTrace / sigmaTag / producerTrace while source-side
holonomy forbids lower realizations and therefore descends the defect. -/
structure BoundedTracedSourceSideHolonomyGapDescent
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  lower_realization_to_source_loop :
    ∀ {k : Nat},
      k < target ->
        (defect :
          TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            SourceClosedStrictResidualHolonomyAt
              SourceEvidence Residual Source
              (source := defect.demand.demand.demand.evidence)

namespace BoundedTracedSourceSideHolonomyGapDescent

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- The traced holonomy socket gives one-step traced defect descent without an
atom-pair successor-realization premise. -/
theorem descend_below
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    {k : Nat}
    (hk : k < target) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact ⟨{
    demand :=
      lowerTracedFeasibleDemandOfSourceStep
        D.source_descent D.step_path D.trace_descent defect.demand
    noAtomRealization := by
      intro hLowerRealization
      exact
        no_source_closed_strict_residual_holonomy_at
          ⟨D.lower_realization_to_source_loop
            hk defect hLowerRealization⟩
  }⟩

/-- Convert traced source-side holonomy gap descent to the bounded hard-gate
instability certificate. -/
def toBoundedTracedSourceSideDefectDescent
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedSourceSideAtomProjectionDefectDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_path_or_holonomy_structure := True
  source_path_or_holonomy_witness := trivial
  descend_below := by
    intro k hk _ hDefect
    exact D.descend_below hk hDefect

/-- Traced source-side holonomy gap descent excludes the target traced
feasible projection defect. -/
theorem terminal_traced_feasible_defect_of_target_defect
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :=
  D.toBoundedTracedSourceSideDefectDescent
    |>.terminal_traced_feasible_defect_of_target_defect

/-- Traced source-side holonomy gap descent excludes the target traced
feasible projection defect. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  D.toBoundedTracedSourceSideDefectDescent
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- A bounded traced persistent defect trace is impossible under traced
source-side holonomy gap descent. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  D.toBoundedTracedSourceSideDefectDescent
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace by source-side holonomy descent. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  D.toBoundedTracedSourceSideDefectDescent
    |>.persistentTraceOfTargetDefect target_defect

/-- A first-class bounded persistent traced feasible defect trace is impossible
under traced source-side holonomy descent. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  trace.false_of_bounded_descent D.toBoundedTracedSourceSideDefectDescent

/-- Traced source-side holonomy descent excludes a target traced feasible
defect through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) := by
  intro target_defect
  exact
    D.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      (D.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
        target_defect)

/-- Traced demand-level readout from source-side holonomy gap descent.

The conclusion is only double-negated.  No endpoint witness is extracted. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (D :
      BoundedTracedSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toBoundedTracedSourceSideDefectDescent
    |>.not_not_atom_realization_of_target_traced_feasible_demand demand

end BoundedTracedSourceSideHolonomyGapDescent


end RepresentationArithmeticAtomProjectionDefect
