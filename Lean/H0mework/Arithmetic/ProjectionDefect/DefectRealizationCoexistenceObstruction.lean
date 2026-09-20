import H0mework.Arithmetic.ProjectionDefect.BoundedPersistentTraceExtraction
import H0mework.Arithmetic.ProjectionDefect.DefectConditionedSourceAnchoredReturnPathLaw

/-!
# Defect-realization coexistence obstruction

This file extracts the minimal hard socket behind the source-holonomy and
source-anchor refinements:

```text
upper projection defect at k+1
+ lower atom-pair realization at k
-> False
```

Together with source residual descent this is exactly what is needed to
descend defects.  It does not construct an atom-pair realization at the upper
shell and does not assume an atom-pair successor operator.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Bounded defect-realization coexistence obstruction.

The obstruction is local below `target`: an upper defect at `k+1` cannot
coexist with a lower arithmetic atom-pair realization at `k`. -/
structure BoundedDefectRealizationCoexistenceObstruction
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    AtomProjectionTerminalNoThirdSink
      Atomic SourceEvidence Residual n
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  coexistence_obstruction :
    ∀ {k : Nat},
      k < target ->
        (defect :
          AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            False

namespace BoundedDefectRealizationCoexistenceObstruction

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {n target : Nat}

/-- Coexistence obstruction gives one-step defect descent. -/
theorem descend_below
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target)
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
      intro realization
      exact D.coexistence_obstruction hk defect realization
  }⟩

/-- Convert coexistence obstruction to the bounded source-side descent hard
gate. -/
def toBoundedSourceSideDefectDescent
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target) :
    BoundedSourceSideAtomProjectionDefectDescent
      Atomic SourceEvidence Residual n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_path_or_holonomy_structure := True
  source_path_or_holonomy_witness := trivial
  descend_below := by
    intro k hk _ hDefect
    exact D.descend_below hk hDefect

/-- Coexistence obstruction excludes the target projection defect. -/
theorem terminal_defect_of_target_defect
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  D.toBoundedSourceSideDefectDescent
    |>.terminal_defect_of_target_defect

/-- Coexistence obstruction excludes the target projection defect. -/
theorem no_target_arithmetic_projection_defect
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  D.toBoundedSourceSideDefectDescent.no_target_arithmetic_projection_defect

/-- A bounded persistent defect trace is impossible under coexistence
obstruction. -/
theorem no_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  D.toBoundedSourceSideDefectDescent
    |>.no_persistent_arithmetic_projection_defect_trace trace

/-- A target defect extracts a first-class bounded persistent defect trace by
coexistence-obstruction descent. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  D.toBoundedSourceSideDefectDescent
    |>.persistentTraceOfTargetDefect target_defect

/-- A first-class bounded persistent defect trace is impossible under
coexistence obstruction. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  D.no_persistent_arithmetic_projection_defect_trace trace.defect_at

/-- Target projection defects are impossible by explicitly extracting the
bounded persistent trace and then excluding it. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) := by
  intro target_defect
  exact
    D.no_bounded_persistent_arithmetic_projection_defect_trace
      (D.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
        target_defect)

/-- Demand-level readout from coexistence obstruction.

The result is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_demand
    (D :
      BoundedDefectRealizationCoexistenceObstruction
        Atomic SourceEvidence Residual n target)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toBoundedSourceSideDefectDescent
    |>.not_not_atom_realization_of_target_demand demand

end BoundedDefectRealizationCoexistenceObstruction

/-- A defect-conditioned source-anchor law induces the minimal coexistence
obstruction. -/
def coexistenceObstructionOfDefectConditionedSourceAnchored
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n target : Nat}
    (L :
      BoundedDefectConditionedSourceAnchoredReturnPathLaw
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    BoundedDefectRealizationCoexistenceObstruction
      Atomic SourceEvidence Residual n target where
  terminal_no_third_sink := terminal_no_third_sink
  source_descent := L.source_descent
  coexistence_obstruction := by
    intro k hk defect realization
    have hForward :
        Source.path defect.demand.evidence
          (L.source_descent.lowerEvidence defect.demand) :=
      L.step_path.step_is_path
        (L.source_descent.step_to_lower defect.demand)
    have hReturn :
        Source.path
          (L.source_descent.lowerEvidence defect.demand)
          defect.demand.evidence :=
      L.path_transitivity.trans
        (L.lower_to_anchor hk defect realization)
        (L.anchor_returns_to_upper hk defect realization)
    have hEq :
        L.source_descent.lowerEvidence defect.demand =
          defect.demand.evidence :=
      L.path_antisymmetry.closes hForward hReturn
    have hStep :
        Residual.residualEnergy
            (L.source_descent.lowerEvidence defect.demand) + 1 =
          Residual.residualEnergy defect.demand.evidence :=
      Residual.step_decreases_one
        (L.source_descent.step_to_lower defect.demand)
    have hImpossible :
        Residual.residualEnergy defect.demand.evidence + 1 =
          Residual.residualEnergy defect.demand.evidence := by
      rw [hEq] at hStep
      exact hStep
    have hlt :
        Residual.residualEnergy defect.demand.evidence <
          Residual.residualEnergy defect.demand.evidence := by
      calc
        Residual.residualEnergy defect.demand.evidence <
            Residual.residualEnergy defect.demand.evidence + 1 :=
          Nat.lt_succ_self _
        _ = Residual.residualEnergy defect.demand.evidence := hImpossible
    exact (Nat.lt_irrefl _) hlt

/-- Bounded traced defect-realization coexistence obstruction. -/
structure BoundedTracedDefectRealizationCoexistenceObstruction
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
  coexistence_obstruction :
    ∀ {k : Nat},
      k < target ->
        (defect :
          TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            False

namespace BoundedTracedDefectRealizationCoexistenceObstruction

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced coexistence obstruction gives one-step traced defect descent. -/
theorem descend_below
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
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
      intro realization
      exact D.coexistence_obstruction hk defect realization
  }⟩

/-- Convert traced coexistence obstruction to the bounded traced source-side
descent hard gate. -/
def toBoundedTracedSourceSideDefectDescent
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
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

/-- Traced coexistence obstruction excludes the target traced feasible
projection defect. -/
theorem terminal_traced_feasible_defect_of_target_defect
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
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

/-- Traced coexistence obstruction excludes the target traced feasible
projection defect. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  D.toBoundedTracedSourceSideDefectDescent
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- A bounded traced persistent defect trace is impossible under traced
coexistence obstruction. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
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
traced feasible defect trace by coexistence-obstruction descent. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
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

/-- A first-class bounded persistent traced feasible defect trace is
impossible under traced coexistence obstruction. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  D.no_persistent_traced_feasible_arithmetic_projection_defect_trace
    trace.defect_at

/-- Target traced feasible projection defects are impossible by explicitly
extracting the bounded persistent trace and then excluding it. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
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

/-- Demand-level traced readout from coexistence obstruction. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (D :
      BoundedTracedDefectRealizationCoexistenceObstruction
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

end BoundedTracedDefectRealizationCoexistenceObstruction

/-- A traced defect-conditioned source-anchor law induces the traced minimal
coexistence obstruction. -/
def tracedCoexistenceObstructionOfDefectConditionedSourceAnchored
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n target : Nat}
    (L :
      BoundedTracedDefectConditionedSourceAnchoredReturnPathLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    BoundedTracedDefectRealizationCoexistenceObstruction
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := terminal_no_third_sink
  source_descent := L.source_descent
  step_path := L.step_path
  trace_descent := L.trace_descent
  coexistence_obstruction := by
    intro k hk defect realization
    have hForward :
        Source.path defect.demand.demand.demand.evidence
          (L.source_descent.lowerEvidence
            defect.demand.demand.demand) :=
      L.step_path.step_is_path
        (L.source_descent.step_to_lower
          defect.demand.demand.demand)
    have hReturn :
        Source.path
          (L.source_descent.lowerEvidence
            defect.demand.demand.demand)
          defect.demand.demand.demand.evidence :=
      L.path_transitivity.trans
        (L.lower_to_anchor hk defect realization)
        (L.anchor_returns_to_upper hk defect realization)
    have hEq :
        L.source_descent.lowerEvidence defect.demand.demand.demand =
          defect.demand.demand.demand.evidence :=
      L.path_antisymmetry.closes hForward hReturn
    have hStep :
        Residual.residualEnergy
            (L.source_descent.lowerEvidence
              defect.demand.demand.demand) + 1 =
          Residual.residualEnergy
            defect.demand.demand.demand.evidence :=
      Residual.step_decreases_one
        (L.source_descent.step_to_lower
          defect.demand.demand.demand)
    have hImpossible :
        Residual.residualEnergy
            defect.demand.demand.demand.evidence + 1 =
          Residual.residualEnergy
            defect.demand.demand.demand.evidence := by
      rw [hEq] at hStep
      exact hStep
    have hlt :
        Residual.residualEnergy
            defect.demand.demand.demand.evidence <
          Residual.residualEnergy
            defect.demand.demand.demand.evidence := by
      calc
        Residual.residualEnergy
            defect.demand.demand.demand.evidence <
          Residual.residualEnergy
              defect.demand.demand.demand.evidence + 1 :=
            Nat.lt_succ_self _
        _ = Residual.residualEnergy
              defect.demand.demand.demand.evidence := hImpossible
    exact (Nat.lt_irrefl _) hlt


end RepresentationArithmeticAtomProjectionDefect
