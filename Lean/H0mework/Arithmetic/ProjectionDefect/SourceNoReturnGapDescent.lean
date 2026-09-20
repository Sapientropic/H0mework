import H0mework.Arithmetic.ProjectionDefect.BoundedPersistentTraceExtraction
import H0mework.Arithmetic.ProjectionDefect.DefectRealizationCoexistenceObstruction

/-!
# Source no-return gap descent

This file lowers the return-path hard gate to a graded source condition.

The source-side shape is:

```text
source paths do not increase residual energy
source descent lowers residual energy by one
therefore lower source evidence cannot return to upper source evidence
```

So if a lower arithmetic atom realization would force that forbidden return
path, the upper defect and lower realization cannot coexist.  This derives
stable projection-defect exclusion without an atom-pair successor-realization
operator and without endpoint coverage.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Source paths are residual-energy nonincreasing.

This is a graded/no-return condition for source categories such as monotone
crystal strings, GT/branching posets, or any source dynamics where paths follow
residual lowering rather than climb back up. -/
structure SourceResidualPathNonincreasing
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  residual_nonincreasing :
    ∀ {source target : SourceEvidence},
      Source.path source target ->
        Residual.residualEnergy target ≤
          Residual.residualEnergy source

namespace SourceResidualPathNonincreasing

variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n : Nat}

/-- A one-step residual source descent cannot be followed by a source path
back to the upper evidence in a residual-nonincreasing source category. -/
theorem no_return_after_source_descent
    (M :
      SourceResidualPathNonincreasing
        SourceEvidence Residual Source)
    (S : SourceDemandOneStepDescent SourceEvidence Residual n)
    {k : Nat}
    (demand : RepRepairDemand SourceEvidence Residual n (k + 1)) :
    ¬ Source.path (S.lowerEvidence demand) demand.evidence := by
  intro hReturn
  have hmono :
      Residual.residualEnergy demand.evidence ≤
        Residual.residualEnergy (S.lowerEvidence demand) :=
    M.residual_nonincreasing hReturn
  have hstep :
      Residual.residualEnergy (S.lowerEvidence demand) + 1 =
        Residual.residualEnergy demand.evidence :=
    Residual.step_decreases_one (S.step_to_lower demand)
  have hlt :
      Residual.residualEnergy (S.lowerEvidence demand) <
        Residual.residualEnergy demand.evidence := by
    rw [← hstep]
    exact Nat.lt_succ_self _
  exact (Nat.not_lt_of_ge hmono) hlt

end SourceResidualPathNonincreasing

/-- Bounded source no-return gap descent.

The only arithmetic/source interaction field is `lower_realization_returns`:
if a lower atom-pair realization coexists with the upper projection defect, it
would force a forbidden source return from the lowered evidence back to the
upper evidence. -/
structure BoundedSourceNoReturnGapDescent
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    AtomProjectionTerminalNoThirdSink
      Atomic SourceEvidence Residual n
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  path_residual_nonincreasing :
    SourceResidualPathNonincreasing SourceEvidence Residual Source
  lower_realization_returns :
    ∀ {k : Nat},
      k < target ->
        (defect :
          AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            Source.path
              (source_descent.lowerEvidence defect.demand)
              defect.demand.evidence

namespace BoundedSourceNoReturnGapDescent

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Source no-return data proves the minimal coexistence obstruction. -/
def toDefectRealizationCoexistenceObstruction
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target) :
    BoundedDefectRealizationCoexistenceObstruction
      Atomic SourceEvidence Residual n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_descent := D.source_descent
  coexistence_obstruction := by
    intro k hk defect realization
    exact
      SourceResidualPathNonincreasing.no_return_after_source_descent
        D.path_residual_nonincreasing
        D.source_descent
        defect.demand
        (D.lower_realization_returns hk defect realization)

/-- Source no-return gives one-step defect descent. -/
theorem descend_below
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target)
    {k : Nat}
    (hk : k < target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  D.toDefectRealizationCoexistenceObstruction.descend_below hk

/-- Source no-return sends a target defect down to a terminal defect. -/
theorem terminal_defect_of_target_defect
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  D.toDefectRealizationCoexistenceObstruction
    |>.terminal_defect_of_target_defect

/-- Source no-return excludes the target projection defect. -/
theorem no_target_arithmetic_projection_defect
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  D.toDefectRealizationCoexistenceObstruction
    |>.no_target_arithmetic_projection_defect

/-- A bounded persistent defect trace is impossible under source no-return
gap descent. -/
theorem no_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  D.toDefectRealizationCoexistenceObstruction
    |>.no_persistent_arithmetic_projection_defect_trace trace

/-- A target defect extracts a first-class bounded persistent defect trace by
source no-return descent. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  D.toDefectRealizationCoexistenceObstruction
    |>.toBoundedSourceSideDefectDescent
    |>.persistentTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent defect trace is impossible under source
no-return gap descent. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  D.no_persistent_arithmetic_projection_defect_trace trace.defect_at

/-- Source no-return excludes the target projection defect by first extracting
the bounded persistent trace and then excluding it. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) := by
  intro target_defect
  exact
    D.no_bounded_persistent_arithmetic_projection_defect_trace
      (D.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
        target_defect)

/-- Demand-level readout from source no-return.

The conclusion is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_demand
    (D :
      BoundedSourceNoReturnGapDescent
        Atomic SourceEvidence Residual Source n target)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toDefectRealizationCoexistenceObstruction
    |>.not_not_atom_realization_of_target_demand demand

end BoundedSourceNoReturnGapDescent

/-- Bounded traced source no-return gap descent. -/
structure BoundedTracedSourceNoReturnGapDescent
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
  path_residual_nonincreasing :
    SourceResidualPathNonincreasing SourceEvidence Residual Source
  lower_realization_returns :
    ∀ {k : Nat},
      k < target ->
        (defect :
          TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            Source.path
              (source_descent.lowerEvidence defect.demand.demand.demand)
              defect.demand.demand.demand.evidence

namespace BoundedTracedSourceNoReturnGapDescent

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced source no-return data proves the traced minimal coexistence
obstruction. -/
def toTracedDefectRealizationCoexistenceObstruction
    (D :
      BoundedTracedSourceNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedDefectRealizationCoexistenceObstruction
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_descent := D.source_descent
  step_path := D.step_path
  trace_descent := D.trace_descent
  coexistence_obstruction := by
    intro k hk defect realization
    exact
      SourceResidualPathNonincreasing.no_return_after_source_descent
        D.path_residual_nonincreasing
        D.source_descent
        defect.demand.demand.demand
        (D.lower_realization_returns hk defect realization)

/-- Traced source no-return gives one-step traced defect descent. -/
theorem descend_below
    (D :
      BoundedTracedSourceNoReturnGapDescent
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
        Atomic SourceEvidence Residual Source n k) :=
  D.toTracedDefectRealizationCoexistenceObstruction.descend_below hk

/-- Traced source no-return sends a target traced defect down to a terminal
traced defect. -/
theorem terminal_traced_feasible_defect_of_target_defect
    (D :
      BoundedTracedSourceNoReturnGapDescent
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
  D.toTracedDefectRealizationCoexistenceObstruction
    |>.terminal_traced_feasible_defect_of_target_defect

/-- Traced source no-return excludes the target traced feasible projection
defect. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (D :
      BoundedTracedSourceNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  D.toTracedDefectRealizationCoexistenceObstruction
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- A bounded traced persistent defect trace is impossible under traced source
no-return gap descent. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedSourceNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  D.toTracedDefectRealizationCoexistenceObstruction
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace by source no-return descent. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedTracedSourceNoReturnGapDescent
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
  D.toTracedDefectRealizationCoexistenceObstruction
    |>.toBoundedTracedSourceSideDefectDescent
    |>.persistentTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is
impossible under traced source no-return gap descent. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedSourceNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  D.no_persistent_traced_feasible_arithmetic_projection_defect_trace
    trace.defect_at

/-- Traced source no-return excludes the target traced feasible projection
defect by first extracting the bounded persistent trace and then excluding
it. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedTracedSourceNoReturnGapDescent
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

/-- Demand-level traced readout from source no-return.

The conclusion is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (D :
      BoundedTracedSourceNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toTracedDefectRealizationCoexistenceObstruction
    |>.not_not_atom_realization_of_target_traced_feasible_demand demand

end BoundedTracedSourceNoReturnGapDescent

namespace CrystalBranchingSource

/-- The rank-one source category is residual-energy nonincreasing along its
native source paths.  This is the positive source-side instance for the
no-return layer; it says nothing about endpoint atom certification. -/
theorem rankOneSourceResidualPathNonincreasing :
    SourceResidualPathNonincreasing
      Nat rankOneResidualTransport rankOneSourceCategory := by
  refine { residual_nonincreasing := ?_ }
  intro source target hPath
  exact hPath

/-- A rank-one source lowering step cannot be followed by a native source path
back to the upper height. -/
theorem no_rank_one_return_after_source_descent
    {n k : Nat}
    (demand : RepRepairDemand Nat rankOneResidualTransport n (k + 1)) :
    ¬ rankOneSourceCategory.path
        ((rankOneSourceDemandOneStepDescent n).lowerEvidence demand)
        demand.evidence :=
  SourceResidualPathNonincreasing.no_return_after_source_descent
    rankOneSourceResidualPathNonincreasing
    (rankOneSourceDemandOneStepDescent n)
    demand

end CrystalBranchingSource


end RepresentationArithmeticAtomProjectionDefect
