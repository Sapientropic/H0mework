import H0mework.Arithmetic.SourceAtoms.GeneratedLoweringStrictPotential
import H0mework.Arithmetic.ProjectionDefect.BoundedPersistentTraceExtraction
import H0mework.Arithmetic.ProjectionDefect.SourceNoReturnGapDescent

/-!
# Source generated lowering residual no-return

This file connects generated unit-lowering dynamics to the residual no-return
hard gate.

If the native lowering potential is the residual-energy readout, every
generated source path is residual-energy nonincreasing.  Thus a one-step
source descent cannot be followed by a generated path back to the upper demand.

This is a source-side obstruction only.  It does not ask the source dynamics to
generate endpoint atoms or atom-pair successor realizations.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

namespace GeneratedLoweringPath

variable {SourceEvidence : Type u}
variable {edge : SourceEvidence -> SourceEvidence -> Prop}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}

/-- Generated lowering paths are residual-nonincreasing when each generating
edge is residual-nonincreasing. -/
theorem residual_nonincreasing
    (edge_residual_nonincreasing :
      ∀ {source target : SourceEvidence},
        edge source target ->
          Residual.residualEnergy target ≤
            Residual.residualEnergy source)
    {source target : SourceEvidence}
    (hPath : GeneratedLoweringPath edge source target) :
    Residual.residualEnergy target ≤
      Residual.residualEnergy source := by
  induction hPath with
  | refl =>
      exact Nat.le_refl _
  | tail hPrefix hEdge ih =>
      exact Nat.le_trans (edge_residual_nonincreasing hEdge) ih

end GeneratedLoweringPath

namespace SourceUnitLoweringDynamics

variable {SourceEvidence : Type u}

/-- If residual energy is the lowering potential, each unit lowering edge is
residual-nonincreasing. -/
theorem edgeResidualNonincreasingOfPotentialReadout
    (D : SourceUnitLoweringDynamics SourceEvidence)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source) :
    ∀ {source target : SourceEvidence},
      D.edge source target ->
        Residual.residualEnergy target ≤
          Residual.residualEnergy source := by
  intro source target hEdge
  rw [residual_eq_potential target, residual_eq_potential source]
  exact Nat.le_of_lt (D.edge_strictly_lowers hEdge)

/-- Generated lowering dynamics are residual-nonincreasing when each native
unit edge is residual-nonincreasing. -/
theorem toSourceResidualPathNonincreasingOfEdges
    (D : SourceUnitLoweringDynamics SourceEvidence)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (edge_residual_nonincreasing :
      ∀ {source target : SourceEvidence},
        D.edge source target ->
          Residual.residualEnergy target ≤
            Residual.residualEnergy source) :
    SourceResidualPathNonincreasing
      SourceEvidence Residual D.sourceCategory := by
  refine { residual_nonincreasing := ?_ }
  intro source target hPath
  exact
    GeneratedLoweringPath.residual_nonincreasing
      (Residual := Residual)
      edge_residual_nonincreasing hPath

/-- Generated lowering dynamics are residual-nonincreasing when their native
potential is the residual-energy readout. -/
theorem toSourceResidualPathNonincreasing
    (D : SourceUnitLoweringDynamics SourceEvidence)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source) :
    SourceResidualPathNonincreasing
      SourceEvidence Residual D.sourceCategory :=
  D.toSourceResidualPathNonincreasingOfEdges
    Residual
    (D.edgeResidualNonincreasingOfPotentialReadout
      Residual residual_eq_potential)

/-- A residual-reading generated lowering source descent cannot return to the
upper evidence. -/
theorem no_return_after_source_descent
    (D : SourceUnitLoweringDynamics SourceEvidence)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (residual_eq_potential :
      ∀ source : SourceEvidence,
        Residual.residualEnergy source = D.potential source)
    (S : SourceDemandOneStepDescent SourceEvidence Residual n)
    {k : Nat}
    (demand : RepRepairDemand SourceEvidence Residual n (k + 1)) :
    ¬ D.sourceCategory.path (S.lowerEvidence demand) demand.evidence :=
  SourceResidualPathNonincreasing.no_return_after_source_descent
    (D.toSourceResidualPathNonincreasing Residual residual_eq_potential)
    S demand

/-- An edge-residual-nonincreasing generated lowering source descent cannot
return to the upper evidence. -/
theorem no_return_after_source_descentOfEdges
    (D : SourceUnitLoweringDynamics SourceEvidence)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (edge_residual_nonincreasing :
      ∀ {source target : SourceEvidence},
        D.edge source target ->
          Residual.residualEnergy target ≤
            Residual.residualEnergy source)
    (S : SourceDemandOneStepDescent SourceEvidence Residual n)
    {k : Nat}
    (demand : RepRepairDemand SourceEvidence Residual n (k + 1)) :
    ¬ D.sourceCategory.path (S.lowerEvidence demand) demand.evidence :=
  SourceResidualPathNonincreasing.no_return_after_source_descent
    (D.toSourceResidualPathNonincreasingOfEdges
      Residual edge_residual_nonincreasing)
    S demand

end SourceUnitLoweringDynamics

/-- Bounded traced source no-return gap descent where the source category is
generated by unit lowering and each generating edge is residual-nonincreasing.

The only bridge from lower arithmetic realization to the upper defect is still
a source-return path.  The generated-lowering data only proves that such a
return is impossible once it would climb from shell `k` to shell `k + 1`. -/
structure BoundedTracedGeneratedLoweringNoReturnGapDescent
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (lowering_dynamics : SourceUnitLoweringDynamics SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual lowering_dynamics.sourceCategory n
  edge_residual_nonincreasing :
    ∀ {source target : SourceEvidence},
      lowering_dynamics.edge source target ->
        Residual.residualEnergy target ≤
          Residual.residualEnergy source
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility
      SourceEvidence Residual lowering_dynamics.sourceCategory
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual lowering_dynamics.sourceCategory n
  lower_realization_returns :
    ∀ {k : Nat},
      k < target ->
        (defect :
          TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual
            lowering_dynamics.sourceCategory n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            lowering_dynamics.sourceCategory.path
              (source_descent.lowerEvidence defect.demand.demand.demand)
              defect.demand.demand.demand.evidence

namespace BoundedTracedGeneratedLoweringNoReturnGapDescent

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {lowering_dynamics : SourceUnitLoweringDynamics SourceEvidence}
variable {n target : Nat}

/-- Generated-lowering no-return data is an instance of the generic traced
source no-return gap-descent socket. -/
def toBoundedTracedSourceNoReturnGapDescent
    (D :
      BoundedTracedGeneratedLoweringNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics n target) :
    BoundedTracedSourceNoReturnGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual
      lowering_dynamics.sourceCategory n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_descent := D.source_descent
  step_path := D.step_path
  trace_descent := D.trace_descent
  path_residual_nonincreasing :=
    lowering_dynamics.toSourceResidualPathNonincreasingOfEdges
      Residual D.edge_residual_nonincreasing
  lower_realization_returns := D.lower_realization_returns

theorem no_return_after_source_descent
    (D :
      BoundedTracedGeneratedLoweringNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics n target)
    {k : Nat}
    (demand : RepRepairDemand SourceEvidence Residual n (k + 1)) :
    ¬ lowering_dynamics.sourceCategory.path
        (D.source_descent.lowerEvidence demand)
        demand.evidence :=
  lowering_dynamics.no_return_after_source_descentOfEdges
    Residual D.edge_residual_nonincreasing D.source_descent demand

/-- Generated-lowering no-return proves traced target-defect exclusion. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (D :
      BoundedTracedGeneratedLoweringNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual
        lowering_dynamics.sourceCategory n target) :=
  D.toBoundedTracedSourceNoReturnGapDescent
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- A bounded traced persistent defect trace is impossible under
generated-lowering residual no-return. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedGeneratedLoweringNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual
            lowering_dynamics.sourceCategory n k)) :
    False :=
  D.toBoundedTracedSourceNoReturnGapDescent
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace
      trace

/-- A target traced feasible defect extracts a first-class bounded persistent
trace by generated-lowering no-return descent. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedTracedGeneratedLoweringNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics n target)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual
          lowering_dynamics.sourceCategory n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual lowering_dynamics.sourceCategory
      n target :=
  D.toBoundedTracedSourceNoReturnGapDescent
    |>.toTracedDefectRealizationCoexistenceObstruction
    |>.toBoundedTracedSourceSideDefectDescent
    |>.persistentTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is impossible
under generated-lowering residual no-return. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedGeneratedLoweringNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics n target)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics.sourceCategory
        n target) :
    False :=
  D.no_persistent_traced_feasible_arithmetic_projection_defect_trace
    trace.defect_at

/-- Target traced feasible projection defects are impossible by first
extracting the bounded persistent trace and then excluding it. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedTracedGeneratedLoweringNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual
        lowering_dynamics.sourceCategory n target) := by
  intro target_defect
  exact
    D.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      (D.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
        target_defect)

/-- Demand-level double-negated readout from generated-lowering no-return. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (D :
      BoundedTracedGeneratedLoweringNoReturnGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual lowering_dynamics n target)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual lowering_dynamics.sourceCategory n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toBoundedTracedSourceNoReturnGapDescent
    |>.not_not_atom_realization_of_target_traced_feasible_demand
      demand

end BoundedTracedGeneratedLoweringNoReturnGapDescent


end RepresentationArithmeticAtomProjectionDefect
