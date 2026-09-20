import H0mework.Arithmetic.SourceAtoms.AntisymmetricSourceSideHolonomyGapDescent

/-!
# Source return-path gap descent

This file lowers the antisymmetric preholonomy hard gate one more step.

The source descent data already supplies:

```text
upper source evidence -> lower source evidence
strict residual drop
```

So a future source theorem should not have to rebuild the whole preloop.
The remaining hard socket is the return path:

```text
upper projection defect at k+1
+ lower atom-pair realization at k
-> lower source evidence -> upper source evidence
```

Together with source path antisymmetry this closes the preloop and therefore
derives gap descent without assuming atom-pair successor realization.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Bounded non-traced source return-path gap descent.

The only coexistence field is `lower_realization_returns`: a lower arithmetic
realization, if it coexists with the upper defect, forces a source path from
the lower source evidence back to the upper evidence.  The forward path and
strict residual drop are derived from `source_descent`. -/
structure BoundedSourceReturnPathGapDescent
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    AtomProjectionTerminalNoThirdSink
      Atomic SourceEvidence Residual n
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  path_antisymmetry :
    SourcePathAntisymmetry SourceEvidence Source
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

namespace BoundedSourceReturnPathGapDescent

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Convert the return-path socket to the antisymmetric preholonomy socket. -/
def toAntisymmetricSourceSideHolonomyGapDescent
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target) :
    BoundedAntisymmetricSourceSideHolonomyGapDescent
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_descent := D.source_descent
  path_antisymmetry := D.path_antisymmetry
  lower_realization_to_source_preloop := by
    intro k hk defect hLowerRealization
    exact {
      target := D.source_descent.lowerEvidence defect.demand
      source_to_target :=
        D.step_path.step_is_path
          (D.source_descent.step_to_lower defect.demand)
      target_to_source :=
        D.lower_realization_returns
          hk defect hLowerRealization
      residual_drops := by
        have hstep :
            Residual.residualEnergy
                (D.source_descent.lowerEvidence defect.demand) + 1 =
              Residual.residualEnergy defect.demand.evidence :=
          Residual.step_decreases_one
            (D.source_descent.step_to_lower defect.demand)
        rw [← hstep]
        exact
          Nat.lt_succ_self
            (Residual.residualEnergy
              (D.source_descent.lowerEvidence defect.demand))
    }

/-- Source return-path gap descent gives one-step defect descent. -/
theorem descend_below
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target)
    {k : Nat}
    (hk : k < target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  D.toAntisymmetricSourceSideHolonomyGapDescent.descend_below hk

/-- Convert the return-path socket to bounded defect-instability descent. -/
def toBoundedSourceSideDefectDescent
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target) :
    BoundedSourceSideAtomProjectionDefectDescent
      Atomic SourceEvidence Residual n target :=
  D.toAntisymmetricSourceSideHolonomyGapDescent
    |>.toBoundedSourceSideDefectDescent

/-- Source return-path gap descent excludes the target projection defect. -/
theorem terminal_defect_of_target_defect
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  D.toAntisymmetricSourceSideHolonomyGapDescent
    |>.terminal_defect_of_target_defect

/-- Source return-path gap descent excludes the target projection defect. -/
theorem no_target_arithmetic_projection_defect
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  D.toAntisymmetricSourceSideHolonomyGapDescent
    |>.no_target_arithmetic_projection_defect

/-- A bounded persistent defect trace is impossible under source return-path
gap descent. -/
theorem no_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  D.toAntisymmetricSourceSideHolonomyGapDescent
    |>.no_persistent_arithmetic_projection_defect_trace trace

/-- A target defect extracts a first-class bounded persistent defect trace by
source return-path descent. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  D.toAntisymmetricSourceSideHolonomyGapDescent
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent defect trace is impossible under source
return-path descent. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  D.toAntisymmetricSourceSideHolonomyGapDescent
    |>.no_bounded_persistent_arithmetic_projection_defect_trace trace

/-- Source return-path descent excludes a target defect through the explicit
bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  D.toAntisymmetricSourceSideHolonomyGapDescent
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level readout from source return-path gap descent.

The result is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_demand
    (D :
      BoundedSourceReturnPathGapDescent
        Atomic SourceEvidence Residual Source n target)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toAntisymmetricSourceSideHolonomyGapDescent
    |>.not_not_atom_realization_of_target_demand demand

end BoundedSourceReturnPathGapDescent

/-- Bounded traced source return-path gap descent.

This is the trace-preserving version.  Source/trace descent supplies the
lower traced demand; the hard coexistence field supplies only the return path
from lower evidence back to the upper defect's source evidence. -/
structure BoundedTracedSourceReturnPathGapDescent
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
  path_antisymmetry :
    SourcePathAntisymmetry SourceEvidence Source
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

namespace BoundedTracedSourceReturnPathGapDescent

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Convert the traced return-path socket to the traced antisymmetric
preholonomy socket. -/
def toTracedAntisymmetricSourceSideHolonomyGapDescent
    (D :
      BoundedTracedSourceReturnPathGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_descent := D.source_descent
  step_path := D.step_path
  trace_descent := D.trace_descent
  path_antisymmetry := D.path_antisymmetry
  lower_realization_to_source_preloop := by
    intro k hk defect hLowerRealization
    exact {
      target := D.source_descent.lowerEvidence defect.demand.demand.demand
      source_to_target :=
        D.step_path.step_is_path
          (D.source_descent.step_to_lower defect.demand.demand.demand)
      target_to_source :=
        D.lower_realization_returns
          hk defect hLowerRealization
      residual_drops := by
        have hstep :
            Residual.residualEnergy
                (D.source_descent.lowerEvidence
                  defect.demand.demand.demand) + 1 =
              Residual.residualEnergy
                defect.demand.demand.demand.evidence :=
          Residual.step_decreases_one
            (D.source_descent.step_to_lower
              defect.demand.demand.demand)
        rw [← hstep]
        exact
          Nat.lt_succ_self
            (Residual.residualEnergy
              (D.source_descent.lowerEvidence
                defect.demand.demand.demand))
    }

/-- Traced source return-path gap descent gives one-step traced defect
descent. -/
theorem descend_below
    (D :
      BoundedTracedSourceReturnPathGapDescent
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
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent.descend_below hk

/-- Convert the traced return-path socket to bounded traced
defect-instability descent. -/
def toBoundedTracedSourceSideDefectDescent
    (D :
      BoundedTracedSourceReturnPathGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedSourceSideAtomProjectionDefectDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent
    |>.toBoundedTracedSourceSideDefectDescent

/-- Traced source return-path gap descent excludes the target traced feasible
projection defect. -/
theorem terminal_traced_feasible_defect_of_target_defect
    (D :
      BoundedTracedSourceReturnPathGapDescent
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
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent
    |>.terminal_traced_feasible_defect_of_target_defect

/-- Traced source return-path gap descent excludes the target traced feasible
projection defect. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (D :
      BoundedTracedSourceReturnPathGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- A bounded traced persistent defect trace is impossible under traced source
return-path gap descent. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedSourceReturnPathGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace by source return-path descent. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedTracedSourceReturnPathGapDescent
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
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is impossible
under traced source return-path descent. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedSourceReturnPathGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      trace

/-- Traced source return-path descent excludes a target traced feasible defect
through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedTracedSourceReturnPathGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Traced demand-level readout from source return-path gap descent.

The result is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (D :
      BoundedTracedSourceReturnPathGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toTracedAntisymmetricSourceSideHolonomyGapDescent
    |>.not_not_atom_realization_of_target_traced_feasible_demand demand

end BoundedTracedSourceReturnPathGapDescent


end RepresentationArithmeticAtomProjectionDefect
