import H0mework.Arithmetic.ProjectionDefect.CodeMediatedBoundedTransport
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.BoundedSuccessorRealizationSteps

/-!
# Code-mediated successor realization steps

This module lowers raw endpoint-code bounded transport to the smaller positive
step-family interface:

```text
code-mediated source/successor endpoint projection
-> realization at k gives realization at k+1
```

It avoids treating pair-object bounded transport as the primitive finite
descent mechanism.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Code-mediated source/successor endpoint projection directly lifts an
existing atom-pair realization to the successor residual shell.

This theorem constructs the successor realization from the successor raw
endpoint-code projection and multiplicative atom certification; it does not
first package the data as pair-object transport. -/
theorem atom_pair_realization_successor_of_code_mediated
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound k : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      CodeMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection)
    (hk : k < bound) :
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) ->
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) := by
  intro hRealized
  rcases hRealized with ⟨p, hEnergy⟩
  have hpBelow : ArithmeticAtomPair.energy p < bound := by
    rw [hEnergy]
    exact hk
  let q : ArithmeticAtomPair Atomic n :=
    atomPairOfEndpointCodePair
      (L.successorCode p hpBelow)
      (Projection.left_atomic (L.successor_code_projected p hpBelow))
      (Projection.right_atomic (L.successor_code_projected p hpBelow))
  refine ⟨q, ?_⟩
  have hqEnergy :
      ArithmeticAtomPair.energy q =
        Residual.residualEnergy (L.successorSource p hpBelow) := by
    calc
      ArithmeticAtomPair.energy q =
          EndpointCodePair.energy (L.successorCode p hpBelow) := by
            dsimp [q]
            exact
              atomPairOfEndpointCodePair_energy
                (L.successorCode p hpBelow)
                (Projection.left_atomic (L.successor_code_projected p hpBelow))
                (Projection.right_atomic (L.successor_code_projected p hpBelow))
      _ = Residual.residualEnergy (L.successorSource p hpBelow) :=
          Projection.codeProjection.code_energy_faithful
            (L.successor_code_projected p hpBelow)
  have hpEnergy :
      ArithmeticAtomPair.energy p =
        Residual.residualEnergy (L.sourceOfPair p hpBelow) := by
    have hSourceEnergy :
        EndpointCodePair.energy (endpointCodePairOfAtomPair p) =
          Residual.residualEnergy (L.sourceOfPair p hpBelow) :=
      Projection.codeProjection.code_energy_faithful
        (L.source_code_projects_pair p hpBelow)
    calc
      ArithmeticAtomPair.energy p =
          EndpointCodePair.energy (endpointCodePairOfAtomPair p) := by
            rw [endpointCodePairOfAtomPair_energy]
      _ = Residual.residualEnergy (L.sourceOfPair p hpBelow) :=
          hSourceEnergy
  have hStep :
      Residual.residualEnergy (L.sourceOfPair p hpBelow) + 1 =
        Residual.residualEnergy (L.successorSource p hpBelow) :=
    Residual.step_decreases_one
      (L.successor_step_to_source p hpBelow)
  calc
    ArithmeticAtomPair.energy q =
        Residual.residualEnergy (L.successorSource p hpBelow) :=
          hqEnergy
    _ = Residual.residualEnergy (L.sourceOfPair p hpBelow) + 1 :=
        hStep.symm
    _ = ArithmeticAtomPair.energy p + 1 := by
        rw [← hpEnergy]
    _ = k + 1 := by
        rw [hEnergy]

/-- Code-mediated bounded transport directly supplies the bounded positive
successor-realization step family. -/
theorem boundedAtomPairRealizationSuccessorStepsOfCodeMediated
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      CodeMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection) :
    BoundedAtomPairRealizationSuccessorSteps Atomic n bound := by
  exact {
    lift_realization := by
      intro k hk hRealized
      exact
        atom_pair_realization_successor_of_code_mediated
          L hk hRealized
  }

/-- Target-shell defect exclusion through code-mediated positive successor
steps. -/
theorem no_atom_projection_defect_at_bound_by_code_mediated_successor_steps
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (L :
      CodeMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n bound) :=
  no_atom_projection_defect_at_bound_by_successor_realization_steps
    terminal source bound
    (boundedAtomPairRealizationSuccessorStepsOfCodeMediated L)

/-- Demand-level code-mediated successor-step readout. -/
theorem not_not_atom_realization_of_demand_at_bound_by_code_mediated_successor_steps
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (L :
      CodeMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  not_not_atom_realization_of_demand_at_bound_by_successor_realization_steps
    terminal source
    (boundedAtomPairRealizationSuccessorStepsOfCodeMediated L)
    demand

/-- Traced target-shell defect exclusion through code-mediated positive
successor steps. -/
theorem no_traced_feasible_atom_projection_defect_at_bound_by_code_mediated_successor_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
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
    (L :
      CodeMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n bound) :=
  no_traced_feasible_atom_projection_defect_at_bound_by_successor_realization_steps
    terminal source step_path trace_descent bound
    (boundedAtomPairRealizationSuccessorStepsOfCodeMediated L)

/-- Traced demand-level code-mediated successor-step readout. -/
theorem not_not_atom_realization_of_traced_feasible_demand_at_bound_by_code_mediated_successor_steps
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
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
    (L :
      CodeMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  not_not_atom_realization_of_traced_feasible_demand_at_bound_by_successor_realization_steps
    terminal source step_path trace_descent
    (boundedAtomPairRealizationSuccessorStepsOfCodeMediated L)
    demand


end RepresentationArithmeticAtomProjectionDefect
