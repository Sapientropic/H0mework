import H0mework.Arithmetic.ProjectionDefect.SourceMediatedBoundedTransport

/-!
# Code-mediated bounded transport

This file lowers source-mediated bounded transport one layer further: the
projection data is raw endpoint-code projection plus multiplicative atom
certification, not a direct atom-pair projection functor.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Raw endpoint code readout of an already-realized atom pair. -/
def endpointCodePairOfAtomPair
    {Atomic : Nat -> Prop} {n : Nat}
    (p : ArithmeticAtomPair Atomic n) :
    EndpointCodePair n where
  leftCode := p.left.code
  rightCode := p.right.code

@[simp]
theorem endpointCodePairOfAtomPair_energy
    {Atomic : Nat -> Prop} {n : Nat}
    (p : ArithmeticAtomPair Atomic n) :
    EndpointCodePair.energy (endpointCodePairOfAtomPair p) =
      ArithmeticAtomPair.energy p := by
  rfl

/-- Source-mediated bounded transport through raw endpoint-code projection.

For every already-realized atom pair below the bound, the source side supplies
a code-projected anchor for that pair and a successor source whose raw
endpoint-code projection is defined.  Multiplicative atomhood for successor
endpoints is read through `AtomicEndpointCodeProjection`.
-/
structure CodeMediatedBoundedPairTransport
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n bound : Nat)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  sourceOfPair :
    (p : ArithmeticAtomPair Atomic n) ->
      ArithmeticAtomPair.energy p < bound ->
        SourceEvidence
  source_code_projects_pair :
    ∀ (p : ArithmeticAtomPair Atomic n)
      (hEnergy : ArithmeticAtomPair.energy p < bound),
        Projection.codeProjection.projectCode (sourceOfPair p hEnergy) =
          some (endpointCodePairOfAtomPair p)
  successorSource :
    (p : ArithmeticAtomPair Atomic n) ->
      ArithmeticAtomPair.energy p < bound ->
        SourceEvidence
  successor_step_to_source :
    ∀ (p : ArithmeticAtomPair Atomic n)
      (hEnergy : ArithmeticAtomPair.energy p < bound),
        Residual.step
          (successorSource p hEnergy)
          (sourceOfPair p hEnergy)
  successorCode :
    (p : ArithmeticAtomPair Atomic n) ->
      ArithmeticAtomPair.energy p < bound ->
        EndpointCodePair n
  successor_code_projected :
    ∀ (p : ArithmeticAtomPair Atomic n)
      (hEnergy : ArithmeticAtomPair.energy p < bound),
        Projection.codeProjection.projectCode (successorSource p hEnergy) =
          some (successorCode p hEnergy)

/-- Code-mediated source data induces bounded pair successor transport. -/
def boundedPairEnergySuccessorTransportOfCodeMediated
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      CodeMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection) :
    BoundedAtomPairEnergySuccessorTransport Atomic n bound where
  liftPair := fun p hEnergy =>
    atomPairOfEndpointCodePair
      (L.successorCode p hEnergy)
      (Projection.left_atomic (L.successor_code_projected p hEnergy))
      (Projection.right_atomic (L.successor_code_projected p hEnergy))
  energy_lift := by
    intro p hEnergy
    have hqEnergy :
        ArithmeticAtomPair.energy
            (atomPairOfEndpointCodePair
              (L.successorCode p hEnergy)
              (Projection.left_atomic (L.successor_code_projected p hEnergy))
              (Projection.right_atomic (L.successor_code_projected p hEnergy))) =
          Residual.residualEnergy (L.successorSource p hEnergy) := by
      calc
        ArithmeticAtomPair.energy
            (atomPairOfEndpointCodePair
              (L.successorCode p hEnergy)
              (Projection.left_atomic (L.successor_code_projected p hEnergy))
              (Projection.right_atomic (L.successor_code_projected p hEnergy))) =
            EndpointCodePair.energy (L.successorCode p hEnergy) :=
              atomPairOfEndpointCodePair_energy
                (L.successorCode p hEnergy)
                (Projection.left_atomic (L.successor_code_projected p hEnergy))
                (Projection.right_atomic (L.successor_code_projected p hEnergy))
        _ = Residual.residualEnergy (L.successorSource p hEnergy) :=
              Projection.codeProjection.code_energy_faithful
                (L.successor_code_projected p hEnergy)
    have hpEnergy :
        ArithmeticAtomPair.energy p =
          Residual.residualEnergy (L.sourceOfPair p hEnergy) := by
      have hSourceEnergy :
          EndpointCodePair.energy (endpointCodePairOfAtomPair p) =
            Residual.residualEnergy (L.sourceOfPair p hEnergy) :=
        Projection.codeProjection.code_energy_faithful
          (L.source_code_projects_pair p hEnergy)
      calc
        ArithmeticAtomPair.energy p =
            EndpointCodePair.energy (endpointCodePairOfAtomPair p) := by
              rw [endpointCodePairOfAtomPair_energy]
        _ = Residual.residualEnergy (L.sourceOfPair p hEnergy) :=
            hSourceEnergy
    have hStep :
        Residual.residualEnergy (L.sourceOfPair p hEnergy) + 1 =
          Residual.residualEnergy (L.successorSource p hEnergy) :=
      Residual.step_decreases_one
        (L.successor_step_to_source p hEnergy)
    calc
      ArithmeticAtomPair.energy
          (atomPairOfEndpointCodePair
            (L.successorCode p hEnergy)
            (Projection.left_atomic (L.successor_code_projected p hEnergy))
            (Projection.right_atomic (L.successor_code_projected p hEnergy))) =
          Residual.residualEnergy (L.successorSource p hEnergy) :=
            hqEnergy
      _ = Residual.residualEnergy (L.sourceOfPair p hEnergy) + 1 :=
          hStep.symm
      _ = ArithmeticAtomPair.energy p + 1 := by
          rw [← hpEnergy]

/-- Code-mediated bounded transport plus shell-zero realization realizes every
shell up to the target bound. -/
theorem atom_pair_realization_up_to_bound_of_zero_and_code_mediated_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (hZero :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0)
    (L :
      CodeMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection) :
    ∀ k : Nat,
      k ≤ bound ->
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k := by
  exact
    atom_pair_realization_up_to_bound_of_zero_and_bounded_pair_transport
      hZero
      (boundedPairEnergySuccessorTransportOfCodeMediated L)

/-- Target-shell defect exclusion using code-mediated bounded transport. -/
theorem no_atom_projection_defect_at_bound_by_code_mediated_transport
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
  no_atom_projection_defect_at_bound_by_bounded_pair_transport
    terminal source bound
    (boundedPairEnergySuccessorTransportOfCodeMediated L)

/-- Demand-level target-shell readout using code-mediated bounded transport.

This still gives only `¬¬` realization; witness extraction is not claimed. -/
theorem not_not_atom_realization_of_demand_at_bound_by_code_mediated_transport
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
  not_not_atom_realization_of_demand_at_bound_by_bounded_pair_transport
    terminal source
    (boundedPairEnergySuccessorTransportOfCodeMediated L)
    demand


end RepresentationArithmeticAtomProjectionDefect
