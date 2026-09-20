import H0mework.Arithmetic.ProjectionDefect.BoundedTransportHardness

/-!
# Source-mediated bounded transport

This file lowers bounded pair successor transport to source/projection data.

The point is not to construct atom pairs by endpoint search.  Instead, an
already-realized low-shell atom pair must have a source anchor, and source
repair dynamics must lift that anchor to a successor source object whose
faithful projection is defined.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Source-mediated bounded pair transport.

For every already-realized atom pair below the bound, the source side supplies:

* a source anchor projecting to that pair;
* a successor source object stepping down to the anchor; and
* defined faithful projection at the successor source.

This is the shape future GT/crystal/branching candidates should justify from
source dynamics, rather than postulating arithmetic pair transport directly.
-/
structure SourceMediatedBoundedPairTransport
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n bound : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  sourceOfPair :
    (p : ArithmeticAtomPair Atomic n) ->
      ArithmeticAtomPair.energy p < bound ->
        SourceEvidence
  source_projects_pair :
    ∀ (p : ArithmeticAtomPair Atomic n)
      (hEnergy : ArithmeticAtomPair.energy p < bound),
        Projection.project (sourceOfPair p hEnergy) = some p
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
  successor_projection_defined :
    ∀ (p : ArithmeticAtomPair Atomic n)
      (hEnergy : ArithmeticAtomPair.energy p < bound),
        Projection.project (successorSource p hEnergy) ≠ none

/-- Source-mediated lift data induces bounded pair successor transport. -/
def boundedPairEnergySuccessorTransportOfSourceMediated
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      SourceMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection) :
    BoundedAtomPairEnergySuccessorTransport Atomic n bound where
  liftPair := fun p hEnergy =>
    match Projection.project (L.successorSource p hEnergy) with
    | some q => q
    | none => p
  energy_lift := by
    intro p hEnergy
    cases hqProject : Projection.project (L.successorSource p hEnergy) with
    | none =>
        exact False.elim
          ((L.successor_projection_defined p hEnergy) hqProject)
    | some q =>
        have hqEnergy :
            ArithmeticAtomPair.energy q =
              Residual.residualEnergy (L.successorSource p hEnergy) :=
          Projection.energy_faithful hqProject
        have hpEnergy :
            ArithmeticAtomPair.energy p =
              Residual.residualEnergy (L.sourceOfPair p hEnergy) :=
          Projection.energy_faithful
            (L.source_projects_pair p hEnergy)
        have hStep :
            Residual.residualEnergy (L.sourceOfPair p hEnergy) + 1 =
              Residual.residualEnergy (L.successorSource p hEnergy) :=
          Residual.step_decreases_one
            (L.successor_step_to_source p hEnergy)
        calc
          ArithmeticAtomPair.energy q =
              Residual.residualEnergy (L.successorSource p hEnergy) := hqEnergy
          _ = Residual.residualEnergy (L.sourceOfPair p hEnergy) + 1 :=
              hStep.symm
          _ = ArithmeticAtomPair.energy p + 1 := by
              rw [← hpEnergy]

/-- Source-mediated bounded transport plus shell-zero realization realizes
every shell up to the target bound. -/
theorem atom_pair_realization_up_to_bound_of_zero_and_source_mediated_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (hZero :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0)
    (L :
      SourceMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection) :
    ∀ k : Nat,
      k ≤ bound ->
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k := by
  exact
    atom_pair_realization_up_to_bound_of_zero_and_bounded_pair_transport
      hZero
      (boundedPairEnergySuccessorTransportOfSourceMediated L)

/-- Target-shell defect exclusion using source-mediated bounded transport
instead of direct arithmetic pair transport. -/
theorem no_atom_projection_defect_at_bound_by_source_mediated_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (L :
      SourceMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n bound) :=
  no_atom_projection_defect_at_bound_by_bounded_pair_transport
    terminal source bound
    (boundedPairEnergySuccessorTransportOfSourceMediated L)

/-- Demand-level target-shell readout using source-mediated bounded transport.

This still gives only `¬¬` realization; it does not extract an atom pair. -/
theorem not_not_atom_realization_of_demand_at_bound_by_source_mediated_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (L :
      SourceMediatedBoundedPairTransport
        Atomic SourceEvidence Residual n bound Projection)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  not_not_atom_realization_of_demand_at_bound_by_bounded_pair_transport
    terminal source
    (boundedPairEnergySuccessorTransportOfSourceMediated L)
    demand


end RepresentationArithmeticAtomProjectionDefect
