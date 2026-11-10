import H0mework.Arithmetic.SourceRepair.ActiveRepairProducer

/-!
# Active source/code factorized bridge

This file should connect the active source-code nonabsorbed lift directly to
multiplicative endpoint factorization readout, without passing through bounded
code-mediated transport.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Active produced demand plus traced source/code lift gives factorized
atom-pair realization.

The arithmetic pair is still produced by the source/code nonabsorbed lift:
factorization only reads the multiplicative atom endpoints already obtained
from raw endpoint-code projection plus atom certification.
-/
theorem factorized_atom_pair_realization_of_active_produced_demand_by_source_code_projection_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (D :
      TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    FactorizedAtomPairRealization Atomic F n k := by
  rcases
    atom_pair_realization_of_active_produced_demand_by_source_code_projection_lift
      P D hActive with
  ⟨p, hEnergy⟩
  exact factorizedAtomPairRealizationOfPair F p hEnergy

/-- The same active source/code lift also gives the double-negated
factorized readout expected by defect-exclusion APIs.

This is a weakening of the positive source/code bridge above; it is kept
separate from bounded transport so that the proof path remains visibly
source/trace/no-third-sink mediated.
-/
theorem not_not_factorized_atom_pair_realization_of_active_produced_demand_by_source_code_projection_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (D :
      TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    ¬¬ FactorizedAtomPairRealization Atomic F n k := by
  intro hNoFactorized
  exact hNoFactorized
    (factorized_atom_pair_realization_of_active_produced_demand_by_source_code_projection_lift
      F P D hActive)

/-- Active source/code nonabsorbed lift rules out traced feasible projection
defects while preserving the factorized bridge context. -/
theorem no_traced_feasible_defect_of_active_produced_demand_by_source_code_factorized_bridge
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (D :
      TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  not_traced_feasible_defect_of_active_produced_demand_by_source_code_projection_lift
    P D hActive

/-- Natural-number specialization of the active source/code factorized bridge. -/
theorem nat_factorized_atom_pair_realization_of_active_produced_demand_by_source_code_projection_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      NatAtomicEndpointCodeProjection SourceEvidence n Residual}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (D :
      TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic
      natMultiplicativeAtomFactorizationCategory
      n k :=
  factorized_atom_pair_realization_of_active_produced_demand_by_source_code_projection_lift
    natMultiplicativeAtomFactorizationCategory
    P D hActive


end RepresentationArithmeticAtomProjectionDefect
