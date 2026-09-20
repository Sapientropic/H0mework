import H0mework.Arithmetic.ProjectionDefect.AtomProjectionDefectCore

/-!
# Active repair producer socket

This file separates the upstream source producer from downstream projection
and atom-pair realization.

The producer only turns an active source-side repair obligation into a traced
feasible repair demand.  It does not contain endpoint projection, atom
certification, coverage, or an atom-pair witness.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Upstream producer for active traced feasible repair demands.

`Active n k` marks source/representation obligations that genuinely exist at
fiber `n` and residual shell `k`.  `produce` turns such an active obligation
into the traced feasible demand consumed by the projection-defect theory. -/
structure ActiveTracedFeasibleRepairProducer
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  Active : Nat -> Nat -> Prop
  produce :
    ∀ {n k : Nat},
      Active n k ->
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k

/-- A produced active demand is still a traced feasible demand. -/
def tracedFeasibleDemandOfActiveProducer
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    {n k : Nat}
    (hActive : P.Active n k) :
    TracedFeasibleRepRepairDemand
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n k :=
  P.produce hActive

/-- Produced active demand plus traced source/projection lift gives an
atom-pair realization.

The producer is upstream-only: the atom pair is still obtained from the
faithful projection lift, not from the producer. -/
theorem atom_pair_realization_of_active_produced_demand_by_source_projection_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (D :
      TracedFeasibleSourceProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_traced_feasible_source_projection_path_nonabsorbed_lift
    D (P.produce hActive)

/-- Produced active demand plus traced source/code-projection lift gives an
atom-pair realization.

This is the preferred endpoint-code route because atom certification remains a
separate field of the code projection. -/
theorem atom_pair_realization_of_active_produced_demand_by_source_code_projection_lift
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
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_traced_feasible_source_code_projection_path_nonabsorbed_lift
    D (P.produce hActive)

/-- Produced active demand plus traced source/projection lift rules out the
missing-realization branch at the active shell. -/
theorem not_traced_feasible_defect_of_active_produced_demand_by_source_projection_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (D :
      TracedFeasibleSourceProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  not_traced_feasible_defect_of_source_projection_path_nonabsorbed_lift
    D (P.produce hActive)

/-- Produced active demand plus traced source/code-projection lift rules out
the missing-realization branch at the active shell. -/
theorem not_traced_feasible_defect_of_active_produced_demand_by_source_code_projection_lift
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
  not_traced_feasible_defect_of_source_code_projection_path_nonabsorbed_lift
    D (P.produce hActive)


end RepresentationArithmeticAtomProjectionDefect
