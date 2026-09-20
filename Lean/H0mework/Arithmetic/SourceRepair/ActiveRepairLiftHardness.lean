import H0mework.Arithmetic.SourceRepair.ActiveRepairProducer

/-!
# Active repair-lift hardness

This file records a hard gate for active traced feasible demands closed by a
positive repair-lift finite descent.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Active produced demand plus traced positive repair lifts gives
double-negated atom-pair realization.

This is not witness extraction.  The proof first produces the traced feasible
demand, then uses finite descent/no-third-sink where arithmetic gap
persistence is generated from positive successor repair lifts. -/
theorem not_not_atom_pair_realization_of_active_produced_demand_by_repair_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (hActive : P.Active n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_repair_lift_and_no_third_sink
    terminal lift (P.produce hActive)

/-- The same active positive repair-lift data excludes traced feasible
projection defects at an active shell. -/
theorem no_traced_feasible_defect_of_active_produced_demand_by_repair_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (_hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_by_repair_lift_and_no_third_sink
    terminal lift k

/-- Nat multiplicative atom specialization with endpoint factorization
readout attached.

Supplying this uniformly is already Goldbach-strength at every active shell;
the theorem only exposes that burden rather than producing the repair lift. -/
theorem not_not_nat_factorized_atom_pair_realization_of_active_produced_demand_by_repair_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    (hActive : P.Active n k) :
    ¬¬ FactorizedAtomPairRealization
      NatMultiplicativelyAtomic
      natMultiplicativeAtomFactorizationCategory
      n k := by
  intro hNoFactorized
  exact
    not_not_atom_pair_realization_of_active_produced_demand_by_repair_lift
      P terminal lift hActive
      (by
        intro hRealized
        rcases hRealized with ⟨p, hEnergy⟩
        exact
          hNoFactorized
            (factorizedAtomPairRealizationOfPair
              natMultiplicativeAtomFactorizationCategory p hEnergy))

/-- Uniform active version: a Nat positive repair-lift family over all active
fibers gives double-negated factorized realization at each active shell. -/
theorem not_not_nat_factorized_atom_pair_realization_of_uniform_active_repair_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (terminal :
      ∀ n : Nat,
        TracedFeasibleAtomProjectionTerminalNoThirdSink
          SourcePath PhaseTrace SigmaTag ProducerTrace
          NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    (lift :
      ∀ n : Nat,
        TracedFeasibleAtomProjectionDefectRepairLift
          SourcePath PhaseTrace SigmaTag ProducerTrace
          NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    {n k : Nat}
    (hActive : P.Active n k) :
    ¬¬ FactorizedAtomPairRealization
      NatMultiplicativelyAtomic
      natMultiplicativeAtomFactorizationCategory
      n k :=
  not_not_nat_factorized_atom_pair_realization_of_active_produced_demand_by_repair_lift
    P (terminal n) (lift n) hActive

/-- Uniform active positive repair lifts exclude traced feasible defects at
every active shell. -/
theorem no_traced_feasible_defect_of_uniform_active_repair_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    (P :
      ActiveTracedFeasibleRepairProducer
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source)
    (terminal :
      ∀ n : Nat,
        TracedFeasibleAtomProjectionTerminalNoThirdSink
          SourcePath PhaseTrace SigmaTag ProducerTrace
          NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    (lift :
      ∀ n : Nat,
        TracedFeasibleAtomProjectionDefectRepairLift
          SourcePath PhaseTrace SigmaTag ProducerTrace
          NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    {n k : Nat}
    (hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_defect_of_active_produced_demand_by_repair_lift
    P (terminal n) (lift n) hActive


end RepresentationArithmeticAtomProjectionDefect
