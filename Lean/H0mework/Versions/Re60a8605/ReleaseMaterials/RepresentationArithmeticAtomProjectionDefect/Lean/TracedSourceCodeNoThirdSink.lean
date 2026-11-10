import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.ActiveSourceCodeFactorizedBridge

/-!
# Traced source/code no-third-sink adapter

This file splits the compressed
`terminal_code_projection_undefined_absorbs` field of the traced source/code
nonabsorbed lift into an explicit two-branch no-third-sink disposition.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Traced source/code no-third-sink disposition.

The projected branch is code-level: it only has to force raw endpoint-code
projection to be defined at the terminal traced demand.  Multiplicative
atom-pair materialization is still handled later by
`AtomicEndpointCodeProjection`.
-/
structure TracedSourceCodeNoThirdSinkDisposition
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  path_compatibility :
    SourceCodeProjectionPathCompatibility
      Atomic SourceEvidence Residual n Source Projection
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  projected_code_repair :
    ∀ {k : Nat},
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k ->
        Prop
  no_third_sink_on_code_silence :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k),
        Projection.codeProjection.projectCode
            (terminalTracedFeasibleDemandOfSourceDescent
              source_descent step_path trace_descent demand).demand.demand.evidence =
          none ->
        headroom_nonzero ->
          absorbed_static ∨ projected_code_repair demand
  projected_code_repair_defines_projection :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k),
        projected_code_repair demand ->
          Projection.codeProjection.projectCode
              (terminalTracedFeasibleDemandOfSourceDescent
                source_descent step_path trace_descent demand).demand.demand.evidence ≠
            none

/-- The no-third-sink disposition induces the older nonabsorbed lift domain. -/
def tracedSourceCodeProjectionPathNonabsorbedLiftDomainOfNoThirdSinkDisposition
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      TracedSourceCodeNoThirdSinkDisposition
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection) :
    TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual n Source Projection where
  source_descent := D.source_descent
  step_path := D.step_path
  trace_descent := D.trace_descent
  path_compatibility := D.path_compatibility
  absorbed_static := D.absorbed_static
  headroom_nonzero := D.headroom_nonzero
  headroom_witness := D.headroom_witness
  nonzero_forbids_absorbed_static :=
    D.nonzero_forbids_absorbed_static
  terminal_code_projection_undefined_absorbs := by
    intro k demand hNone
    cases
      D.no_third_sink_on_code_silence
        demand hNone D.headroom_witness with
    | inl hAbsorbed =>
        exact hAbsorbed
    | inr hProjected =>
        exact False.elim
          ((D.projected_code_repair_defines_projection demand hProjected) hNone)

/-- Source/code no-third-sink disposition realizes any traced feasible demand
by first deriving the nonabsorbed lift domain. -/
theorem atom_pair_realization_of_traced_feasible_demand_by_source_code_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      TracedSourceCodeNoThirdSinkDisposition
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_traced_feasible_source_code_projection_path_nonabsorbed_lift
    (tracedSourceCodeProjectionPathNonabsorbedLiftDomainOfNoThirdSinkDisposition D)
    demand

/-- The same source/code no-third-sink disposition rules out traced feasible
projection defects at every shell. -/
theorem no_traced_feasible_defect_by_source_code_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      TracedSourceCodeNoThirdSinkDisposition
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact defect.noAtomRealization
    (atom_pair_realization_of_traced_feasible_demand_by_source_code_no_third_sink
      D defect.demand)

/-- Active produced demand plus the explicit source/code no-third-sink
disposition gives factorized atom-pair realization. -/
theorem factorized_atom_pair_realization_of_active_produced_demand_by_source_code_no_third_sink
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
      TracedSourceCodeNoThirdSinkDisposition
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    FactorizedAtomPairRealization Atomic F n k :=
  factorized_atom_pair_realization_of_active_produced_demand_by_source_code_projection_lift
    F P
    (tracedSourceCodeProjectionPathNonabsorbedLiftDomainOfNoThirdSinkDisposition D)
    hActive

/-- Active produced demand plus the explicit source/code no-third-sink
disposition rules out traced feasible defects. -/
theorem no_traced_feasible_defect_of_active_produced_demand_by_source_code_no_third_sink
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
      TracedSourceCodeNoThirdSinkDisposition
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_defect_of_active_produced_demand_by_source_code_factorized_bridge
    P
    (tracedSourceCodeProjectionPathNonabsorbedLiftDomainOfNoThirdSinkDisposition D)
    hActive

/-- Natural-number specialization of the active source/code no-third-sink
factorized bridge. -/
theorem nat_factorized_atom_pair_realization_of_active_produced_demand_by_source_code_no_third_sink
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
      TracedSourceCodeNoThirdSinkDisposition
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual n Source Projection)
    (hActive : P.Active n k) :
    FactorizedAtomPairRealization
      NatMultiplicativelyAtomic
      natMultiplicativeAtomFactorizationCategory
      n k :=
  factorized_atom_pair_realization_of_active_produced_demand_by_source_code_no_third_sink
    natMultiplicativeAtomFactorizationCategory
    P D hActive


end RepresentationArithmeticAtomProjectionDefect
