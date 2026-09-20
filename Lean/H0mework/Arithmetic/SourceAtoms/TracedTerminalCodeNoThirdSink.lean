import H0mework.Arithmetic.SourceRepair.CodeMediatedRepairLift

/-!
# Traced terminal code no-third-sink

This file adds a terminal-only raw endpoint-code no-third-sink adapter.

It is weaker than `TracedSourceCodeNoThirdSinkDisposition`: it only explains
the terminal contradiction used by finite descent, and does not directly
produce source/code projection for arbitrary traced demands.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Terminal projected-repair readout through raw endpoint-code projection.

The projected branch must identify a terminal traced feasible demand and show
that raw endpoint-code projection is defined there.  Multiplicative atomhood
is then read from `AtomicEndpointCodeProjection`; no atom-pair witness is
supplied as a separate field. -/
structure TracedTerminalCodeProjectionDefinedReadout
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  projected_repair : Prop
  terminal_demand :
    projected_repair ->
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n 0
  code_projection_defined :
    ∀ hProjected : projected_repair,
      Projection.codeProjection.projectCode
          (terminal_demand hProjected).demand.demand.evidence ≠ none

/-- Terminal projected-repair readout where raw endpoint-code projection
failure is absorbed.

This is closer to the sigma blueprint: the projected branch identifies the
terminal demand, but only says projection silence would force
`absorbed_static`.  Nonzero headroom later rules absorption out and recovers
defined raw code projection. -/
structure TracedTerminalCodeProjectionNonabsorbedReadout
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual)
    (absorbed_static : Prop) where
  projected_repair : Prop
  terminal_demand :
    projected_repair ->
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n 0
  code_projection_undefined_absorbs :
    ∀ hProjected : projected_repair,
      Projection.codeProjection.projectCode
          (terminal_demand hProjected).demand.demand.evidence = none ->
        absorbed_static

/-- A nonabsorbed terminal code readout gives defined raw code projection once
absorption has been ruled out. -/
theorem traced_terminal_code_projection_defined_of_nonabsorbed_readout
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    {absorbed_static : Prop}
    (R :
      TracedTerminalCodeProjectionNonabsorbedReadout
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection absorbed_static)
    (hNotAbsorbed : ¬ absorbed_static) :
    ∀ hProjected : R.projected_repair,
      Projection.codeProjection.projectCode
          (R.terminal_demand hProjected).demand.demand.evidence ≠ none := by
  intro hProjected hNone
  exact hNotAbsorbed
    (R.code_projection_undefined_absorbs hProjected hNone)

/-- A nonabsorbed terminal code readout induces a defined-code readout after
absorption is ruled out. -/
def tracedTerminalCodeProjectionDefinedReadoutOfNonabsorbed
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    {absorbed_static : Prop}
    (R :
      TracedTerminalCodeProjectionNonabsorbedReadout
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection absorbed_static)
    (hNotAbsorbed : ¬ absorbed_static) :
    TracedTerminalCodeProjectionDefinedReadout
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n Projection where
  projected_repair := R.projected_repair
  terminal_demand := R.terminal_demand
  code_projection_defined :=
    traced_terminal_code_projection_defined_of_nonabsorbed_readout
      R hNotAbsorbed

/-- A terminal raw endpoint-code readout materializes a terminal atom-pair
realization through atom certification and energy faithfulness. -/
theorem projected_repair_realizes_of_traced_terminal_code_defined_readout
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (R :
      TracedTerminalCodeProjectionDefinedReadout
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    R.projected_repair ->
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0 := by
  intro hProjected
  exact
    atom_pair_realization_of_atomic_code_defined_demand
      Projection
      (R.terminal_demand hProjected).demand.demand
      (R.code_projection_defined hProjected)

/-- Traced terminal no-third-sink whose projected branch is raw code
definedness, not a pre-supplied atom-pair witness. -/
structure TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_readout :
    TracedTerminalCodeProjectionDefinedReadout
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n Projection
  no_third_sink :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_readout.projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static

/-- Traced terminal no-third-sink where raw code projection failure in the
projected branch would force absorbed-static. -/
structure TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_readout :
    TracedTerminalCodeProjectionNonabsorbedReadout
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n Projection absorbed_static
  no_third_sink :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_readout.projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static

/-- Nonabsorbed raw-code terminal no-third-sink induces the defined raw-code
terminal law. -/
def tracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSinkOfCodeNonabsorbed
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n Projection where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_readout :=
    tracedTerminalCodeProjectionDefinedReadoutOfNonabsorbed
      L.projected_readout
      (L.nonzero_forbids_absorbed_static L.headroom_witness)
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static

/-- Raw-code terminal no-third-sink induces the materializing terminal law. -/
def tracedFeasibleAtomProjectionTerminalMaterializingNoThirdSinkOfCodeDefined
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_repair := L.projected_readout.projected_repair
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static
  projected_repair_realizes :=
    projected_repair_realizes_of_traced_terminal_code_defined_readout
      L.projected_readout

/-- Raw-code terminal no-third-sink induces the older terminal no-third-sink
socket used by finite descent. -/
def tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeDefined
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n :=
  tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing
    (tracedFeasibleAtomProjectionTerminalMaterializingNoThirdSinkOfCodeDefined L)

/-- Terminal raw-code no-third-sink excludes terminal traced feasible
projection defects. -/
theorem no_terminal_traced_feasible_atom_projection_defect_of_code_defined_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :=
  no_terminal_traced_feasible_atom_projection_defect_of_materializing_no_third_sink
    (tracedFeasibleAtomProjectionTerminalMaterializingNoThirdSinkOfCodeDefined L)

/-- Nonabsorbed raw-code terminal no-third-sink induces the older terminal
no-third-sink socket. -/
def tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeNonabsorbed
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n :=
  tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeDefined
    (tracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSinkOfCodeNonabsorbed L)

/-- Nonabsorbed raw-code terminal no-third-sink excludes terminal traced
feasible projection defects. -/
theorem no_terminal_traced_feasible_atom_projection_defect_of_code_nonabsorbed_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :=
  no_terminal_traced_feasible_atom_projection_defect_of_code_defined_no_third_sink
    (tracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSinkOfCodeNonabsorbed L)

/-- Active finite-descent hard gate using terminal raw-code no-third-sink and
positive repair lifts. -/
theorem not_not_nat_factorized_atom_pair_realization_of_active_code_terminal_repair_lift
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
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n Projection)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    (hActive : P.Active n k) :
    ¬¬ FactorizedAtomPairRealization
      NatMultiplicativelyAtomic
      natMultiplicativeAtomFactorizationCategory
      n k :=
  not_not_nat_factorized_atom_pair_realization_of_active_produced_demand_by_repair_lift
    P
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeDefined terminal)
    lift
    hActive

/-- Active defect exclusion with terminal raw-code no-third-sink and positive
repair lifts. -/
theorem no_traced_feasible_defect_of_active_code_terminal_repair_lift
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
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n Projection)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    (hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_defect_of_active_produced_demand_by_repair_lift
    P
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeDefined terminal)
    lift
    hActive

/-- Active finite-descent hard gate using nonabsorbed terminal raw-code
no-third-sink and positive repair lifts. -/
theorem not_not_nat_factorized_atom_pair_realization_of_active_code_nonabsorbed_terminal_repair_lift
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
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n Projection)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    (hActive : P.Active n k) :
    ¬¬ FactorizedAtomPairRealization
      NatMultiplicativelyAtomic
      natMultiplicativeAtomFactorizationCategory
      n k :=
  not_not_nat_factorized_atom_pair_realization_of_active_code_terminal_repair_lift
    P
    (tracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSinkOfCodeNonabsorbed
      terminal)
    lift
    hActive

/-- Active defect exclusion with nonabsorbed terminal raw-code no-third-sink
and positive repair lifts. -/
theorem no_traced_feasible_defect_of_active_code_nonabsorbed_terminal_repair_lift
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
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n Projection)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n)
    (hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_defect_of_active_code_terminal_repair_lift
    P
    (tracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSinkOfCodeNonabsorbed
      terminal)
    lift
    hActive

/-- Fully code-mediated active hard gate: terminal raw-code no-third-sink plus
global raw endpoint-code successor transport. -/
theorem not_not_nat_factorized_atom_pair_realization_of_active_code_terminal_code_mediated_repair_lift
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
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (T :
      CodeMediatedPairTransport
        NatMultiplicativelyAtomic SourceEvidence Residual n Projection)
    (hActive : P.Active n k) :
    ¬¬ FactorizedAtomPairRealization
      NatMultiplicativelyAtomic
      natMultiplicativeAtomFactorizationCategory
      n k :=
  not_not_nat_factorized_atom_pair_realization_of_active_code_mediated_repair_lift
    P
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeDefined terminal)
    source step_path trace_descent T hActive

/-- Fully code-mediated active hard gate with nonabsorbed terminal raw-code
no-third-sink. -/
theorem not_not_nat_factorized_atom_pair_realization_of_active_code_nonabsorbed_terminal_code_mediated_repair_lift
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
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (T :
      CodeMediatedPairTransport
        NatMultiplicativelyAtomic SourceEvidence Residual n Projection)
    (hActive : P.Active n k) :
    ¬¬ FactorizedAtomPairRealization
      NatMultiplicativelyAtomic
      natMultiplicativeAtomFactorizationCategory
      n k :=
  not_not_nat_factorized_atom_pair_realization_of_active_code_terminal_code_mediated_repair_lift
    P
    (tracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSinkOfCodeNonabsorbed
      terminal)
    source step_path trace_descent T hActive

/-- Defect exclusion for the fully code-mediated active hard gate. -/
theorem no_traced_feasible_defect_of_active_code_terminal_code_mediated_repair_lift
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
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (T :
      CodeMediatedPairTransport
        NatMultiplicativelyAtomic SourceEvidence Residual n Projection)
    (hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_defect_of_active_code_mediated_repair_lift
    P
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeDefined terminal)
    source step_path trace_descent T hActive

/-- Defect exclusion for the fully code-mediated active hard gate with
nonabsorbed terminal raw-code no-third-sink. -/
theorem no_traced_feasible_defect_of_active_code_nonabsorbed_terminal_code_mediated_repair_lift
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
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (T :
      CodeMediatedPairTransport
        NatMultiplicativelyAtomic SourceEvidence Residual n Projection)
    (hActive : P.Active n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_defect_of_active_code_terminal_code_mediated_repair_lift
    P
    (tracedFeasibleAtomProjectionTerminalCodeDefinedNoThirdSinkOfCodeNonabsorbed
      terminal)
    source step_path trace_descent T hActive


end RepresentationArithmeticAtomProjectionDefect
