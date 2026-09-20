import H0mework.Arithmetic.SourceRepair.ActiveRepairLiftHardness
import H0mework.Arithmetic.ProjectionDefect.CodeMediatedBoundedTransport

/-!
# Code-mediated repair lift

This file derives positive atom-pair repair lifts from raw endpoint-code
successor projection.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Unbounded source/code-mediated successor transport.

For every realized atom pair, the source side supplies a source anchor whose
raw endpoint-code projection reads that pair, and a successor source one
residual step above it whose raw endpoint-code projection is atomically
certified.

This is intentionally global.  Supplying it is all-shell arithmetic strength,
not finite endpoint search and not a free source-side construction. -/
structure CodeMediatedPairTransport
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  sourceOfPair :
    ArithmeticAtomPair Atomic n -> SourceEvidence
  source_code_projects_pair :
    ∀ p : ArithmeticAtomPair Atomic n,
      Projection.codeProjection.projectCode (sourceOfPair p) =
        some (endpointCodePairOfAtomPair p)
  successorSource :
    ArithmeticAtomPair Atomic n -> SourceEvidence
  successor_step_to_source :
    ∀ p : ArithmeticAtomPair Atomic n,
      Residual.step (successorSource p) (sourceOfPair p)
  successorCode :
    ArithmeticAtomPair Atomic n -> EndpointCodePair n
  successor_code_projected :
    ∀ p : ArithmeticAtomPair Atomic n,
      Projection.codeProjection.projectCode (successorSource p) =
        some (successorCode p)

/-- A global code-mediated pair transport restricts to the existing bounded
transport interface at every bound. -/
def codeMediatedBoundedPairTransportOfGlobal
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (T :
      CodeMediatedPairTransport
        Atomic SourceEvidence Residual n Projection) :
    CodeMediatedBoundedPairTransport
      Atomic SourceEvidence Residual n bound Projection where
  sourceOfPair := fun p _hEnergy => T.sourceOfPair p
  source_code_projects_pair := fun p _hEnergy =>
    T.source_code_projects_pair p
  successorSource := fun p _hEnergy => T.successorSource p
  successor_step_to_source := fun p _hEnergy =>
    T.successor_step_to_source p
  successorCode := fun p _hEnergy => T.successorCode p
  successor_code_projected := fun p _hEnergy =>
    T.successor_code_projected p

/-- Code-mediated successor transport induces a global pair-level successor
transport. -/
def atomPairEnergySuccessorTransportOfCodeMediated
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (T :
      CodeMediatedPairTransport
        Atomic SourceEvidence Residual n Projection) :
    AtomPairEnergySuccessorTransport Atomic n where
  liftPair := fun p =>
    atomPairOfEndpointCodePair
      (T.successorCode p)
      (Projection.left_atomic (T.successor_code_projected p))
      (Projection.right_atomic (T.successor_code_projected p))
  energy_lift := by
    intro p
    have hqEnergy :
        ArithmeticAtomPair.energy
            (atomPairOfEndpointCodePair
              (T.successorCode p)
              (Projection.left_atomic (T.successor_code_projected p))
              (Projection.right_atomic (T.successor_code_projected p))) =
          Residual.residualEnergy (T.successorSource p) := by
      calc
        ArithmeticAtomPair.energy
            (atomPairOfEndpointCodePair
              (T.successorCode p)
              (Projection.left_atomic (T.successor_code_projected p))
              (Projection.right_atomic (T.successor_code_projected p))) =
            EndpointCodePair.energy (T.successorCode p) :=
              atomPairOfEndpointCodePair_energy
                (T.successorCode p)
                (Projection.left_atomic (T.successor_code_projected p))
                (Projection.right_atomic (T.successor_code_projected p))
        _ = Residual.residualEnergy (T.successorSource p) :=
              Projection.codeProjection.code_energy_faithful
                (T.successor_code_projected p)
    have hpEnergy :
        ArithmeticAtomPair.energy p =
          Residual.residualEnergy (T.sourceOfPair p) := by
      have hSourceEnergy :
          EndpointCodePair.energy (endpointCodePairOfAtomPair p) =
            Residual.residualEnergy (T.sourceOfPair p) :=
        Projection.codeProjection.code_energy_faithful
          (T.source_code_projects_pair p)
      calc
        ArithmeticAtomPair.energy p =
            EndpointCodePair.energy (endpointCodePairOfAtomPair p) := by
              rw [endpointCodePairOfAtomPair_energy]
        _ = Residual.residualEnergy (T.sourceOfPair p) :=
            hSourceEnergy
    have hStep :
        Residual.residualEnergy (T.sourceOfPair p) + 1 =
          Residual.residualEnergy (T.successorSource p) :=
      Residual.step_decreases_one (T.successor_step_to_source p)
    calc
      ArithmeticAtomPair.energy
          (atomPairOfEndpointCodePair
            (T.successorCode p)
            (Projection.left_atomic (T.successor_code_projected p))
            (Projection.right_atomic (T.successor_code_projected p))) =
          Residual.residualEnergy (T.successorSource p) := hqEnergy
      _ = Residual.residualEnergy (T.sourceOfPair p) + 1 := hStep.symm
      _ = ArithmeticAtomPair.energy p + 1 := by
          rw [← hpEnergy]

/-- Code-mediated successor transport gives the positive realization transport
lift used by gap-persistence arguments. -/
theorem atomPairRealizationTransportLiftOfCodeMediated
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (T :
      CodeMediatedPairTransport
        Atomic SourceEvidence Residual n Projection) :
    AtomPairRealizationTransportLift Atomic n :=
  atomPairRealizationTransportLiftOfPairTransport
    (atomPairEnergySuccessorTransportOfCodeMediated T)

/-- Code-mediated successor transport supplies every per-shell positive repair
lift. -/
theorem atomPairSuccessorRepairLiftOfCodeMediated
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (T :
      CodeMediatedPairTransport
        Atomic SourceEvidence Residual n Projection)
    (k : Nat) :
    AtomPairSuccessorRepairLift Atomic n k :=
  atomPairSuccessorRepairLiftOfRealizationTransportLift
    (atomPairRealizationTransportLiftOfCodeMediated T) k

/-- Source/trace descent plus global code-mediated successor transport gives
the traced positive repair-lift socket. -/
def tracedFeasibleAtomProjectionDefectRepairLiftOfCodeMediated
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
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
        Atomic SourceEvidence Residual n Projection) :
    TracedFeasibleAtomProjectionDefectRepairLift
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  source_descent := source
  step_path := step_path
  trace_descent := trace_descent
  realization_successor :=
    atomPairSuccessorRepairLiftOfCodeMediated T

/-- Active hard gate: a global Nat code-mediated successor transport plus
traced finite-descent/no-third-sink data gives double-negated factorized
realization at every active shell. -/
theorem not_not_nat_factorized_atom_pair_realization_of_active_code_mediated_repair_lift
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
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n)
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
  not_not_nat_factorized_atom_pair_realization_of_active_produced_demand_by_repair_lift
    P terminal
    (tracedFeasibleAtomProjectionDefectRepairLiftOfCodeMediated
      source step_path trace_descent T)
    hActive

/-- The same active code-mediated repair-lift data excludes traced feasible
defects at active shells. -/
theorem no_traced_feasible_defect_of_active_code_mediated_repair_lift
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
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n)
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
  no_traced_feasible_defect_of_active_produced_demand_by_repair_lift
    P terminal
    (tracedFeasibleAtomProjectionDefectRepairLiftOfCodeMediated
      source step_path trace_descent T)
    hActive


end RepresentationArithmeticAtomProjectionDefect
