import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime.Ledger
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Integrals
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Capacity

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
noncomputable section

structure ActualStep (current : State) : Prop where
  forward : type_of% FiniteActuation.duration_positive
  clocks : type_of% (next_clocks current.1)
  clockJoins : type_of% FiniteActuation.clock_junctions
  stateJoins : type_of% (state_junctions current.1)
  hamiltonianJoins : type_of% (hamiltonian_junctions current.1)
  quantumEquation : type_of% (quantum_equation current.1)
  gammaEquation : type_of% (gamma_equation current.1)
  positionEquation : type_of% (position_equation current.1)
  momentumEquation : type_of% (momentum_equation current.1)
  receiverEquation : type_of% (receiver_equation current.1)
  jointClock : type_of% (joint_clock_partial current.1 current.2)
  jointReceiver : type_of% (joint_receiver_partial current.1 current.2)
  jointForce : type_of% (joint_nuclear_force current.1)
  jointVelocity : type_of% (joint_nuclear_velocity current.1)
  positiveThroughout : type_of% (receiver_positive current.1 current.2)
  phaseEnergy : type_of% (phase_energy_account current.1 current.2)
  positionIntegral : type_of% (position_integral current.1)
  momentumIntegral : type_of% (momentum_integral current.1)
  receiverIntegral : type_of% (receiver_integral current.1)
  quantumIntegral : type_of% (quantum_integral current.1)
  gammaIntegral : type_of% (gamma_integral current.1)
  momentumUpdate : type_of% (total_momentum_update current.1 current.2)
  receiverUpdate : type_of% (total_receiver_update current.1 current.2)
  sourceEndpoints : type_of% (source_endpoints current.1 current.2)
  targetEndpoints : type_of% (target_endpoints current.1 current.2)
  kinetic : type_of% (next_kinetic_generated current.1 current.2)
  positiveDebit : type_of% (positive_debit_below_reserve current.1 current.2)
  remainingStock : type_of% (next_stock current.1 current.2)
  generatedReserve : type_of% (next_reserve current.1 current.2)
  unreservedIncrease : type_of% (next_unreserved_increases current.1 current.2)
  energy : type_of% (next_mechanical_account current.1 current.2)
  entropy : type_of% (next_whole_account current.1 current.2)
  residualFlow : type_of% (gamma_residual_retained current.1 current.2)
  nextInvariant : Admissible (nextMaterial current.1)
  actualChange : type_of% (next_changes_momentum current.1 current.2)

theorem actualStep (current : State) : ActualStep current :=
  ⟨FiniteActuation.duration_positive,next_clocks current.1,FiniteActuation.clock_junctions,
    state_junctions current.1,hamiltonian_junctions current.1,quantum_equation current.1,
    gamma_equation current.1,position_equation current.1,momentum_equation current.1,
    receiver_equation current.1,joint_clock_partial current.1 current.2,
    joint_receiver_partial current.1 current.2,joint_nuclear_force current.1,joint_nuclear_velocity current.1,
    receiver_positive current.1 current.2,phase_energy_account current.1 current.2,
    position_integral current.1,momentum_integral current.1,receiver_integral current.1,
    quantum_integral current.1,gamma_integral current.1,total_momentum_update current.1 current.2,
    total_receiver_update current.1 current.2,source_endpoints current.1 current.2,
    target_endpoints current.1 current.2,next_kinetic_generated current.1 current.2,
    positive_debit_below_reserve current.1 current.2,next_stock current.1 current.2,
    next_reserve current.1 current.2,next_unreserved_increases current.1 current.2,
    next_mechanical_account current.1 current.2,next_whole_account current.1 current.2,
    gamma_residual_retained current.1 current.2,next_admissible current.1 current.2,
    next_changes_momentum current.1 current.2⟩

private def restructuringLaw : SourceNativeLedgerRestructuringLaw source :=
  identityOnlyWorldLedgerRestructuringLaw source LAlanine40K2025.Source.key (by
    intro support responsibility
    refine ⟨fun left right => ?_⟩
    have same : (⟨responsibility,left⟩ : OpenResponsibilityAt RecoveryN support)=⟨responsibility,right⟩ :=
      (recoveryEntry_unique _ _).trans (recoveryEntry_unique _ _).symm
    exact eq_of_heq (Sigma.mk.inj same).2)

private def restructuringCompiler : SourceNativeRestructuringLedgerCompiler source where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := by
    intro current occurrence
    exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)
      (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)

def restructuringSource : SourceNativeRestructuringLedgerSource RecoveryN BodyV where
  source := source
  compiler := restructuringCompiler

inductive Projection
  | current | next | clocks | actuation | account | capacity | realization | wholeLedger
  | parent (face : FiniteActuation.Runtime.Projection)

def projectionLaw : SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .current | .next => Material
    | .clocks => (ℚ × ℚ) × (ℚ × ℚ)
    | .actuation => PLift (ActualStep current)
    | .account => PLift (type_of% (next_whole_account current.1 current.2))
    | .capacity => (ℚ × ℝ) × PLift (type_of% (next_unreserved_increases current.1 current.2))
    | .realization => PLift (type_of% (gamma_residual_retained current.1 current.2))
    | .wholeLedger => SourceNativeLedgerEvolutionAt source occurrence
    | .parent face => (type_of% (parentFace face)) × PLift (type_of% (parent_face_factorizes face))
  project := by
    intro projection current occurrence active
    cases projection with
    | current => exact current.1
    | next => exact (nextState current).1
    | clocks => exact (((current.1.body.resource.quantum.localClock,current.1.body.bodyClock),
        ((nextState current).1.body.resource.quantum.localClock,(nextState current).1.body.bodyClock)))
    | actuation => exact ⟨actualStep current⟩
    | account => exact ⟨next_whole_account current.1 current.2⟩
    | capacity => exact ((current.1.reserve,current.1.body.resource.momentum),⟨next_unreserved_increases current.1 current.2⟩)
    | realization => exact ⟨gamma_residual_retained current.1 current.2⟩
    | wholeLedger => exact ledgerCompiler.compile occurrence
    | parent face => exact (parentFace face,⟨parent_face_factorizes face⟩)

def authoritySource : SourceNativeAuthoritySource RecoveryN BodyV where
  restructuringSource := restructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal restructuringSource (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN BodyV where
  source := authoritySource
  emitted := emitted
  compiler_commutes := by intro current; rfl

def livingRoot : SourceNativeLivingRootClosure RecoveryN BodyV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def initialVisit : SourceNativeTemporalVisitAt livingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite livingRoot.toAuthoritativeRoot.toRoot.initialVisit

def initialGenerated := livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit initialVisit

def initialEntry := recoveryEntry reservoirSupport

def initialEntryRow : initialGenerated.GeneratedEntryRowAt initialEntry :=
  (initialGenerated.canonicalGeneratedEntryRow? initialEntry).get (by rfl)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    initialGenerated.occurrence initialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? initialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
