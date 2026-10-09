import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime.Ledger
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.History

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

structure OriginalFiniteActuation : Prop where
  input : type_of% input_is_parent
  forward : type_of% duration_positive
  clocks : type_of% generated_clocks
  physicalClocks : ∀ phase time, type_of% (physical_clocks phase time)
  clockJoins : type_of% clock_junctions
  stateJoins : type_of% state_junctions
  hamiltonianJoins : type_of% hamiltonian_junctions
  quantumEquation : type_of% quantum_equation
  gammaEquation : type_of% gamma_equation
  positionEquation : type_of% position_equation
  momentumEquation : type_of% momentum_equation
  receiverEquation : type_of% receiver_equation
  jointClock : type_of% joint_clock_partial
  jointReceiver : type_of% joint_receiver_partial
  jointForce : type_of% joint_nuclear_force
  jointVelocity : type_of% joint_nuclear_velocity
  positiveThroughout : type_of% receiver_positive
  phaseEnergy : type_of% phase_energy_account
  positionIntegral : type_of% position_integral
  momentumIntegral : type_of% momentum_integral
  receiverIntegral : type_of% receiver_integral
  quantumIntegral : type_of% quantum_integral
  gammaIntegral : type_of% gamma_integral
  momentumUpdate : type_of% total_momentum_update
  receiverUpdate : type_of% total_receiver_update
  sourceEndpoints : type_of% source_endpoints
  targetEndpoints : type_of% target_endpoints
  kinetic : type_of% target_kinetic_generated
  positiveDebit : type_of% target_debit_positive_and_bounded
  remainingStock : type_of% target_stock
  energy : type_of% target_resource_account
  entropy : type_of% target_free_energy_entropy_account
  history : type_of% complete_historical_account
  engine : type_of% complete_engine_account
  residualFlow : type_of% electron_residual_retained
  residualTarget : type_of% target_retains_residual
  retainedConfiguration : type_of% target_configuration_preserved
  actualChange : type_of% target_momentum_changed

theorem originalFiniteActuation : OriginalFiniteActuation :=
  ⟨input_is_parent,duration_positive,generated_clocks,physical_clocks,clock_junctions,state_junctions,
    hamiltonian_junctions,quantum_equation,gamma_equation,position_equation,momentum_equation,
    receiver_equation,joint_clock_partial,joint_receiver_partial,joint_nuclear_force,joint_nuclear_velocity,
    receiver_positive,phase_energy_account,position_integral,momentum_integral,receiver_integral,
    quantum_integral,gamma_integral,total_momentum_update,total_receiver_update,source_endpoints,
    target_endpoints,target_kinetic_generated,target_debit_positive_and_bounded,target_stock,
    target_resource_account,target_free_energy_entropy_account,complete_historical_account,
    complete_engine_account,electron_residual_retained,target_retains_residual,target_configuration_preserved,
    target_momentum_changed⟩

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
    cases current <;> exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)
      (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)

def restructuringSource : SourceNativeRestructuringLedgerSource RecoveryN BodyV where
  source := source
  compiler := restructuringCompiler

inductive Projection
  | current | next | clocks | history | energy | firstActuation | readiness | wholeLedger
  | parent (face : Coulomb.Runtime.Face)

def projectionLaw : SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun projection {current} _ => match projection with
    | .firstActuation => match current with | .ingress => PUnit | .ready _ => PEmpty
    | .readiness => match current with | .ingress => PEmpty | .ready _ => PUnit
    | _ => PUnit
  InactiveAt := fun projection {current} _ => match projection with
    | .firstActuation => match current with | .ingress => PEmpty | .ready _ => PUnit
    | .readiness => match current with | .ingress => PUnit | .ready _ => PEmpty
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    all_goals cases current <;> first | exact .inl PUnit.unit | exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .current | .next => ActuationResult
    | .clocks => (ℚ × ℚ) × (ℚ × ℚ)
    | .history => Coulomb.Material × PLift (type_of% complete_historical_account)
    | .energy => PLift (type_of% target_resource_account ∧ type_of% complete_engine_account)
    | .firstActuation => PLift OriginalFiniteActuation
    | .readiness => ActuationResult × PLift (nextCurrent current=current ∧ IsEmpty (BodyV.NativeWriteAt current))
    | .wholeLedger => SourceNativeLedgerEvolutionAt source occurrence
    | .parent face => (type_of% (parentFace face)) × PLift (type_of% (parent_face_factorizes face))
  project := by
    intro projection current occurrence active
    cases projection with
    | current => exact currentResult current
    | next => exact currentResult (nextCurrent current)
    | clocks => exact (((currentResult current).resource.quantum.localClock,(currentResult current).bodyClock),
        ((currentResult (nextCurrent current)).resource.quantum.localClock,(currentResult (nextCurrent current)).bodyClock))
    | history => exact (FiniteActuation.input,⟨complete_historical_account⟩)
    | energy => exact ⟨target_resource_account,complete_engine_account⟩
    | firstActuation => exact ⟨originalFiniteActuation⟩
    | readiness =>
        cases current with
        | ingress => exact nomatch active
        | ready result => exact (result,⟨rfl,ready_no_native result⟩)
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
  compiler_commutes := by intro current; cases current <;> rfl

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
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
