import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime.Ledger

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

structure OriginalJointActuation : Prop where
  inputResource : type_of% actuation_input_is_parent
  inputNuclear : type_of% body_input_nuclear
  inputHeld : type_of% body_input_held
  inputRealized : type_of% body_input_realized
  clocks : type_of% clocks_endpoints
  elapsed : ∀ time, type_of% (clocks_elapsed time)
  forward : type_of% elapsed_strictly_forward
  resourceFlow : ∀ time, type_of% (resource_path_generated time)
  resourceEquation : ∀ time, type_of% (resource_equation time)
  electronEquation : ∀ time, type_of% (electronic_equation time)
  receiverEquation : ∀ time, type_of% (joint_receiver_equation time)
  clockEquation : ∀ time, type_of% (joint_clock_equation time)
  positionEquation : ∀ time i, type_of% (joint_position_equation time i)
  momentumEquation : ∀ time i, type_of% (joint_momentum_equation time i)
  trajectory : ∀ time i, type_of% (plateau_hamilton_equations time i)
  onForce : type_of% on_force_integral
  offForce : type_of% off_force_integral
  debit : type_of% receiver_target_debit
  balance : type_of% combined_target_energy
  positive : type_of% receiver_target_positive
  generated : ∀ i, type_of% (source_output_generated i)
  bodyClock : type_of% source_output_body_clock
  resourceClock : type_of% source_output_resource_clock
  residual : type_of% source_output_realization
  history : type_of% full_historical_account
  engine : type_of% original_engine_account
  nonzero : type_of% source_output_changes_body

theorem originalJointActuation : OriginalJointActuation :=
  ⟨actuation_input_is_parent,body_input_nuclear,body_input_held,body_input_realized,
    clocks_endpoints,clocks_elapsed,elapsed_strictly_forward,resource_path_generated,resource_equation,
    electronic_equation,joint_receiver_equation,joint_clock_equation,joint_position_equation,
    joint_momentum_equation,plateau_hamilton_equations,on_force_integral,off_force_integral,
    receiver_target_debit,combined_target_energy,receiver_target_positive,source_output_generated,
    source_output_body_clock,source_output_resource_clock,source_output_realization,
    full_historical_account,original_engine_account,source_output_changes_body⟩

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

def bodyFace (face : Reentry.Runtime.ReentryProjection) :=
  Reentry.Runtime.reentryRuntimeFacade.readoutAt bodyMaterial face

inductive Projection
  | current | next | clocks | history | energy | firstActuation | readiness | wholeLedger
  | parent (face : ControlRecovery.Runtime.Projection)
  | bodyParent (face : Reentry.Runtime.ReentryProjection)

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
    | .history => Reentry.Runtime.ReentryHistory × PLift (type_of% full_historical_account)
    | .energy => PLift (type_of% combined_target_energy ∧ type_of% original_engine_account)
    | .firstActuation => PLift OriginalJointActuation
    | .readiness => ActuationResult × PLift (nextCurrent current=current ∧ IsEmpty (BodyV.NativeWriteAt current))
    | .wholeLedger => SourceNativeLedgerEvolutionAt source occurrence
    | .parent face => (type_of% (parentFace face)) × PLift (type_of% (parent_face_factorizes face))
    | .bodyParent face => (type_of% (bodyFace face)) × PLift (type_of% (body_face_factorizes face))
  project := by
    intro projection current occurrence active
    cases projection with
    | current => exact currentResult current
    | next => exact currentResult (nextCurrent current)
    | clocks => exact (((currentResult current).resource.quantum.localClock,(currentResult current).bodyClock),
        ((currentResult (nextCurrent current)).resource.quantum.localClock,(currentResult (nextCurrent current)).bodyClock))
    | history => exact (Reentry.Runtime.reentrySourceHistory,⟨full_historical_account⟩)
    | energy => exact ⟨combined_target_energy,original_engine_account⟩
    | firstActuation => exact ⟨originalJointActuation⟩
    | readiness =>
        cases current with
        | ingress => exact nomatch active
        | ready result => exact (result,⟨rfl,ready_no_native result⟩)
    | wholeLedger => exact ledgerCompiler.compile occurrence
    | parent face => exact (parentFace face,⟨parent_face_factorizes face⟩)
    | bodyParent face => exact (bodyFace face,⟨body_face_factorizes face⟩)

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
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
