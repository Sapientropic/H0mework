import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime.Ledger

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

structure OriginalControlExtraction : Prop where
  inputActual : type_of% ControlRecovery.source_exact
  inputClock : type_of% ControlRecovery.origin_clock
  inputZero : type_of% Receiver.source_zero
  coupledAction : type_of% (Receiver.pulse_is_coupled_flow (nativeClockStep : ℝ))
  actualJoint : type_of% (Receiver.next_joint ControlRecovery.origin)
  onForce : type_of% (Receiver.on_force_integral ControlRecovery.material)
  offForce : type_of% (Receiver.off_force_integral ControlRecovery.material)
  firstClock : type_of% first_clock
  secondClock : type_of% second_clock
  actualGain : type_of% Receiver.output_kinetic
  baseline : type_of% Receiver.source_energy_conserved
  energy : type_of% Receiver.full_historical_account
  debit : type_of% Receiver.full_historical_debit
  remaining : type_of% Receiver.output_remaining
  memory : type_of% Receiver.output_memory
  environment : type_of% Receiver.output_environment
  changed : type_of% Receiver.output_changed
  oldLoadDifferent : type_of% first_not_old_load

theorem originalControlExtraction : OriginalControlExtraction :=
  ⟨ControlRecovery.source_exact,ControlRecovery.origin_clock,Receiver.source_zero,
    Receiver.pulse_is_coupled_flow _,Receiver.next_joint _,Receiver.on_force_integral _,
    Receiver.off_force_integral _,first_clock,second_clock,Receiver.output_kinetic,
    Receiver.source_energy_conserved,Receiver.full_historical_account,Receiver.full_historical_debit,
    Receiver.output_remaining,Receiver.output_memory,Receiver.output_environment,
    Receiver.output_changed,first_not_old_load⟩

private def restructuringLaw : SourceNativeLedgerRestructuringLaw source :=
  identityOnlyWorldLedgerRestructuringLaw source LAlanine40K2025.Source.key (by
    intro support responsibility
    refine ⟨fun left right => ?_⟩
    have same : (⟨responsibility, left⟩ : OpenResponsibilityAt RecoveryN support) =
        ⟨responsibility, right⟩ :=
      (recoveryEntry_unique _ _).trans (recoveryEntry_unique _ _).symm
    exact eq_of_heq (Sigma.mk.inj same).2)

private def restructuringCompiler : SourceNativeRestructuringLedgerCompiler source where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)

def restructuringSource : SourceNativeRestructuringLedgerSource RecoveryN ControlV where
  source := source
  compiler := restructuringCompiler

inductive Projection
  | current | next | joint | resources | receiver | thermal | netAccount
  | parent (face : Replenish.Runtime.Projection) | firstControl | wholeLedger

def resourceRead (current : ControlCurrent) : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) × ℝ :=
  (values (currentMaterial current).quantum,
    (donorRemainingOf (loadBlock (currentMaterial current).quantum),
      donorRemainingOf (suppliedBlock (currentMaterial current).quantum)),
    donorRemainingOf (historicalSupply current))

def projectionLaw : SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .firstControl => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .firstControl => match current with | .ingress => PEmpty | .running _ => PUnit
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    cases current with
    | ingress => exact .inl PUnit.unit
    | running _ => exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .current | .next => Material
    | .joint => PointerJoint × PointerJoint × PLift (type_of% (next_joint current))
    | .resources => (type_of% (resourceRead current)) × (type_of% (resourceRead (nextCurrent current))) ×
        (ℝ × ℝ) × PLift (type_of% (next_resource_balance current) ∧ type_of% (next_remaining current) ∧
          type_of% (next_memory current) ∧ type_of% (next_donor current))
    | .receiver => (ℝ × ℝ) × (ℝ × ℝ) × PLift (type_of% (next_baseline_account current) ∧ type_of% (next_clock current))
    | .thermal => PLift (type_of% (Live.thermalJoint_generated (currentMaterial (nextCurrent current)).quantum) ∧
        type_of% (Live.entropyProduction_disposition (currentMaterial (nextCurrent current)).quantum))
    | .netAccount => (ℝ × ℝ × ℝ) × PLift (type_of% (next_net_account current))
    | .parent face => (type_of% (parentFace face)) ×
        PLift (type_of% (parent_face_factorizes face) ∧ type_of% origin_is_parent)
    | .firstControl => PLift OriginalControlExtraction
    | .wholeLedger => SourceNativeLedgerEvolutionAt source occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => currentMaterial current
    | .next => currentMaterial (nextCurrent current)
    | .joint => ((currentMaterial current).quantum.joint,(currentMaterial (nextCurrent current)).quantum.joint,⟨next_joint current⟩)
    | .resources => (resourceRead current,resourceRead (nextCurrent current),
        (decodedMemory current,decodedMemory (nextCurrent current)),
        ⟨next_resource_balance current,next_remaining current,next_memory current,next_donor current⟩)
    | .receiver => (((currentMaterial current).momentum,(currentMaterial (nextCurrent current)).momentum),
        (receiverEnergy current,receiverEnergy (nextCurrent current)),⟨next_baseline_account current,next_clock current⟩)
    | .thermal => ⟨Live.thermalJoint_generated _,Live.entropyProduction_disposition _⟩
    | .netAccount => ((Live.freeEnergy (currentMaterial (nextCurrent current)).quantum-Live.freeEnergy (currentMaterial current).quantum,
        Live.entropyProduction (currentMaterial (nextCurrent current)).quantum-Live.entropyProduction (currentMaterial current).quantum,
        receiverEnergy (nextCurrent current)-receiverEnergy current),⟨next_net_account current⟩)
    | .parent face => (parentFace face,⟨parent_face_factorizes face,origin_is_parent⟩)
    | .firstControl => ⟨originalControlExtraction⟩
    | .wholeLedger => ledgerCompiler.compile occurrence
def authoritySource : SourceNativeAuthoritySource RecoveryN ControlV where
  restructuringSource := restructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal restructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN ControlV where
  source := authoritySource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure RecoveryN ControlV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def initialVisit : SourceNativeTemporalVisitAt livingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite livingRoot.toAuthoritativeRoot.toRoot.initialVisit

def initialGenerated :=
  livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit initialVisit

def initialEntry := recoveryEntry reservoirSupport

def initialEntryRow : initialGenerated.GeneratedEntryRowAt initialEntry :=
  (initialGenerated.canonicalGeneratedEntryRow? initialEntry).get (by rfl)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    initialGenerated.occurrence initialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? initialGenerated.wholeLedgerWriteBack).get
    (by rfl)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
