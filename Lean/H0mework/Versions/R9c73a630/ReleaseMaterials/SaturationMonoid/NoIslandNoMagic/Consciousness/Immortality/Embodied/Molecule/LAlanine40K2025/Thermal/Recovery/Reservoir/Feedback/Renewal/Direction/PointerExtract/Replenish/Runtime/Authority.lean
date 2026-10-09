import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime.Ledger

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

structure OriginalReplenishment : Prop where
  inputActual : type_of% Replenish.source_exact
  inputClock : type_of% Replenish.origin_clock
  supplyClock : type_of% first_clock
  supplyAction : type_of% (respondNext_joint Replenish.origin)
  transferPositive : type_of% Gain.source_transfer_positive
  supplyPositive : type_of% first_pc_gain
  secondMaterial : type_of% second_material
  bothClocks : type_of% Account.clocks
  executionAction : type_of% Account.execution_joint
  actualGain : type_of% Gain.net_gain_positive
  debit : type_of% Account.full_historical_debit
  energy : type_of% Account.full_historical_account
  balance : type_of% Account.execution_balance
  remaining : type_of% Account.original_debit_strict
  memory : type_of% Account.execution_memory
  receiver : type_of% Account.receiver_empty
  changed : type_of% Account.output_joint_changed
  oldLoadDifferent : type_of% first_not_old_load

theorem originalReplenishment : OriginalReplenishment :=
  ⟨Replenish.source_exact,Replenish.origin_clock,first_clock,respondNext_joint Replenish.origin,
    Gain.source_transfer_positive,first_pc_gain,second_material,Account.clocks,Account.execution_joint,
    Gain.net_gain_positive,Account.full_historical_debit,Account.full_historical_account,
    Account.execution_balance,Account.original_debit_strict,Account.execution_memory,
    Account.receiver_empty,Account.output_joint_changed,first_not_old_load⟩

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

def restructuringSource : SourceNativeRestructuringLedgerSource RecoveryN ReplenishV where
  source := source
  compiler := restructuringCompiler

inductive Projection
  | current | next | joint | resources | receiver | thermal | netAccount
  | parent (face : Restore.Runtime.Projection) | firstSupply | wholeLedger

def resourceRead (current : ReplenishCurrent) : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) × ℝ :=
  (values (currentMaterial current).quantum,
    (donorRemainingOf (loadBlock (currentMaterial current).quantum),
      donorRemainingOf (suppliedBlock (currentMaterial current).quantum)),
    donorRemainingOf (historicalSupply current))

def projectionLaw : SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .firstSupply => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .firstSupply => match current with | .ingress => PEmpty | .running _ => PUnit
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
    | .receiver => (ℝ × ℝ) × (ℝ × ℝ) × PLift (type_of% (next_receiver current) ∧ type_of% (receiver_energy_next current))
    | .thermal => PLift (type_of% (Live.thermalJoint_generated (currentMaterial (nextCurrent current)).quantum) ∧
        type_of% (Live.entropyProduction_disposition (currentMaterial (nextCurrent current)).quantum))
    | .netAccount => (ℝ × ℝ × ℝ) × PLift (type_of% (next_net_account current))
    | .parent face => (type_of% (parentFace face)) ×
        PLift (type_of% (parent_face_factorizes face) ∧ type_of% origin_is_parent)
    | .firstSupply => PLift OriginalReplenishment
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
        (receiverEnergy current,receiverEnergy (nextCurrent current)),⟨next_receiver current,receiver_energy_next current⟩)
    | .thermal => ⟨Live.thermalJoint_generated _,Live.entropyProduction_disposition _⟩
    | .netAccount => ((eventWork current,accumulatedWork current,accumulatedTransfer current),⟨next_net_account current⟩)
    | .parent face => (parentFace face,⟨parent_face_factorizes face,origin_is_parent⟩)
    | .firstSupply => ⟨originalReplenishment⟩
    | .wholeLedger => ledgerCompiler.compile occurrence
def authoritySource : SourceNativeAuthoritySource RecoveryN ReplenishV where
  restructuringSource := restructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal restructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN ReplenishV where
  source := authoritySource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure RecoveryN ReplenishV :=
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
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
