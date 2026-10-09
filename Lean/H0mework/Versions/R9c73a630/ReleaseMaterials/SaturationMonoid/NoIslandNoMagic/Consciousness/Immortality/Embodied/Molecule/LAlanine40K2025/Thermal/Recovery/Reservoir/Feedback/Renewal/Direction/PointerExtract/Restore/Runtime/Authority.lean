import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime.Ledger

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

structure OriginalPayment : Prop where
  inputActual : type_of% input_actual
  control : type_of% coupled_hermitian
  flow : type_of% pulse_at_clock
  inputPositive : type_of% input_positive
  launch : type_of% launch_lower
  onForce : type_of% on_force
  offForce : type_of% off_force
  onPath : type_of% on_positive
  offPath : type_of% off_nonnegative
  demand : type_of% positive_demand
  emptied : type_of% output_momentum
  energy : type_of% paid_energy
  pointerPayment : type_of% pointer_recharged
  body : type_of% output_body
  branches : type_of% output_branches
  restoration : type_of% output_joint
  changed : type_of% actual_change
  netAccount : type_of% paid_net_account
  clock : type_of% output_clock

theorem originalPayment : OriginalPayment :=
  ⟨input_actual,coupled_hermitian,pulse_at_clock,input_positive,launch_lower,on_force,off_force,
    on_positive,off_nonnegative,positive_demand,output_momentum,paid_energy,pointer_recharged,
    output_body,output_branches,output_joint,actual_change,paid_net_account,output_clock⟩
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

def restructuringSource : SourceNativeRestructuringLedgerSource RecoveryN PaymentV where
  source := source
  compiler := restructuringCompiler

inductive Projection
  | current | next | joint | resources | receiver | thermal | netAccount
  | parent (face : PointerExtract.Runtime.Projection) | firstPayment | wholeLedger

def resourceRead (current : PaymentCurrent) : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) × ℝ :=
  (values (currentMaterial current).quantum,
    (donorRemainingOf (loadBlock (currentMaterial current).quantum),
      donorRemainingOf (suppliedBlock (currentMaterial current).quantum)),
    donorRemainingOf (historicalSupply current))

def projectionLaw : SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .firstPayment => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .firstPayment => match current with | .ingress => PEmpty | .running _ => PUnit
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
    | .receiver => (ℝ × ℝ) × (ℝ × ℝ) × PLift (type_of% (next_energy current))
    | .thermal => PLift (type_of% (Live.thermalJoint_generated (currentMaterial (nextCurrent current)).quantum) ∧
        type_of% (Live.entropyProduction_disposition (currentMaterial (nextCurrent current)).quantum))
    | .netAccount => PLift (type_of% (next_net_account current))
    | .parent face => (type_of% (parentFace face)) ×
        PLift (type_of% (parent_face_factorizes face) ∧ type_of% origin_is_parent)
    | .firstPayment => PLift OriginalPayment
    | .wholeLedger => SourceNativeLedgerEvolutionAt source occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => currentMaterial current
    | .next => currentMaterial (nextCurrent current)
    | .joint => ((currentMaterial current).quantum.joint,(currentMaterial (nextCurrent current)).quantum.joint,⟨next_joint current⟩)
    | .resources => (resourceRead current,resourceRead (nextCurrent current),
        (decodedMemory current,decodedMemory (nextCurrent current)),
        ⟨next_resource_balance current,next_remaining current,next_memory current,next_donor current⟩)
    | .receiver => ((receiverEnergy current,receiverEnergy (nextCurrent current)),
        (pointerEnergy (currentMaterial current).quantum.joint,pointerEnergy (currentMaterial (nextCurrent current)).quantum.joint),
        ⟨next_energy current⟩)
    | .thermal => ⟨Live.thermalJoint_generated _,Live.entropyProduction_disposition _⟩
    | .netAccount => ⟨next_net_account current⟩
    | .parent face => (parentFace face,⟨parent_face_factorizes face,origin_is_parent⟩)
    | .firstPayment => ⟨originalPayment⟩
    | .wholeLedger => ledgerCompiler.compile occurrence
def authoritySource : SourceNativeAuthoritySource RecoveryN PaymentV where
  restructuringSource := restructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal restructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN PaymentV where
  source := authoritySource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure RecoveryN PaymentV :=
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
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Restore.Runtime
