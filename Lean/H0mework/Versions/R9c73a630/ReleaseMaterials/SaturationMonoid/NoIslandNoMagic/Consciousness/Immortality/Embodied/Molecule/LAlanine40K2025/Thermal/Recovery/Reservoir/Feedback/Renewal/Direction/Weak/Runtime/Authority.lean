import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Runtime.Ledger

/-! Fixed weak-supply authority carries every original nine-q face and generates the new action. -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Resource Propagation.Producer
noncomputable section

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

def restructuringSource : SourceNativeRestructuringLedgerSource RecoveryN WeakV where
  source := source
  compiler := restructuringCompiler

inductive Projection
  | current | next | joint | resources | thermal | netAccount | parent (face : SharpNet.Runtime.Face) | firstSupply | wholeLedger

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
    | .current | .next => Live.State
    | .joint => PointerJoint × PointerJoint × PLift (type_of% (next_joint current))
    | .resources => (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) ×
        PLift (type_of% (remaining_range (currentState current)) ∧
          type_of% (remaining_range (currentState (nextCurrent current))) ∧
          type_of% (next_resource_balance current) ∧ type_of% (next_remaining current))
    | .thermal => PLift (type_of% (Live.thermalJoint_generated (currentState (nextCurrent current))) ∧
        type_of% (Live.entropyProduction_disposition (currentState (nextCurrent current))))
    | .netAccount => (ℝ × ℝ × ℝ) × PLift (type_of% (next_net_account current))
    | .parent face => (type_of% (parentFace face)) ×
        PLift (type_of% (parent_face_factorizes face) ∧ type_of% origin_is_parent)
    | .firstSupply => PLift WeakSupplyAndLoadCandidate
    | .wholeLedger => SourceNativeLedgerEvolutionAt source occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => currentState current
    | .next => currentState (nextCurrent current)
    | .joint => ((currentState current).joint, (currentState (nextCurrent current)).joint,
        ⟨next_joint current⟩)
    | .resources => (values (currentState current), values (currentState (nextCurrent current)),
        (donorRemainingOf (suppliedBlock (currentState current)),
          donorRemainingOf (suppliedBlock (currentState (nextCurrent current)))),
        ⟨remaining_range _, remaining_range _, next_resource_balance current, next_remaining current⟩)
    | .thermal => ⟨Live.thermalJoint_generated _, Live.entropyProduction_disposition _⟩
    | .netAccount => ((eventWork current, accumulatedWork current, accumulatedTransfer current),
        ⟨next_net_account current⟩)
    | .parent face => (parentFace face, ⟨parent_face_factorizes face,origin_is_parent⟩)
    | .firstSupply => ⟨sourceGeneratedWeakSupplyAndLoad⟩
    | .wholeLedger => ledgerCompiler.compile occurrence

def authoritySource : SourceNativeAuthoritySource RecoveryN WeakV where
  restructuringSource := restructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal restructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN WeakV where
  source := authoritySource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure RecoveryN WeakV :=
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
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
