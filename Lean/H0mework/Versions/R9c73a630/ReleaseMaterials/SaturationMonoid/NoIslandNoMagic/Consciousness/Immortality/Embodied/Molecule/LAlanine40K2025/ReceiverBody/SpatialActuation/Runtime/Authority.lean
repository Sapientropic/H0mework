import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Runtime.Ledger
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Action

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

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
  | current | next | clocks | history | energy | firstActuation | readiness | wholeLedger | spatial
  | parent (face : SIWork.Runtime.Face)

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
    | .spatial => ActuationResult × ((BasinRefinement.SourceFiniteData.Basis → List BasinRefinement.SourceGaussianModel.Term) ×
        (BasinRefinement.SourceGaussianModel.Point → BasinRefinement.SourceGaussianModel.Point → ℂ))
    | .clocks => (ℚ × ℚ) × (ℚ × ℚ)
    | .history => FiniteContinuation.Material × PLift (type_of% generated_history_joule)
    | .energy => PLift (type_of% generated_account ∧ type_of% generated_engine_residual)
    | .firstActuation => PLift OriginalSpatialAction
    | .readiness => ActuationResult × PLift (nextCurrent current=current ∧ IsEmpty (BodyV.NativeWriteAt current))
    | .wholeLedger => SourceNativeLedgerEvolutionAt source occurrence
    | .parent face => (type_of% (parentFace face)) × PLift (type_of% (parent_face_factorizes face))
  project := by
    intro projection current occurrence active
    cases projection with
    | spatial => exact (currentResult current,termsAt (currentResult current),gammaAt (currentResult current))
    | current => exact currentResult current
    | next => exact currentResult (nextCurrent current)
    | clocks => exact (((currentResult current).resource.quantum.localClock,(currentResult current).bodyClock),
        ((currentResult (nextCurrent current)).resource.quantum.localClock,(currentResult (nextCurrent current)).bodyClock))
    | history => exact (SpatialActuation.input,⟨generated_history_joule⟩)
    | energy => exact ⟨generated_account,generated_engine_residual⟩
    | firstActuation => exact ⟨originalSpatialAction⟩
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
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Runtime
