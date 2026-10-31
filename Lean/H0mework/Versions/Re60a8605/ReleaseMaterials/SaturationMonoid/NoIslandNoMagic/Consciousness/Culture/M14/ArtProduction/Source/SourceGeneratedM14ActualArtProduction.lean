import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface.SourceNativeM14ArtProductionCoordinates

/-!
# Source-generated actual M14 art production

This is a responsibility-lifecycle producer, not a renamed communication
delivery.  One exact platform material-action source admits the raw M12
object, and one private `ProgressAt` receipt consumes that source occurrence
to change its residual from the coarse context to the refined work context.
The dependent process run generates the trace and write-back.

The same material action supplies the generated next.  No paid-root next,
target work, trace, or write-back is accepted at the producer mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ArtProduction
namespace Source

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ComplementObservation
open ProcessGame.Society.M14EssentialAccessRelationFixture
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle
open ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual
open ProcessGame.Society.M14SourceGeneratedPlatformGateRenewedActualService
open ProcessGame.Society.M14ProofCarryingPlatformGateFullAdmission
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface

noncomputable section

/-! ## Exact source-indexed receipts -/

inductive M14ArtProductionAcceptedTaskAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary ->
      M12AestheticObjectReadout -> Type
  | private generated : M14ArtProductionAcceptedTaskAt oldVisit sourceIndex
      boundary
      (sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary)
      (sourceObjectRead m14ArtProductionRawOccurrence)

inductive M14ArtProductionAdmissionAuthorityAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary ->
      Unit -> Type
  | private generated : M14ArtProductionAdmissionAuthorityAt oldVisit
      sourceIndex boundary
      (sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary)
      ()

inductive M14ArtProductionBearerAcceptanceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Lifecycle.ActorBearer ->
      SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary ->
      Unit -> Type
  | private generated : M14ArtProductionBearerAcceptanceAt oldVisit
      sourceIndex boundary
      (sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary
        ).materialService.materialBearer
      (sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary)
      ()

/-- Genuine progress receipt.  Its only constructor is indexed by the exact
material-action source, raw M12 object, coarse input, and refined output. -/
inductive M14ArtProductionProgressAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary ->
      M12AestheticObjectReadout ->
      SourceGeneratedM12AestheticContextOccurrence ->
      SourceGeneratedM12AestheticContextOccurrence -> Type
  | private generated : M14ArtProductionProgressAt oldVisit sourceIndex
      boundary
      (sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary)
      (sourceObjectRead m14ArtProductionRawOccurrence)
      m14ArtProductionRawOccurrence m14ArtProductionWorkOccurrence

def m14ArtProductionAcceptedTask
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (source : SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
      boundary) :
    M14ArtProductionAcceptedTaskAt oldVisit sourceIndex boundary source
      (sourceObjectRead m14ArtProductionRawOccurrence) := by
  cases source
  exact .generated

def m14ArtProductionAdmissionAuthority
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (source : SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
      boundary) :
    M14ArtProductionAdmissionAuthorityAt oldVisit sourceIndex boundary source
      () := by
  cases source
  exact .generated

def m14ArtProductionBearerAcceptance
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (source : SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
      boundary) :
    M14ArtProductionBearerAcceptanceAt oldVisit sourceIndex boundary
      source.materialService.materialBearer source () := by
  cases source
  exact .generated

def m14ArtProductionProgress
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (source : SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
      boundary) :
    M14ArtProductionProgressAt oldVisit sourceIndex boundary source
      (sourceObjectRead m14ArtProductionRawOccurrence)
      m14ArtProductionRawOccurrence m14ArtProductionWorkOccurrence := by
  cases source
  exact .generated

theorem m14ArtProductionProgress_endpoints_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {source : SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
      boundary}
    {object : M12AestheticObjectReadout}
    {input output : SourceGeneratedM12AestheticContextOccurrence}
    (progress : M14ArtProductionProgressAt oldVisit sourceIndex boundary
      source object input output) :
    source = sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
        boundary ∧
      object = sourceObjectRead m14ArtProductionRawOccurrence ∧
      input = m14ArtProductionRawOccurrence ∧
      output = m14ArtProductionWorkOccurrence := by
  cases progress
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Actual production vocabulary and process -/

def m14ArtProductionVocabularyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ResponsibilityLifecycle.Vocabulary where
  SourceEvent :=
    SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary
  Content := M12AestheticObjectReadout
  Residual := SourceGeneratedM12AestheticContextOccurrence
  Bearer := Lifecycle.ActorBearer
  ProtectedInterest := essentialAccessRelationCompiler.Actor
  Scope := Unit
  Lineage := essentialAccessRelationCompiler.ExactRelationSeed
  Incidence := Nat
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun _source => MinimalRegistrableSourceAnchor.canonical ()
    (platformGateMaterialSeedAt boundary)
  sourceIncidence := fun _source => m14ArtProductionDepthAt boundary
  ObstructionAt := fun _source => PEmpty
  demandContent := fun obstruction => nomatch obstruction
  demandResidual := fun obstruction => nomatch obstruction
  CommitmentAt := fun _source _content => PEmpty
  MandateOriginAt := fun _source _content => PEmpty
  AcceptedTaskAt := M14ArtProductionAcceptedTaskAt oldVisit sourceIndex
    boundary
  ActiveDependencyAt := fun _source _content => PEmpty
  ProtectedRiskAt := fun _source _content => PEmpty
  AdmissionAuthorityAt := M14ArtProductionAdmissionAuthorityAt oldVisit
    sourceIndex boundary
  AcceptedAt := M14ArtProductionBearerAcceptanceAt oldVisit sourceIndex
    boundary
  StandingMandateAt := fun _bearer _source _scope => PEmpty
  DischargeJurisdiction := fun _content _scope => PUnit
  ProgressAt := M14ArtProductionProgressAt oldVisit sourceIndex boundary
  MaintenanceAt := fun _source _content _scope => PEmpty
  TypedDeferAt := fun _source _content _scope => PEmpty
  ScopeNarrowingAt := fun _source _oldScope _newScope => PEmpty
  TransferAcceptedAt := fun _source _oldBearer _newBearer _scope => PEmpty
  FulfilledAt := fun _source _content _scope => PEmpty
  WaivedAt := fun _source _content _scope => PEmpty
  InvalidatedAt := fun _source _content _scope => PEmpty
  AbandonedAt := fun _source _content _scope => PEmpty
  ImpossibleResidueAcceptedAt := fun _source _content _scope => PEmpty
  SupersessionAt := fun _source _oldIncidence _oldContent _newIncidence
    _newContent _oldScope _newScope => PEmpty
  ReopenAt := fun _source _oldIncidence _oldContent _newIncidence
    _newContent _oldScope _newScope => PEmpty
  JurisdictionEndedAt := fun _source _content _scope => PEmpty
  ConsentRevokedAt := fun _source _content _scope => PEmpty
  CapacityReleasedAt := fun _source _content _scope => PEmpty
  UpperRouteAt := fun _source _content _scope => PEmpty
  NextActorSignal := PEmpty
  AgeSignal := PEmpty
  TransferOfferSignal := PEmpty

abbrev M14ArtProductionVocabularyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  m14ArtProductionVocabularyAt oldVisit sourceIndex boundary

def m14ArtProductionAdmissionPayloadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (source : SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
      boundary) :
    NativeAdmissionPayload
      (M14ArtProductionVocabularyAt oldVisit sourceIndex boundary) where
  sourceEvent := source
  content := sourceObjectRead m14ArtProductionRawOccurrence
  residual := m14ArtProductionRawOccurrence
  bearer := source.materialService.materialBearer
  beneficiary := actualRelationCycleActorAt
    (m14ArtProductionDepthAt boundary) .t1
  scope := ()
  lineage := platformGateMaterialSeedAt boundary
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask (m14ArtProductionAcceptedTask source)
  authority := m14ArtProductionAdmissionAuthority source
  assumption := .accepted (m14ArtProductionBearerAcceptance source)
  dischargeJurisdiction := ()

def m14ArtProductionSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary

def m14ArtProductionRawObligationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionAdmissionPayloadAt
    (m14ArtProductionSourceAt oldVisit sourceIndex boundary)).toObligation

inductive M14ArtProductionBoundaryEventAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AdmittedObligation
      (M14ArtProductionVocabularyAt oldVisit sourceIndex boundary) -> Type
  | private generated : M14ArtProductionBoundaryEventAt oldVisit sourceIndex
      boundary (m14ArtProductionRawObligationAt oldVisit sourceIndex boundary)

def m14ArtProductionProcessAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    NativeResponsibilityProcess
      (M14ArtProductionVocabularyAt oldVisit sourceIndex boundary) where
  AdmissionEvent := SourceGeneratedM14ArtProductionSourceAt oldVisit
    sourceIndex boundary
  admissionPayload := m14ArtProductionAdmissionPayloadAt
  BoundaryEvent := M14ArtProductionBoundaryEventAt oldVisit sourceIndex
    boundary
  boundarySource := by
    intro obligation event
    cases event
    exact m14ArtProductionSourceAt oldVisit sourceIndex boundary
  boundary_anchor_eq := by
    intro obligation event
    cases event
    rfl
  boundary_incidence_eq := by
    intro obligation event
    cases event
    rfl
  boundaryDisposition := by
    intro obligation event
    cases event
    exact .carry (.progressed m14ArtProductionWorkOccurrence
      (m14ArtProductionProgress
        (m14ArtProductionSourceAt oldVisit sourceIndex boundary)))
  ReopenEvent := fun _archive => PEmpty
  reopenPayload := fun event => nomatch event

abbrev M14ArtProductionProcessAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  m14ArtProductionProcessAt oldVisit sourceIndex boundary

def m14ArtProductionBoundaryEvent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14ArtProductionBoundaryEventAt oldVisit sourceIndex boundary
      (m14ArtProductionRawObligationAt oldVisit sourceIndex boundary) :=
  .generated

def m14ArtProductionEmptyStateAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ResponsibilityState
      (M14ArtProductionVocabularyAt oldVisit sourceIndex boundary) :=
  ResponsibilityState.empty _

def m14ArtProductionAdmissionEdgeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (M14ArtProductionProcessAt oldVisit sourceIndex boundary).Edge
      (m14ArtProductionEmptyStateAt oldVisit sourceIndex boundary) :=
  .admit (m14ArtProductionSourceAt oldVisit sourceIndex boundary)

def m14ArtProductionSourceStateAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionAdmissionEdgeAt oldVisit sourceIndex boundary).target

def m14ArtProductionSourceSlotAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Fin (m14ArtProductionSourceStateAt oldVisit sourceIndex boundary
      ).slots.length :=
  ⟨0, by
    simp [m14ArtProductionSourceStateAt, m14ArtProductionAdmissionEdgeAt,
      m14ArtProductionEmptyStateAt,
      NativeResponsibilityProcess.Edge.target]⟩

theorem m14ArtProductionSource_present
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtProductionSourceStateAt oldVisit sourceIndex boundary).slots.get
        (m14ArtProductionSourceSlotAt oldVisit sourceIndex boundary) =
      .live (m14ArtProductionRawObligationAt oldVisit sourceIndex boundary) :=
  rfl

def m14ArtProductionProgressEdgeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (M14ArtProductionProcessAt oldVisit sourceIndex boundary).Edge
      (m14ArtProductionSourceStateAt oldVisit sourceIndex boundary) :=
  .cross (m14ArtProductionSourceSlotAt oldVisit sourceIndex boundary)
    (m14ArtProductionRawObligationAt oldVisit sourceIndex boundary)
    (m14ArtProductionSource_present oldVisit sourceIndex boundary)
    (m14ArtProductionBoundaryEvent oldVisit sourceIndex boundary)

def m14ArtProductionTargetStateAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionProgressEdgeAt oldVisit sourceIndex boundary).target

def m14ArtProductionRunAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (M14ArtProductionProcessAt oldVisit sourceIndex boundary).Run
      (m14ArtProductionSourceStateAt oldVisit sourceIndex boundary)
      (m14ArtProductionTargetStateAt oldVisit sourceIndex boundary) :=
  .step .nil (m14ArtProductionProgressEdgeAt oldVisit sourceIndex boundary)

@[simp] theorem m14ArtProductionRun_events_length
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtProductionRunAt oldVisit sourceIndex boundary).events.length = 1 :=
  rfl

def m14ArtProductionProducedObligationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { m14ArtProductionRawObligationAt oldVisit sourceIndex boundary with
    residual := m14ArtProductionWorkOccurrence }

@[simp] theorem m14ArtProductionTarget_writeBack_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtProductionTargetStateAt oldVisit sourceIndex boundary).slots[0]? =
      some (.live
        (m14ArtProductionProducedObligationAt oldVisit sourceIndex
          boundary)) :=
  rfl

def m14ArtProductionSourceOwnershipAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceOwnsResponsibilityIncidence
      (M14ArtProductionVocabularyAt oldVisit sourceIndex boundary)
      (m14ArtProductionSourceAt oldVisit sourceIndex boundary)
      (m14ArtProductionRawObligationAt oldVisit sourceIndex boundary) :=
  (M14ArtProductionProcessAt oldVisit sourceIndex boundary
    ).boundarySourceOwnership
      (m14ArtProductionBoundaryEvent oldVisit sourceIndex boundary)

/-- Canonical lifecycle write-back generated by the progress edge. -/
structure SourceGeneratedM14ArtProductionWriteBackAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type where
  private mk ::
  trace : (M14ArtProductionProcessAt oldVisit sourceIndex boundary).Run
    (m14ArtProductionSourceStateAt oldVisit sourceIndex boundary)
    (m14ArtProductionTargetStateAt oldVisit sourceIndex boundary)
  traceExact : trace = m14ArtProductionRunAt oldVisit sourceIndex boundary

def sourceGeneratedM14ArtProductionWriteBackAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14ArtProductionWriteBackAt oldVisit sourceIndex
      boundary :=
  ⟨m14ArtProductionRunAt oldVisit sourceIndex boundary, rfl⟩

@[simp] theorem m14ArtProductionWriteBack_trace_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (sourceGeneratedM14ArtProductionWriteBackAt oldVisit sourceIndex boundary
      ).trace = m14ArtProductionRunAt oldVisit sourceIndex boundary :=
  rfl

theorem m14ArtProductionMaterialActionNext_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let source := m14ArtProductionSourceAt oldVisit sourceIndex boundary
    source.materialService.generatedNext =
      ⟨source.materialService.sourceAction.target.TargetV,
        source.materialService.sourceAction.target.targetRoot.toAuthoritativeRoot,
        source.materialService.sourceAction.target.targetVisit⟩ := by
  dsimp
  exact (m14ArtProductionSourceAt oldVisit sourceIndex boundary
    ).materialService.generatedNextExact

/-! ## Negative controls: source material, trace, and write-back are not
optional reports. -/

abbrev M14ArtProductionProgressReceiptAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14ArtProductionProgressAt oldVisit sourceIndex boundary
    (m14ArtProductionSourceAt oldVisit sourceIndex boundary)
    (sourceObjectRead m14ArtProductionRawOccurrence)
    m14ArtProductionRawOccurrence m14ArtProductionWorkOccurrence

structure M14ArtProductionWithoutMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type where
  progress : M14ArtProductionProgressReceiptAt oldVisit sourceIndex boundary
  noMaterial : IsEmpty (SourceGeneratedM12BeautyMaterialAt .coarse)

structure M14ArtProductionWithoutTraceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type where
  progress : M14ArtProductionProgressReceiptAt oldVisit sourceIndex boundary
  noTrace : IsEmpty
    ((M14ArtProductionProcessAt oldVisit sourceIndex boundary).Run
      (m14ArtProductionSourceStateAt oldVisit sourceIndex boundary)
      (m14ArtProductionTargetStateAt oldVisit sourceIndex boundary))

structure M14ArtProductionWithoutWriteBackAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type where
  progress : M14ArtProductionProgressReceiptAt oldVisit sourceIndex boundary
  noWriteBack : IsEmpty
    (SourceGeneratedM14ArtProductionWriteBackAt oldVisit sourceIndex boundary)

theorem m14ArtProduction_noMaterial_claim_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty (M14ArtProductionWithoutMaterialAt oldVisit sourceIndex
      boundary) :=
  ⟨fun candidate => candidate.noMaterial.false
    (m14ArtProductionSourceAt oldVisit sourceIndex boundary).rawMaterial⟩

theorem m14ArtProduction_noTrace_claim_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty (M14ArtProductionWithoutTraceAt oldVisit sourceIndex boundary) :=
  ⟨fun candidate => candidate.noTrace.false
    (m14ArtProductionRunAt oldVisit sourceIndex boundary)⟩

theorem m14ArtProduction_emptyTrace_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty { writeBack : SourceGeneratedM14ArtProductionWriteBackAt oldVisit
        sourceIndex boundary // writeBack.trace.events = [] } :=
  ⟨fun candidate => by
    have emptyTrace := candidate.property
    rw [candidate.1.traceExact] at emptyTrace
    simp [m14ArtProductionRunAt,
      NativeResponsibilityProcess.Run.events] at emptyTrace
  ⟩

theorem m14ArtProduction_noWriteBack_claim_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty (M14ArtProductionWithoutWriteBackAt oldVisit sourceIndex
      boundary) :=
  ⟨fun candidate => candidate.noWriteBack.false
    (sourceGeneratedM14ArtProductionWriteBackAt oldVisit sourceIndex
      boundary)⟩

theorem sourceGeneratedM14ActualArtProduction_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let source := m14ArtProductionSourceAt oldVisit sourceIndex boundary
    Nonempty (M14ArtProductionProgressAt oldVisit sourceIndex boundary source
        (sourceObjectRead m14ArtProductionRawOccurrence)
        m14ArtProductionRawOccurrence m14ArtProductionWorkOccurrence) ∧
      type_of% (m14ArtProductionProgress_endpoints_exact
        (m14ArtProductionProgress source)) ∧
      source.materialDebit = platformGateMaterialMaintenanceDebitAt boundary ∧
      source.rawMaterial = sourceGeneratedM12BeautyMaterialAt .coarse ∧
      source.publicationContact = sourceGeneratedM12PublicationContact ∧
      type_of% m14ArtWork_object_preserved ∧
      type_of% m14ArtWork_alignment_changes ∧
      type_of% m14ArtWork_transformation_nontrivial ∧
      Nonempty (SourceOwnsResponsibilityIncidence
        (M14ArtProductionVocabularyAt oldVisit sourceIndex boundary)
        source (m14ArtProductionRawObligationAt oldVisit sourceIndex
          boundary)) ∧
      (m14ArtProductionRunAt oldVisit sourceIndex boundary).events.length = 1 ∧
      type_of% (m14ArtProductionTarget_writeBack_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProductionWriteBack_trace_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProductionMaterialActionNext_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProduction_noMaterial_claim_isEmpty oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProduction_noTrace_claim_isEmpty oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProduction_emptyTrace_isEmpty oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProduction_noWriteBack_claim_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14ArtProduction_sourceActionRuntime oldVisit sourceIndex
        boundary) ∧
      type_of% (sourceGeneratedM12BeautyMaterial_directConsumer .coarse) ∧
      type_of% sourceGeneratedM12AestheticPublicCommunication_directConsumer ∧
      type_of% (platformGateFullAdmission_directConsumer oldVisit sourceIndex
        boundary) := by
  let source := m14ArtProductionSourceAt oldVisit sourceIndex boundary
  exact ⟨⟨m14ArtProductionProgress source⟩,
    m14ArtProductionProgress_endpoints_exact
      (m14ArtProductionProgress source),
    source.materialDebit_exact, source.rawMaterial_exact,
    source.publicationContact_exact,
    m14ArtWork_object_preserved, m14ArtWork_alignment_changes,
    m14ArtWork_transformation_nontrivial,
    ⟨m14ArtProductionSourceOwnershipAt oldVisit sourceIndex boundary⟩,
    m14ArtProductionRun_events_length oldVisit sourceIndex boundary,
    m14ArtProductionTarget_writeBack_exact oldVisit sourceIndex boundary,
    m14ArtProductionWriteBack_trace_exact oldVisit sourceIndex boundary,
    m14ArtProductionMaterialActionNext_exact oldVisit sourceIndex boundary,
    m14ArtProduction_noMaterial_claim_isEmpty oldVisit sourceIndex boundary,
    m14ArtProduction_noTrace_claim_isEmpty oldVisit sourceIndex boundary,
    m14ArtProduction_emptyTrace_isEmpty oldVisit sourceIndex boundary,
    m14ArtProduction_noWriteBack_claim_isEmpty oldVisit sourceIndex boundary,
    m14ArtProduction_sourceActionRuntime oldVisit sourceIndex boundary,
    sourceGeneratedM12BeautyMaterial_directConsumer .coarse,
    sourceGeneratedM12AestheticPublicCommunication_directConsumer,
    platformGateFullAdmission_directConsumer oldVisit sourceIndex boundary⟩

end
end Source
end ArtProduction
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source.m14ArtProductionProgress_endpoints_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source.m14ArtProductionTarget_writeBack_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source.m14ArtProductionMaterialActionNext_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source.m14ArtProduction_emptyTrace_isEmpty
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source.sourceGeneratedM14ActualArtProduction_directConsumer
