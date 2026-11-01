import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Theory.Revision.ClaimAuthorityDisposition
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedLedger

/-!
# Joint-root-derived claim lifecycle fixture

Every lifecycle object is generated at an arbitrary visit of the existing old
root.  The initial-visit API at the end is a definitional specialization, not
a transported copy.  Migration occurs at revised current `0`; retirement
occurs at revised current `1`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M13ReflexiveClaimLifecycleFixture

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ComplementObservation Settlement Theory.Revision
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8RevisedLedger

noncomputable section

abbrev OldTheory := RootInquiryU8CompletionRegression.oldTheory
abbrev OldN := M9ProofCarryingRenewalU8Failure.N
abbrev OldVisit :=
  RootVisit
    M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot

/-! ## Visit-indexed lifecycle -/

abbrev RevisedNAt (oldVisit : OldVisit) :=
  M9ProofCarryingRenewalU8RevisedLedger.NewNAt oldVisit

abbrev RevisedVAt (oldVisit : OldVisit) :=
  M9ProofCarryingRenewalU8RevisedLedger.NewVAt oldVisit

/-- Full occurrence identity, including the revised root current. -/
abbrev RevisedRootOccurrenceAt (oldVisit : OldVisit) :=
  Sigma (revisedSourceAt oldVisit).toRootSource.actual.OccurrenceAt

def firstRootOccurrenceAt (oldVisit : OldVisit) :
    RevisedRootOccurrenceAt oldVisit :=
  ⟨(0 : Nat), revisedEmittedAt oldVisit (0 : Nat)⟩

def laterRootOccurrenceAt (oldVisit : OldVisit) :
    RevisedRootOccurrenceAt oldVisit :=
  ⟨(1 : Nat), revisedEmittedAt oldVisit (1 : Nat)⟩

theorem revisedOccurrence_eq_emitted_at
    (oldVisit : OldVisit)
    {current : (RevisedVAt oldVisit).Current}
    (occurrence :
      (revisedSourceAt oldVisit).toRootSource.actual.OccurrenceAt current) :
    occurrence = revisedEmittedAt oldVisit current := by
  exact
    M14SourceGeneratedLossAllocationCompiler.lossAllocationOccurrence_eq_emitted
      (rootedAt oldVisit) occurrence

abbrev revisedInitialSupportAt (oldVisit : OldVisit) :
    (RevisedNAt oldVisit).Support :=
  M14SourceGeneratedLossAllocationWorld.lossAllocationInitialSupport
    (rootedAt oldVisit)

/-- Responsibility content and bearer are literal images of the revised
old-row claim and responsibility carriers. -/
def claimVocabularyAt (oldVisit : OldVisit) :
    ResponsibilityLifecycle.Vocabulary where
  SourceEvent := RevisedRootOccurrenceAt oldVisit
  Content := (RevisedNAt oldVisit).Claim
  Residual := Unit
  Bearer := (RevisedNAt oldVisit).Responsibility
  ProtectedInterest := Unit
  Scope := (RevisedNAt oldVisit).Support
  Lineage := (RevisedNAt oldVisit).Lineage
  Incidence := (RevisedNAt oldVisit).Incidence
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun _ => MinimalRegistrableSourceAnchor.canonical
    (revisedInitialSupportAt oldVisit)
    ((RevisedNAt oldVisit).lineageAt (revisedInitialSupportAt oldVisit))
  sourceIncidence := fun _ =>
    (RevisedNAt oldVisit).incidenceAt (revisedInitialSupportAt oldVisit)
  ObstructionAt := fun _ => Unit
  demandContent := fun _ => (oldRevisedEntryAt oldVisit).claim
  demandResidual := fun _ => ()
  CommitmentAt := fun _ _ => Unit
  MandateOriginAt := fun _ _ => Unit
  AcceptedTaskAt := fun _ _ => Unit
  ActiveDependencyAt := fun _ _ => Unit
  ProtectedRiskAt := fun _ _ => Unit
  AdmissionAuthorityAt := fun _ _ => Unit
  AcceptedAt := fun _ _ _ => Unit
  StandingMandateAt := fun _ _ _ => Unit
  DischargeJurisdiction := fun _ _ => Unit
  ProgressAt := fun _ _ _ _ => Unit
  MaintenanceAt := fun _ _ _ => Unit
  TypedDeferAt := fun _ _ _ => Unit
  ScopeNarrowingAt := fun _ _ _ => Unit
  TransferAcceptedAt := fun _ _ _ _ => Unit
  FulfilledAt := fun _ _ _ => Unit
  WaivedAt := fun _ _ _ => Unit
  InvalidatedAt := fun _ _ _ => Unit
  AbandonedAt := fun _ _ _ => Unit
  ImpossibleResidueAcceptedAt := fun _ _ _ => Unit
  SupersessionAt := fun _ _ _ _ _ _ _ => Unit
  ReopenAt := fun _ _ _ _ _ _ _ => Unit
  JurisdictionEndedAt := fun _ _ _ => Unit
  ConsentRevokedAt := fun _ _ _ => Unit
  CapacityReleasedAt := fun _ _ _ => Unit
  UpperRouteAt := fun _ _ _ => Unit
  NextActorSignal := Unit
  AgeSignal := Unit
  TransferOfferSignal := Unit

abbrev ClaimVAt (oldVisit : OldVisit) := claimVocabularyAt oldVisit

/-- The inherited obligation is read directly from this visit's revised
old-row image. -/
def inheritedClaimPayloadAt (oldVisit : OldVisit) :
    NativeAdmissionPayload (ClaimVAt oldVisit) where
  sourceEvent := firstRootOccurrenceAt oldVisit
  content := (oldRevisedEntryAt oldVisit).claim
  residual := ()
  bearer := (oldRevisedEntryAt oldVisit).1
  beneficiary := ()
  scope := revisedInitialSupportAt oldVisit
  lineage := (RevisedNAt oldVisit).lineageAt
    (revisedInitialSupportAt oldVisit)
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def inheritedClaimAt (oldVisit : OldVisit) :
    AdmittedObligation (ClaimVAt oldVisit) :=
  (inheritedClaimPayloadAt oldVisit).toObligation

inductive ClaimBoundaryEventAt
    (oldVisit : OldVisit)
    (_obligation : AdmittedObligation (ClaimVAt oldVisit))
  | migrate
  | retire

def boundarySourceAt
    (oldVisit : OldVisit)
    {obligation : AdmittedObligation (ClaimVAt oldVisit)} :
    ClaimBoundaryEventAt oldVisit obligation →
      (ClaimVAt oldVisit).SourceEvent
  | .migrate => firstRootOccurrenceAt oldVisit
  | .retire => laterRootOccurrenceAt oldVisit

def boundaryDispositionAt
    (oldVisit : OldVisit)
    {obligation : AdmittedObligation (ClaimVAt oldVisit)} :
    (event : ClaimBoundaryEventAt oldVisit obligation) →
      BoundaryDisposition (ClaimVAt oldVisit) obligation
        (boundarySourceAt oldVisit event)
  | .migrate =>
      .terminal (.superseded
        { successor := obligation
          incidence := ()
          lineage_eq := rfl
          anchorTransport := SourceAnchorTransport.refl _ })
  | .retire => .terminal (.final (.fulfilled ()))

def claimProcessAt (oldVisit : OldVisit) :
    NativeResponsibilityProcess (ClaimVAt oldVisit) where
  AdmissionEvent := Unit
  admissionPayload := fun _ => inheritedClaimPayloadAt oldVisit
  BoundaryEvent := ClaimBoundaryEventAt oldVisit
  boundarySource := boundarySourceAt oldVisit
  boundary_anchor_eq := by intro obligation event; cases event <;> rfl
  boundary_incidence_eq := by intro obligation event; cases event <;> rfl
  boundaryDisposition := boundaryDispositionAt oldVisit
  ReopenEvent := fun _ => PEmpty
  reopenPayload := fun event => nomatch event

abbrev ClaimPAt (oldVisit : OldVisit) := claimProcessAt oldVisit

def inheritedClaimAdmissionEdgeAt (oldVisit : OldVisit) :
    (ClaimPAt oldVisit).Edge
      (ResponsibilityState.empty (ClaimVAt oldVisit)) :=
  .admit ()

def inheritedClaimStateAt (oldVisit : OldVisit) :
    (ClaimPAt oldVisit).GeneratedState :=
  (NativeResponsibilityProcess.GeneratedState.initial (ClaimPAt oldVisit)).step
    (ClaimPAt oldVisit) (inheritedClaimAdmissionEdgeAt oldVisit)

abbrev firstWriteSourceAt (oldVisit : OldVisit) :
    ResponsibilityState (ClaimVAt oldVisit) :=
  (inheritedClaimStateAt oldVisit).current

@[simp] theorem inheritedClaimState_slot_present_at
    (oldVisit : OldVisit) :
    (inheritedClaimStateAt oldVisit).current.slots.get
        ⟨0, by change 0 < 1; decide⟩ =
      .live (inheritedClaimAt oldVisit) :=
  rfl

theorem inheritedClaimState_history_generated_at
    (oldVisit : OldVisit) :
    (inheritedClaimStateAt oldVisit).current.history =
      (inheritedClaimStateAt oldVisit).generated.events :=
  (inheritedClaimStateAt oldVisit).history_eq (ClaimPAt oldVisit)

def firstWriteSettlementAt (oldVisit : OldVisit) :
    ExactSettlementEdge (ClaimPAt oldVisit) (firstWriteSourceAt oldVisit) where
  slot := ⟨0, by change 0 < 1; decide⟩
  obligation := inheritedClaimAt oldVisit
  present := rfl
  event := .migrate

def firstWriteRolloverAt (oldVisit : OldVisit) :
    ExactSettlementEdge.SupersededRolloverAt
      (firstWriteSettlementAt oldVisit) where
  receipt :=
    { successor := inheritedClaimAt oldVisit
      incidence := ()
      lineage_eq := rfl
      anchorTransport := SourceAnchorTransport.refl _ }
  disposition_eq := rfl

def revisedInventoryAt (_oldVisit : OldVisit) : LawInventory OldN :=
  RootInquiryU8CompletionRegression.oldInventory

def revisionRelationAt (oldVisit : OldVisit) :
    LawRevisionRelation OldTheory.inventory (revisedInventoryAt oldVisit) where
  PreservedAt := fun _ _ => Unit
  WeakenedAt := fun _ _ => Unit
  ReplacedAt := fun _ _ => Unit

/-- Singleton fibre selecting this visit's exact revised initial event. -/
def dispositionSourceAt (oldVisit : OldVisit) :
    LawRevisionDispositionSourceAt (revisionRelationAt oldVisit) where
  OccurrenceAt := fun _ => { occurrence : RevisedRootOccurrenceAt oldVisit //
    occurrence = firstRootOccurrenceAt oldVisit }
  emit := fun _ => ⟨firstRootOccurrenceAt oldVisit, rfl⟩
  event_eq_emit := by
    intro law occurrence
    cases law
    apply Subtype.ext
    exact occurrence.2
  compileDisposition := fun _ _ => .replaced () ()

def migrationCompilerAt (oldVisit : OldVisit) :
    SourceOwnedInheritedClaimMigrationCompilerAt
      (dispositionSourceAt oldVisit) (ClaimPAt oldVisit)
      (firstWriteSourceAt oldVisit) where
  compileFirstWrite := fun _ _ => firstWriteSettlementAt oldVisit
  compileRollover := fun _ _ => firstWriteRolloverAt oldVisit

def migrationAt (oldVisit : OldVisit) :
    SourceGeneratedInheritedClaimMigrationAt
      (migrationCompilerAt oldVisit) () :=
  SourceGeneratedInheritedClaimMigrationAt.generate
    (migrationCompilerAt oldVisit) ()

@[simp] theorem migration_rootOccurrence_eq_at (oldVisit : OldVisit) :
    (migrationAt oldVisit).exactOccurrence.1 =
      firstRootOccurrenceAt oldVisit :=
  rfl

def laterConsumerAt (oldVisit : OldVisit) :
    ExactSettlementEdge.ResidualConsumerAt
      (migrationAt oldVisit).liveSuccessor where
  event := .retire

@[simp] theorem laterConsumer_source_eq_at (oldVisit : OldVisit) :
    (ClaimPAt oldVisit).boundarySource (laterConsumerAt oldVisit).event =
      laterRootOccurrenceAt oldVisit :=
  rfl

def laterFulfillmentAt (oldVisit : OldVisit) :
    ExactSettlementEdge.FulfilledSettlementAt
      ((migrationAt oldVisit).laterSettlement (laterConsumerAt oldVisit)) where
  receipt := ()
  disposition_eq := rfl

def retirementAt (oldVisit : OldVisit) :
    SourceGeneratedInheritedClaimRetirementAt
      (migrationAt oldVisit) (laterConsumerAt oldVisit)
      (laterFulfillmentAt oldVisit) :=
  SourceGeneratedInheritedClaimRetirementAt.generate
    (migrationAt oldVisit) (laterConsumerAt oldVisit)
    (laterFulfillmentAt oldVisit)

/-! ## Visit-indexed root-projection payloads -/

structure RootClaimMigrationFaceAtVisit
    (oldVisit : OldVisit)
    {current : (RevisedVAt oldVisit).Current}
    (occurrence :
      (revisedSourceAt oldVisit).toRootSource.actual.OccurrenceAt current) :
    Type where
  private mk ::
  rootOccurrence_eq :
    (⟨current, occurrence⟩ : RevisedRootOccurrenceAt oldVisit) =
      firstRootOccurrenceAt oldVisit

def RootClaimMigrationFaceAtVisit.generate
    {oldVisit : OldVisit}
    {current : (RevisedVAt oldVisit).Current}
    (occurrence :
      (revisedSourceAt oldVisit).toRootSource.actual.OccurrenceAt current)
    (rootOccurrence_eq :
      (⟨current, occurrence⟩ : RevisedRootOccurrenceAt oldVisit) =
        firstRootOccurrenceAt oldVisit) :
    RootClaimMigrationFaceAtVisit oldVisit occurrence :=
  ⟨rootOccurrence_eq⟩

namespace RootClaimMigrationFaceAtVisit

variable {oldVisit : OldVisit}
variable {current : (RevisedVAt oldVisit).Current}
variable {occurrence :
  (revisedSourceAt oldVisit).toRootSource.actual.OccurrenceAt current}

def exactMigration
    (_face : RootClaimMigrationFaceAtVisit oldVisit occurrence) :=
  migrationAt oldVisit

def exactRollover
    (_face : RootClaimMigrationFaceAtVisit oldVisit occurrence) :=
  (migrationAt oldVisit).firstWriteRollover

def liveSuccessor
    (_face : RootClaimMigrationFaceAtVisit oldVisit occurrence) :=
  (migrationAt oldVisit).liveSuccessor

theorem sourceEvent_eq_rootOccurrence
    (face : RootClaimMigrationFaceAtVisit oldVisit occurrence) :
    (ClaimPAt oldVisit).boundarySource
        (migrationAt oldVisit).firstWriteSettlement.event =
      (⟨current, occurrence⟩ : RevisedRootOccurrenceAt oldVisit) := by
  rcases face with ⟨rootOccurrence_eq⟩
  rw [rootOccurrence_eq]
  rfl

end RootClaimMigrationFaceAtVisit

structure RootClaimRetirementFaceAtVisit
    (oldVisit : OldVisit)
    {current : (RevisedVAt oldVisit).Current}
    (occurrence :
      (revisedSourceAt oldVisit).toRootSource.actual.OccurrenceAt current) :
    Type where
  private mk ::
  rootOccurrence_eq :
    (⟨current, occurrence⟩ : RevisedRootOccurrenceAt oldVisit) =
      laterRootOccurrenceAt oldVisit

def RootClaimRetirementFaceAtVisit.generate
    {oldVisit : OldVisit}
    {current : (RevisedVAt oldVisit).Current}
    (occurrence :
      (revisedSourceAt oldVisit).toRootSource.actual.OccurrenceAt current)
    (rootOccurrence_eq :
      (⟨current, occurrence⟩ : RevisedRootOccurrenceAt oldVisit) =
        laterRootOccurrenceAt oldVisit) :
    RootClaimRetirementFaceAtVisit oldVisit occurrence :=
  ⟨rootOccurrence_eq⟩

namespace RootClaimRetirementFaceAtVisit

variable {oldVisit : OldVisit}
variable {current : (RevisedVAt oldVisit).Current}
variable {occurrence :
  (revisedSourceAt oldVisit).toRootSource.actual.OccurrenceAt current}

def exactRetirement
    (_face : RootClaimRetirementFaceAtVisit oldVisit occurrence) :=
  retirementAt oldVisit

def closed
    (_face : RootClaimRetirementFaceAtVisit oldVisit occurrence) :=
  (retirementAt oldVisit).closed

theorem sourceEvent_eq_rootOccurrence
    (face : RootClaimRetirementFaceAtVisit oldVisit occurrence) :
    (ClaimPAt oldVisit).boundarySource (laterConsumerAt oldVisit).event =
      (⟨current, occurrence⟩ : RevisedRootOccurrenceAt oldVisit) := by
  rcases face with ⟨rootOccurrence_eq⟩
  rw [rootOccurrence_eq]
  rfl

end RootClaimRetirementFaceAtVisit

/-! ## Definitionally specialized initial-visit facade -/

abbrev initialVisit : OldVisit :=
  M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.initialVisit

abbrev RevisedN := RevisedNAt initialVisit
abbrev RevisedV := RevisedVAt initialVisit
abbrev RevisedRootOccurrence := RevisedRootOccurrenceAt initialVisit
abbrev firstRootOccurrence := firstRootOccurrenceAt initialVisit
abbrev laterRootOccurrence := laterRootOccurrenceAt initialVisit

theorem revisedOccurrence_eq_emitted
    {current : RevisedV.Current}
    (occurrence :
      revisedSource.toRootSource.actual.OccurrenceAt current) :
    occurrence = revisedEmitted current :=
  revisedOccurrence_eq_emitted_at initialVisit occurrence

abbrev revisedInitialSupport := revisedInitialSupportAt initialVisit
abbrev claimVocabulary := claimVocabularyAt initialVisit
abbrev ClaimV := ClaimVAt initialVisit
abbrev inheritedClaimPayload := inheritedClaimPayloadAt initialVisit
abbrev inheritedClaim := inheritedClaimAt initialVisit
abbrev ClaimBoundaryEvent := ClaimBoundaryEventAt initialVisit
def boundarySource {obligation : AdmittedObligation ClaimV} :
    ClaimBoundaryEvent obligation → ClaimV.SourceEvent :=
  boundarySourceAt initialVisit

def boundaryDisposition {obligation : AdmittedObligation ClaimV} :
    (event : ClaimBoundaryEvent obligation) →
      BoundaryDisposition ClaimV obligation (boundarySource event) :=
  boundaryDispositionAt initialVisit
abbrev claimProcess := claimProcessAt initialVisit
abbrev ClaimP := ClaimPAt initialVisit
abbrev inheritedClaimAdmissionEdge :=
  inheritedClaimAdmissionEdgeAt initialVisit
abbrev inheritedClaimState := inheritedClaimStateAt initialVisit
abbrev firstWriteSource := firstWriteSourceAt initialVisit

@[simp] theorem inheritedClaimState_slot_present :
    inheritedClaimState.current.slots.get ⟨0, by decide⟩ =
      .live inheritedClaim :=
  inheritedClaimState_slot_present_at initialVisit

theorem inheritedClaimState_history_generated :
    inheritedClaimState.current.history =
      inheritedClaimState.generated.events :=
  inheritedClaimState_history_generated_at initialVisit

abbrev firstWriteSettlement := firstWriteSettlementAt initialVisit
abbrev firstWriteRollover := firstWriteRolloverAt initialVisit
abbrev revisedInventory := revisedInventoryAt initialVisit
abbrev revisionRelation := revisionRelationAt initialVisit
abbrev dispositionSource := dispositionSourceAt initialVisit
abbrev migrationCompiler := migrationCompilerAt initialVisit
abbrev migration := migrationAt initialVisit

@[simp] theorem migration_rootOccurrence_eq :
    migration.exactOccurrence.1 = firstRootOccurrence :=
  migration_rootOccurrence_eq_at initialVisit

abbrev laterConsumer := laterConsumerAt initialVisit

@[simp] theorem laterConsumer_source_eq :
    ClaimP.boundarySource laterConsumer.event = laterRootOccurrence :=
  laterConsumer_source_eq_at initialVisit

abbrev laterFulfillment := laterFulfillmentAt initialVisit
abbrev retirement := retirementAt initialVisit

abbrev RootClaimMigrationFaceAt
    {current : RevisedV.Current}
    (occurrence :
      revisedSource.toRootSource.actual.OccurrenceAt current) :=
  RootClaimMigrationFaceAtVisit initialVisit occurrence

def RootClaimMigrationFaceAt.generate
    {current : RevisedV.Current}
    (occurrence :
      revisedSource.toRootSource.actual.OccurrenceAt current)
    (rootOccurrence_eq :
      (⟨current, occurrence⟩ : RevisedRootOccurrence) =
        firstRootOccurrence) :
    RootClaimMigrationFaceAt occurrence :=
  RootClaimMigrationFaceAtVisit.generate occurrence rootOccurrence_eq

namespace RootClaimMigrationFaceAt

variable {current : RevisedV.Current}
variable {occurrence :
  revisedSource.toRootSource.actual.OccurrenceAt current}

def exactMigration
    (face : RootClaimMigrationFaceAt occurrence) :=
  RootClaimMigrationFaceAtVisit.exactMigration
    (oldVisit := initialVisit) face

def exactRollover
    (face : RootClaimMigrationFaceAt occurrence) :=
  RootClaimMigrationFaceAtVisit.exactRollover
    (oldVisit := initialVisit) face

def liveSuccessor
    (face : RootClaimMigrationFaceAt occurrence) :=
  RootClaimMigrationFaceAtVisit.liveSuccessor
    (oldVisit := initialVisit) face

theorem sourceEvent_eq_rootOccurrence
    (face : RootClaimMigrationFaceAt occurrence) :
    ClaimP.boundarySource migration.firstWriteSettlement.event =
      (⟨current, occurrence⟩ : RevisedRootOccurrence) :=
  RootClaimMigrationFaceAtVisit.sourceEvent_eq_rootOccurrence face

end RootClaimMigrationFaceAt

abbrev RootClaimRetirementFaceAt
    {current : RevisedV.Current}
    (occurrence :
      revisedSource.toRootSource.actual.OccurrenceAt current) :=
  RootClaimRetirementFaceAtVisit initialVisit occurrence

def RootClaimRetirementFaceAt.generate
    {current : RevisedV.Current}
    (occurrence :
      revisedSource.toRootSource.actual.OccurrenceAt current)
    (rootOccurrence_eq :
      (⟨current, occurrence⟩ : RevisedRootOccurrence) =
        laterRootOccurrence) :
    RootClaimRetirementFaceAt occurrence :=
  RootClaimRetirementFaceAtVisit.generate occurrence rootOccurrence_eq

namespace RootClaimRetirementFaceAt

variable {current : RevisedV.Current}
variable {occurrence :
  revisedSource.toRootSource.actual.OccurrenceAt current}

def exactRetirement
    (face : RootClaimRetirementFaceAt occurrence) :=
  RootClaimRetirementFaceAtVisit.exactRetirement
    (oldVisit := initialVisit) face

def closed
    (face : RootClaimRetirementFaceAt occurrence) :=
  RootClaimRetirementFaceAtVisit.closed
    (oldVisit := initialVisit) face

theorem sourceEvent_eq_rootOccurrence
    (face : RootClaimRetirementFaceAt occurrence) :
    ClaimP.boundarySource laterConsumer.event =
      (⟨current, occurrence⟩ : RevisedRootOccurrence) :=
  RootClaimRetirementFaceAtVisit.sourceEvent_eq_rootOccurrence face

end RootClaimRetirementFaceAt

end
end M13ReflexiveClaimLifecycleFixture
end Society
end ProcessGame
end SaturationMonoid
