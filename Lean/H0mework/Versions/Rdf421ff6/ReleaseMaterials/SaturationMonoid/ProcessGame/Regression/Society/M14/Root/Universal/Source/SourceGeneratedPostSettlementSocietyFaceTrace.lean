import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.SourceNativeDependentFaceLaw
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.DomainReuse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Compiler.SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Response.Producer.SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Continuation.Producer.SourceGeneratedContributionCapacityBearerRoleIndependentContinuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Channel.Carrier.Producer.SourceGeneratedContributionCapacityEssentialAccessChannel

/-!
# Source-owned post-settlement Society face trace

This file is below the post-settlement living root.  It fixes one finite
classified face trace in the authority source before the emitter exists.
`actual` and `fullCaptureSearch` are restrictions of that one trace, not two
occurrences.  The search restriction may audit the actual whole-ledger image,
but it has no write or next-current constructor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementSocietyFaceTrace

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14UBIExitCapacityFixture
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse
open M14SourceGeneratedContributionCapacityBearerLeaveExecution
open M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open UniversalRootGrammar

/-- Actual execution and counterfactual audit are two coordinates of one
source-installed trace. -/
inductive PostSettlementSocietyScenario
  | actual
  | fullCaptureSearch
  deriving DecidableEq

/-- The finite bearing vocabulary of the existing post-settlement source.
The channel constructor remains dependent; tenure and health are generated
by their existing relation authorities rather than by a new sector registry. -/
inductive PostSettlementSocietyBearingFace
  | ledger
  | renewal
  | birthBearerExit
  | bearerExerciseResponse
  | bearerLeaveExecution
  | bearerRoleIndependentContinuation
  | essentialAccessTenure
  | essentialAccessHealth
  deriving DecidableEq

abbrev PostSettlementSourceAt (oldVisit : OldVisit) (sourceIndex : Nat) :=
  (contributionCapacityPostSettlementRenewalRestructuringSource oldVisit
    sourceIndex).toLedgerSource

abbrev PostSettlementOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (current : (PostSettlementRenewalVAt oldVisit).Current) :=
  (PostSettlementSourceAt oldVisit sourceIndex).source.toRootSource.actual.OccurrenceAt
    current

/-- Exact payload type already used by each old post-root projection. -/
def postSettlementSocietyFacePayloadAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    PostSettlementSocietyBearingFace → Type _
  | .ledger => SourceNativeLedgerEvolutionAt
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
      occurrence
  | .renewal => PLift (Nonempty (PeriodicActualServiceExitAt current))
  | .birthBearerExit => PLift (Nonempty
      (SourceGeneratedContributionCapacityBirthBearerExitAt current
        (Classical.choice occurrence.2.periodicExitGenerated)))
  | .bearerExerciseResponse => PLift (Nonempty
      (CanonicalContributionCapacityBearerExerciseNoncaptureResponseAt current
        (Classical.choice occurrence.2.periodicExitGenerated)))
  | .bearerLeaveExecution => PLift (Nonempty
      (CanonicalContributionCapacityBearerLeaveExecutionAt current
        (Classical.choice occurrence.2.periodicExitGenerated)))
  | .bearerRoleIndependentContinuation => PLift (Nonempty
      (CanonicalContributionCapacityBearerRoleIndependentContinuationAt
        current (Classical.choice occurrence.2.periodicExitGenerated)))
  | .essentialAccessTenure => PLift (Nonempty
      (SourceGeneratedContributionCapacityEssentialAccessChannelAt current
        tenureAuthority
        (Classical.choice occurrence.2.periodicExitGenerated)))
  | .essentialAccessHealth => PLift (Nonempty
      (SourceGeneratedContributionCapacityEssentialAccessChannelAt current
        healthAuthority
        (Classical.choice occurrence.2.periodicExitGenerated)))

/-- The payload is generated from the exact lower occurrence. -/
def postSettlementSocietyFaceReadAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    (face : PostSettlementSocietyBearingFace) →
      postSettlementSocietyFacePayloadAt oldVisit sourceIndex occurrence face
  | .ledger =>
      (contributionCapacityPostSettlementRenewalLedgerCompiler oldVisit
        sourceIndex).compile occurrence
  | .renewal => PLift.up occurrence.2.periodicExitGenerated
  | .birthBearerExit =>
      PLift.up
        ⟨sourceGeneratedContributionCapacityBirthBearerExitAt current
          (Classical.choice occurrence.2.periodicExitGenerated)⟩
  | .bearerExerciseResponse =>
      PLift.up
        ⟨sourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
          current (Classical.choice occurrence.2.periodicExitGenerated)⟩
  | .bearerLeaveExecution =>
      PLift.up
        ⟨sourceGeneratedContributionCapacityBearerLeaveExecutionAt current
          (Classical.choice occurrence.2.periodicExitGenerated)⟩
  | .bearerRoleIndependentContinuation =>
      PLift.up
        ⟨sourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
          current (Classical.choice occurrence.2.periodicExitGenerated)⟩
  | .essentialAccessTenure =>
      PLift.up
        ⟨sourceGeneratedContributionCapacityEssentialAccessChannelAt current
          tenureAuthority
          (Classical.choice occurrence.2.periodicExitGenerated)⟩
  | .essentialAccessHealth =>
      PLift.up
        ⟨sourceGeneratedContributionCapacityEssentialAccessChannelAt current
          healthAuthority
          (Classical.choice occurrence.2.periodicExitGenerated)⟩

/-- Search deletes only capture-adjusted continuation actionability.  Every
other point retains the same exact source payload as the actual restriction. -/
def postSettlementSocietyPassedAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    PostSettlementSocietyScenario →
      PostSettlementSocietyBearingFace → Type _
  | .fullCaptureSearch, .bearerRoleIndependentContinuation =>
      PLift (Nonempty BirthBearerFullCaptureActionableExit)
  | _, face =>
      postSettlementSocietyFacePayloadAt oldVisit sourceIndex occurrence face

abbrev PostSettlementFailureResidualBearerAt (current : Nat) :=
  PLift (Nonempty (PeriodicActualServiceExitAt current))

abbrev PostSettlementFailureSourceOwnership :=
  SourceOwnsResponsibilityIncidence V
    (P.boundarySource
      exitCapacityProgram.purchasingPowerStanding.activatedConsumer.activation)
    (exactOpenSettlement exactResidualActivation).obligation

abbrev PostSettlementFailureConsumerAt {current : Nat}
    (bearer : PostSettlementFailureResidualBearerAt current) :=
  PLift (Nonempty (RenewalResponsibilityConsumerAt
    (Classical.choice bearer.down).paymentOccurrence.installed.operationalAuthority))

/-- A full-capture audit is a typed disposition of the existing source
occurrence.  It stores no alternative write: its whole-ledger value is
definitionally required to be the canonical compiler image. -/
structure PostSettlementFullCaptureAuditDispositionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current)
    (scenario : PostSettlementSocietyScenario)
    (face : PostSettlementSocietyBearingFace)
    (bearer : PeriodicActualServiceExitAt current)
    (_consumer : RenewalResponsibilityConsumerAt
      bearer.paymentOccurrence.installed.operationalAuthority) : Type 19 where
  scenarioExact : scenario = .fullCaptureSearch
  faceExact : face = .bearerRoleIndependentContinuation
  bearerExact : bearer = Classical.choice occurrence.2.periodicExitGenerated
  wholeLedgerWriteBack : SourceNativeLedgerEvolutionAt
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
    occurrence
  wholeLedgerExact : wholeLedgerWriteBack =
    (contributionCapacityPostSettlementRenewalLedgerCompiler oldVisit
      sourceIndex).compile occurrence
  bareContinuation :
    CanonicalContributionCapacityBearerRoleIndependentContinuationAt current
      bearer
  bareContinuationExact : bareContinuation =
    sourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
      current bearer
  capturedActionableExitEmpty : IsEmpty BirthBearerFullCaptureActionableExit
  paymentRootFactorization :
    bearer.paymentOccurrence.installed.RootAnswerAndNextFactorizes
  generatedTargetCurrent : Nat
  generatedTargetCurrentExact : generatedTargetCurrent =
    (show Nat from current) + 1

/-- Applying a search disposition to the actual ledger is identity. -/
def PostSettlementFullCaptureAuditDispositionAt.applyToActualWriteBack
    {oldVisit : OldVisit} {sourceIndex : Nat}
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    {occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current}
    {scenario : PostSettlementSocietyScenario}
    {face : PostSettlementSocietyBearingFace}
    {bearer : PeriodicActualServiceExitAt current}
    {consumer : RenewalResponsibilityConsumerAt
      bearer.paymentOccurrence.installed.operationalAuthority}
    (_audit : PostSettlementFullCaptureAuditDispositionAt oldVisit sourceIndex
      occurrence scenario face bearer consumer)
    (actual : SourceNativeLedgerEvolutionAt
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
      occurrence) := actual

@[simp] theorem searchDisposition_preservesActualWriteBack
    {oldVisit : OldVisit} {sourceIndex : Nat}
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    {occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current}
    {scenario : PostSettlementSocietyScenario}
    {face : PostSettlementSocietyBearingFace}
    {bearer : PeriodicActualServiceExitAt current}
    {consumer : RenewalResponsibilityConsumerAt
      bearer.paymentOccurrence.installed.operationalAuthority}
    (audit : PostSettlementFullCaptureAuditDispositionAt oldVisit sourceIndex
      occurrence scenario face bearer consumer)
    (actual : SourceNativeLedgerEvolutionAt
      (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex)
      occurrence) :
    audit.applyToActualWriteBack actual = actual :=
  rfl

def postSettlementSocietyVocabulary
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeDependentFaceVocabulary
      (PostSettlementSourceAt oldVisit sourceIndex) where
  Scenario := PostSettlementSocietyScenario
  scenarioDecidableEq := inferInstance
  actualScenario := .actual
  FaceAt := fun {_current} _occurrence =>
    PostSettlementSocietyBearingFace
  PassedAt := fun {_current} occurrence scenario face =>
    postSettlementSocietyPassedAt oldVisit sourceIndex occurrence scenario face
  ResidualBearerAt := fun {current} _occurrence _scenario _face =>
    PostSettlementFailureResidualBearerAt current
  SourceOwnershipAt := fun {_current} _occurrence _scenario _face _bearer =>
    PostSettlementFailureSourceOwnership
  ConsumerAt := fun {_current} _occurrence _scenario _face bearer =>
    PostSettlementFailureConsumerAt bearer
  DispositionAt := fun {_current} occurrence scenario face bearer consumer =>
    PLift (Nonempty
      (PostSettlementFullCaptureAuditDispositionAt oldVisit sourceIndex
        occurrence scenario face (Classical.choice bearer.down)
        (Classical.choice consumer.down)))

abbrev PostSettlementSocietyPointAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :=
  SourceGeneratedClassifiedDependentFacePointAt
    (postSettlementSocietyVocabulary oldVisit sourceIndex) occurrence

def postSettlementFullCaptureFailedAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    SourceGeneratedFailedDependentFaceAt
      (postSettlementSocietyVocabulary oldVisit sourceIndex) occurrence
      .fullCaptureSearch .bearerRoleIndependentContinuation := by
  let bearer := Classical.choice occurrence.2.periodicExitGenerated
  let consumer := bearer.paymentOccurrence.installed.rootResponsibilityConsumer
  exact
    { passedEmpty := ⟨fun reported =>
        reported.down.elim fun actionableExit =>
          birthBearerFullCaptureActionableExit_isEmpty.false actionableExit⟩
      residualBearer := PLift.up occurrence.2.periodicExitGenerated
      sourceOwned :=
        exitCapacityProgram.purchasingPowerStanding.sourceOwnership
      consumer := PLift.up ⟨consumer⟩
      disposition := PLift.up
        ⟨{ scenarioExact := rfl
           faceExact := rfl
           bearerExact := rfl
           wholeLedgerWriteBack :=
             (contributionCapacityPostSettlementRenewalLedgerCompiler oldVisit
               sourceIndex).compile occurrence
           wholeLedgerExact := rfl
           bareContinuation :=
             sourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
               current bearer
           bareContinuationExact := rfl
           capturedActionableExitEmpty :=
             birthBearerFullCaptureActionableExit_isEmpty
           paymentRootFactorization := bearer.rootFactorization
           generatedTargetCurrent := (show Nat from current) + 1
           generatedTargetCurrentExact := rfl }⟩ }

/-- The sole point constructor.  Its result is already classified by the
fixed source vocabulary. -/
def postSettlementSocietyPointAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current)
    (scenario : PostSettlementSocietyScenario)
    (face : PostSettlementSocietyBearingFace) :
    PostSettlementSocietyPointAt oldVisit sourceIndex occurrence := by
  cases scenario with
  | actual =>
      exact
        { scenario := .actual
          face := face
          outcome := .inl
            (postSettlementSocietyFaceReadAt oldVisit sourceIndex occurrence
              face) }
  | fullCaptureSearch =>
      cases face with
      | bearerRoleIndependentContinuation =>
          exact
            { scenario := .fullCaptureSearch
              face := .bearerRoleIndependentContinuation
              outcome := .inr
                (postSettlementFullCaptureFailedAt oldVisit sourceIndex
                  occurrence) }
      | ledger =>
          exact
            { scenario := .fullCaptureSearch
              face := .ledger
              outcome := .inl
                (postSettlementSocietyFaceReadAt oldVisit sourceIndex
                  occurrence .ledger) }
      | renewal =>
          exact
            { scenario := .fullCaptureSearch
              face := .renewal
              outcome := .inl
                (postSettlementSocietyFaceReadAt oldVisit sourceIndex
                  occurrence .renewal) }
      | birthBearerExit =>
          exact
            { scenario := .fullCaptureSearch
              face := .birthBearerExit
              outcome := .inl
                (postSettlementSocietyFaceReadAt oldVisit sourceIndex
                  occurrence .birthBearerExit) }
      | bearerExerciseResponse =>
          exact
            { scenario := .fullCaptureSearch
              face := .bearerExerciseResponse
              outcome := .inl
                (postSettlementSocietyFaceReadAt oldVisit sourceIndex
                  occurrence .bearerExerciseResponse) }
      | bearerLeaveExecution =>
          exact
            { scenario := .fullCaptureSearch
              face := .bearerLeaveExecution
              outcome := .inl
                (postSettlementSocietyFaceReadAt oldVisit sourceIndex
                  occurrence .bearerLeaveExecution) }
      | essentialAccessTenure =>
          exact
            { scenario := .fullCaptureSearch
              face := .essentialAccessTenure
              outcome := .inl
                (postSettlementSocietyFaceReadAt oldVisit sourceIndex
                  occurrence .essentialAccessTenure) }
      | essentialAccessHealth =>
          exact
            { scenario := .fullCaptureSearch
              face := .essentialAccessHealth
              outcome := .inl
                (postSettlementSocietyFaceReadAt oldVisit sourceIndex
                  occurrence .essentialAccessHealth) }

abbrev PostSettlementSocietyGrammarIndex :=
  PostSettlementSocietyScenario × PostSettlementSocietyBearingFace

def postSettlementSocietyGrammarIndices :
    List PostSettlementSocietyGrammarIndex :=
  [(.actual, .ledger),
    (.actual, .renewal),
    (.actual, .birthBearerExit),
    (.actual, .bearerExerciseResponse),
    (.actual, .bearerLeaveExecution),
    (.actual, .bearerRoleIndependentContinuation),
    (.actual, .essentialAccessTenure),
    (.actual, .essentialAccessHealth),
    (.fullCaptureSearch, .ledger),
    (.fullCaptureSearch, .renewal),
    (.fullCaptureSearch, .birthBearerExit),
    (.fullCaptureSearch, .bearerExerciseResponse),
    (.fullCaptureSearch, .bearerLeaveExecution),
    (.fullCaptureSearch, .bearerRoleIndependentContinuation),
    (.fullCaptureSearch, .essentialAccessTenure),
    (.fullCaptureSearch, .essentialAccessHealth)]

@[simp] theorem postSettlementSocietyGrammarIndices_length :
    postSettlementSocietyGrammarIndices.length = 16 :=
  rfl

theorem postSettlementSocietyGrammarIndices_nodup :
    postSettlementSocietyGrammarIndices.Nodup := by
  decide

theorem postSettlementSocietyGrammarIndex_mem
    (scenario : PostSettlementSocietyScenario)
    (face : PostSettlementSocietyBearingFace) :
    (scenario, face) ∈ postSettlementSocietyGrammarIndices := by
  cases scenario <;> cases face <;> decide

def postSettlementSocietyPointOfIndexAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current)
    (index : PostSettlementSocietyGrammarIndex) :
    PostSettlementSocietyPointAt oldVisit sourceIndex occurrence :=
  postSettlementSocietyPointAt oldVisit sourceIndex occurrence index.1 index.2

@[simp] theorem postSettlementSocietyPointOfIndex_scenario
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current)
    (index : PostSettlementSocietyGrammarIndex) :
    (postSettlementSocietyPointOfIndexAt oldVisit sourceIndex occurrence
      index).scenario = index.1 := by
  cases index with
  | mk scenario face =>
      cases scenario <;> cases face <;> rfl

@[simp] theorem postSettlementSocietyPointOfIndex_face
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current)
    (index : PostSettlementSocietyGrammarIndex) :
    (postSettlementSocietyPointOfIndexAt oldVisit sourceIndex occurrence
      index).face = index.2 := by
  cases index with
  | mk scenario face =>
      cases scenario <;> cases face <;> rfl

theorem postSettlementSocietyPointOfIndex_injective
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    Function.Injective
      (postSettlementSocietyPointOfIndexAt oldVisit sourceIndex occurrence) := by
  intro left right equality
  apply Prod.ext
  · have scenarioEquality := congrArg
        SourceGeneratedClassifiedDependentFacePointAt.scenario equality
    rw [postSettlementSocietyPointOfIndex_scenario,
      postSettlementSocietyPointOfIndex_scenario] at scenarioEquality
    exact scenarioEquality
  · have faceEquality := congrArg
        SourceGeneratedClassifiedDependentFacePointAt.face equality
    rw [postSettlementSocietyPointOfIndex_face,
      postSettlementSocietyPointOfIndex_face] at faceEquality
    exact faceEquality

/-- One and only one installed unfolding contains both scenario restrictions. -/
def postSettlementSocietyTraceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    RootedAccountedUnfolding
      (PostSettlementSocietyPointAt oldVisit sourceIndex occurrence) :=
  let point := postSettlementSocietyPointOfIndexAt oldVisit sourceIndex occurrence
  DomainReuse.eventOccurrence
    (point (.actual, .ledger))
    (postSettlementSocietyGrammarIndices.tail.map point)

@[simp] theorem postSettlementSocietyTrace_trace
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    (postSettlementSocietyTraceAt oldVisit sourceIndex occurrence).trace =
      postSettlementSocietyGrammarIndices.map
        (postSettlementSocietyPointOfIndexAt oldVisit sourceIndex occurrence) := by
  rw [show postSettlementSocietyGrammarIndices =
      (.actual, .ledger) :: postSettlementSocietyGrammarIndices.tail by rfl]
  exact DomainReuse.eventOccurrence_trace _ _

theorem postSettlementSocietyTrace_nodup
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    (postSettlementSocietyTraceAt oldVisit sourceIndex occurrence
      ).trace.Nodup := by
  rw [postSettlementSocietyTrace_trace]
  exact postSettlementSocietyGrammarIndices_nodup.map
    (postSettlementSocietyPointOfIndex_injective oldVisit sourceIndex
      occurrence)

@[simp] theorem postSettlementSocietyTrace_length
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {current : (PostSettlementRenewalVAt oldVisit).Current}
    (occurrence : PostSettlementOccurrenceAt oldVisit sourceIndex current) :
    (postSettlementSocietyTraceAt oldVisit sourceIndex occurrence
      ).trace.length = 16 := by
  rw [postSettlementSocietyTrace_trace, List.length_map]
  exact postSettlementSocietyGrammarIndices_length

def postSettlementSocietyFamilyLaw
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeDependentFaceFamilyLaw
      (PostSettlementSourceAt oldVisit sourceIndex) where
  vocabulary := postSettlementSocietyVocabulary oldVisit sourceIndex
  traceAt := postSettlementSocietyTraceAt oldVisit sourceIndex
  traceNodup := postSettlementSocietyTrace_nodup oldVisit sourceIndex
  scenarioNonempty := by
    intro current occurrence scenario
    let index : PostSettlementSocietyGrammarIndex := (scenario, .ledger)
    let point := postSettlementSocietyPointOfIndexAt oldVisit sourceIndex
      occurrence index
    refine ⟨point, ?_, ?_⟩
    · rw [postSettlementSocietyTrace_trace]
      exact List.mem_map.mpr
        ⟨index, postSettlementSocietyGrammarIndex_mem scenario .ledger, rfl⟩
    · exact postSettlementSocietyPointOfIndex_scenario oldVisit sourceIndex
        occurrence index
  scenarioFaceExactlyOnce := by
    intro current occurrence scenario face
    let index : PostSettlementSocietyGrammarIndex := (scenario, face)
    let point := postSettlementSocietyPointOfIndexAt oldVisit sourceIndex
      occurrence index
    refine ⟨point, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [postSettlementSocietyTrace_trace]
        exact List.mem_map.mpr
          ⟨index, postSettlementSocietyGrammarIndex_mem scenario face, rfl⟩
      · exact postSettlementSocietyPointOfIndex_scenario oldVisit sourceIndex
          occurrence index
      · exact postSettlementSocietyPointOfIndex_face oldVisit sourceIndex
          occurrence index
    · intro candidate candidateExact
      rcases candidateExact with ⟨candidateMem, candidateScenario,
        candidateFace⟩
      rw [postSettlementSocietyTrace_trace] at candidateMem
      rcases List.mem_map.mp candidateMem with
        ⟨candidateIndex, _candidateIndexMem, candidateEq⟩
      have candidateIndexScenario : candidateIndex.1 = scenario := by
        have equality := congrArg
          SourceGeneratedClassifiedDependentFacePointAt.scenario candidateEq
        rw [postSettlementSocietyPointOfIndex_scenario] at equality
        exact equality.trans candidateScenario
      have candidateIndexFace : candidateIndex.2 = face := by
        have equality := congrArg
          SourceGeneratedClassifiedDependentFacePointAt.face candidateEq
        rw [postSettlementSocietyPointOfIndex_face] at equality
        exact equality.trans candidateFace
      have indexEq : candidateIndex = index := by
        apply Prod.ext
        · simpa [index] using candidateIndexScenario
        · simpa [index] using candidateIndexFace
      subst candidateIndex
      exact candidateEq.symm

end
end M14SourceGeneratedPostSettlementSocietyFaceTrace
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementSocietyFaceTrace.postSettlementSocietyFamilyLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementSocietyFaceTrace.postSettlementSocietyTrace_nodup
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementSocietyFaceTrace.postSettlementSocietyTrace_length
