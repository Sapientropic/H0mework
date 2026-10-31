import H0mework.Society.Renewal.InstalledRenewalProjection
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Renewal.RootInstalledRenewalRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.AI.AIStandingRenewalRegression

/-!
# M8 source-installed renewal projection regression

This regression reuses the existing operational-separation root source and
its exact continuing ledger row.  Before installing an emitter, the complete
authority source is uplifted with the already source-generated AI renewal
payload.  The resulting local face, temporal row, operational standing,
responsibility consumer, root coordinate and living next are all restrictions
of the same occurrence.

The concrete AI event is only a direct consumer.  The production law remains
quantified over arbitrary source occurrences and arbitrary finite, cofinal or
post-cofinal temporal visits.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8SourceInstalledRenewalProjectionRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal
open ConstructiveRoot.OperationalSearchSourceNativeRootRegression
open M8RootInstalledRenewalRegression
open M8AIStandingRenewalRegression
open AI.TraceWitnessedStanding
open DomainReuse

abbrev BaseRoot := root false

/-- Regression-only universal installer over the already existing one-row
root source.  The local domain parameters and seed are arbitrary; the exact
root row and successor are always compiled from the source occurrence rather
than imported from a temporal visit. -/
def singletonRootRenewalLaw
    {LocalSource LocalState Seed : Type}
    {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
    (localGame : SaturationMonoid.ProcessGame occurrenceOf)
    (SeedAt : LocalSource → LocalState → Seed → Prop)
    (ConsumerAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt localGame.source → Type)
    (sourceSeed : SourceSeed occurrenceOf Seed SeedAt localGame.source)
    (consumer : ConsumerAt sourceSeed)
    (disposition : DispositionAt sourceSeed) :
    SourceNativeRenewalProjectionLaw
      BaseRoot.toAuthoritativeRoot.toLedgerRoot.source
      localGame Seed SeedAt ConsumerAt DispositionAt where
  ActiveAt := fun {_current} _occurrence => PUnit
  InactiveAt := fun {_current} _occurrence => PEmpty
  classify := fun {_current} _occurrence => .inl PUnit.unit
  compile := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support
    cases event
    let source := BaseRoot.toAuthoritativeRoot.toLedgerRoot.source
    let exactOccurrence := (⟨(), ()⟩ :
      source.source.toRootSource.actual.OccurrenceAt ())
    let exactEntry : OpenResponsibilityAt N
        (source.source.toRootSource.account.supportOf exactOccurrence) :=
      entry false
    let exactRow :=
      source.ledgerCompiler.canonicalGeneratedEntry_of_terminalOrTransferred
        exactOccurrence exactEntry (by rfl)
    let exactSuccessor :=
      (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
        (source.ledgerCompiler.compile exactOccurrence)).get (by rfl)
    exact RootRestrictedRenewalPayloadAt.generate sourceSeed consumer disposition
      exactEntry exactRow exactSuccessor
  sourceSeed_reflects_rootOccurrence := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      _leftActive _rightActive _seedEq
    cases leftCurrent
    cases rightCurrent
    rcases leftOccurrence with ⟨leftSupport, leftEvent⟩
    rcases rightOccurrence with ⟨rightSupport, rightEvent⟩
    cases leftSupport
    cases rightSupport
    cases leftEvent
    cases rightEvent
    rfl

/-- Build the complete source identity first and install the emitter only
after the renewal law has become a projection coordinate. -/
def rootWithRenewalLaw
    {LocalSource LocalState Seed : Type}
    {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
    {localGame : SaturationMonoid.ProcessGame occurrenceOf}
    {SeedAt : LocalSource → LocalState → Seed → Prop}
    {ConsumerAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt localGame.source → Type}
    (law : SourceNativeRenewalProjectionLaw
      BaseRoot.toAuthoritativeRoot.toLedgerRoot.source
      localGame Seed SeedAt ConsumerAt DispositionAt) :
    SourceNativeLivingRootClosure N V where
  source :=
    { base := withRenewalProjection BaseRoot.toAuthoritativeRoot.source law
      terminalHandoff :=
        (withRenewalProjection BaseRoot.toAuthoritativeRoot.source law)
          |>.emptyFaithfulTerminalHandoff
            (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := emitted
  compiler_commutes := fun _ => rfl

def initialVisitWithRenewalLaw
    {LocalSource LocalState Seed : Type}
    {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
    {localGame : SaturationMonoid.ProcessGame occurrenceOf}
    {SeedAt : LocalSource → LocalState → Seed → Prop}
    {ConsumerAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt localGame.source → Type}
    (law : SourceNativeRenewalProjectionLaw
      BaseRoot.toAuthoritativeRoot.toLedgerRoot.source
      localGame Seed SeedAt ConsumerAt DispositionAt) :
    SourceNativeTemporalVisitAt
      (rootWithRenewalLaw law).toAuthoritativeRoot.toLedgerRoot :=
  .finite (rootWithRenewalLaw law).toAuthoritativeRoot.toRoot.initialVisit

def recognitionWithRenewalLaw
    {LocalSource LocalState Seed : Type}
    {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
    {localGame : SaturationMonoid.ProcessGame occurrenceOf}
    {SeedAt : LocalSource → LocalState → Seed → Prop}
    {ConsumerAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt localGame.source → Type}
    (law : SourceNativeRenewalProjectionLaw
      BaseRoot.toAuthoritativeRoot.toLedgerRoot.source
      localGame Seed SeedAt ConsumerAt DispositionAt) :
    SourceNativeRenewalRecognitionAt (rootWithRenewalLaw law)
      localGame Seed SeedAt ConsumerAt DispositionAt where
  law := law
  installation := renewalComponent
    BaseRoot.toAuthoritativeRoot.source law

def installedAtInitialVisit
    {LocalSource LocalState Seed : Type}
    {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
    {localGame : SaturationMonoid.ProcessGame occurrenceOf}
    {SeedAt : LocalSource → LocalState → Seed → Prop}
    {ConsumerAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt localGame.source → Type}
    (law : SourceNativeRenewalProjectionLaw
      BaseRoot.toAuthoritativeRoot.toLedgerRoot.source
      localGame Seed SeedAt ConsumerAt DispositionAt)
    (active : law.ActiveAt
      ((rootWithRenewalLaw law).emitted
        (initialVisitWithRenewalLaw law).current))
    (classified : law.classify
      ((rootWithRenewalLaw law).emitted
        (initialVisitWithRenewalLaw law).current) = .inl active) :
    SourceInstalledRenewalAt (recognitionWithRenewalLaw law)
      (initialVisitWithRenewalLaw law) :=
  SourceInstalledRenewalAt.generate active classified

/-- The source-first AI renewal law is total on the existing root occurrence
family.  Its payload includes the exact canonical row and whole-ledger
successor; neither is supplied by the later temporal consumer. -/
def aiRenewalLaw : SourceNativeRenewalProjectionLaw
    BaseRoot.toAuthoritativeRoot.toLedgerRoot.source
    threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
    AIConsumerAt AIDispositionAt :=
  singletonRootRenewalLaw threeAgentProcessGame MultiAgent.seedAt
    AIConsumerAt AIDispositionAt aiRenewalSeed
    aiResponsibilityConsumer aiRenewalDisposition

/-- Complete source identity with the renewal coordinate installed before an
emitter is supplied. -/
def aiRenewalAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection BaseRoot.toAuthoritativeRoot.source aiRenewalLaw

/-- Same underlying root source/compiler and emitter, with one additional
source-fixed restriction coordinate.  This is not a second social root
ontology or ledger. -/
def aiRenewalRoot : SourceNativeLivingRootClosure N V where
  source :=
    { base := aiRenewalAuthoritySource
      terminalHandoff :=
        aiRenewalAuthoritySource.emptyFaithfulTerminalHandoff
          (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := emitted
  compiler_commutes := fun _ => rfl

def aiRenewalVisit : SourceNativeTemporalVisitAt
    aiRenewalRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite aiRenewalRoot.toAuthoritativeRoot.toRoot.initialVisit

def aiRenewalRecognition : SourceNativeRenewalRecognitionAt
    aiRenewalRoot threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
    AIConsumerAt AIDispositionAt where
  law := aiRenewalLaw
  installation := renewalComponent
    BaseRoot.toAuthoritativeRoot.source aiRenewalLaw

def aiSourceInstalledRenewal :
    SourceInstalledRenewalAt aiRenewalRecognition aiRenewalVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def aiRootInstalledLocalFace :=
  aiSourceInstalledRenewal.localFace MultiAgent.lineageOf aiStandingOf

theorem local_seed_is_exact_ai_seed :
    aiRootInstalledLocalFace.sourceSeed = aiRenewalSeed :=
  rfl

theorem local_consumer_is_exact_ai_consumer :
    aiRootInstalledLocalFace.responsibilityConsumer =
      aiResponsibilityConsumer :=
  rfl

theorem local_disposition_is_exact_ai_disposition :
    aiRootInstalledLocalFace.exactDisposition = aiRenewalDisposition :=
  rfl

theorem root_entry_is_exact_source_payload_entry :
    aiSourceInstalledRenewal.operationalAuthority.exactEventMembership =
      aiSourceInstalledRenewal.temporalSelectedRow :=
  rfl

theorem root_budget_not_refilled :
    aiSourceInstalledRenewal.operationalAuthority.operationalStanding.progressBudget ≤
      aiSourceInstalledRenewal.payload.sourceEntry.progressBudget :=
  aiSourceInstalledRenewal.operationalAuthority.progressBudget_not_refilled

theorem source_projection_is_exact_active_payload :
    aiRenewalRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (aiRenewalRoot.emitted aiRenewalVisit.current) =
      (.inl ⟨aiSourceInstalledRenewal.active,
        aiSourceInstalledRenewal.payload⟩ :
        SourceNativeProjectionFiberAt
          aiRenewalRecognition.law.toProjectionLaw PUnit.unit
          (aiRenewalRoot.emitted aiRenewalVisit.current)) :=
  aiSourceInstalledRenewal.componentOutcome_eq_activePayload

theorem root_answer_projection_and_next_are_one_compiler_image :
    let evolution := aiRenewalRoot.canonicalCausalAnswerAndNext
      (ULift.up aiRenewalVisit)
    evolution.generated =
        aiRenewalRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          aiRenewalVisit ∧
      HEq (evolution.generated.projectionOutcome
          aiRenewalRecognition.rootProjection)
        (aiRenewalRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (aiRenewalRoot.emitted aiRenewalVisit.current)) ∧
      evolution.nextCurrent =
        aiRenewalRoot.generatedNextCurrentAt aiRenewalVisit :=
  aiSourceInstalledRenewal.rootAnswerAndNext_factorizes

/-- Compile-time no-post-hoc control: the old root does not definitionally
contain the new renewal coordinate. -/
theorem base_root_has_no_posthoc_renewal_coordinate : True := by
  fail_if_success
    exact ({
      law := aiRenewalLaw
      installation := renewalComponent
        BaseRoot.toAuthoritativeRoot.source aiRenewalLaw
    } : SourceNativeRenewalRecognitionAt
      BaseRoot threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
      AIConsumerAt AIDispositionAt)
  trivial

/-- Whole direct consumer: source-first component, exact local face, temporal
row, operational standing, independent root consumer and generated next. -/
structure SourceInstalledRenewalCertificate : Type 3 where
  installed : SourceInstalledRenewalAt aiRenewalRecognition aiRenewalVisit
  localFace : AILocalRenewalFace
  localSeedExact : localFace.sourceSeed = aiRenewalSeed
  rootConsumer : RenewalResponsibilityConsumerAt
    installed.operationalAuthority
  rootBudgetNotRefilled :
    installed.operationalAuthority.operationalStanding.progressBudget ≤
      installed.payload.sourceEntry.progressBudget
  sourceProjectionExact :
    aiRenewalRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (aiRenewalRoot.emitted aiRenewalVisit.current) =
      (.inl ⟨installed.active, installed.payload⟩ :
        SourceNativeProjectionFiberAt
          aiRenewalRecognition.law.toProjectionLaw PUnit.unit
          (aiRenewalRoot.emitted aiRenewalVisit.current))
  answerProjectionNextExact :
    let evolution := aiRenewalRoot.canonicalCausalAnswerAndNext
      (ULift.up aiRenewalVisit)
    evolution.generated =
        aiRenewalRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          aiRenewalVisit ∧
      HEq (evolution.generated.projectionOutcome
          aiRenewalRecognition.rootProjection)
        (aiRenewalRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (aiRenewalRoot.emitted aiRenewalVisit.current)) ∧
      evolution.nextCurrent =
        aiRenewalRoot.generatedNextCurrentAt aiRenewalVisit

def sourceInstalledRenewalDirectConsumer :
    SourceInstalledRenewalCertificate where
  installed := aiSourceInstalledRenewal
  localFace := aiRootInstalledLocalFace
  localSeedExact := local_seed_is_exact_ai_seed
  rootConsumer := aiSourceInstalledRenewal.rootResponsibilityConsumer
  rootBudgetNotRefilled := root_budget_not_refilled
  sourceProjectionExact := source_projection_is_exact_active_payload
  answerProjectionNextExact :=
    root_answer_projection_and_next_are_one_compiler_image

end M8SourceInstalledRenewalProjectionRegression
end Society
end ProcessGame
end SaturationMonoid
