import H0mework.Foundation.Authority.Representation
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Source-native dependent-face families

One lower actual occurrence generates one finite `RootedAccountedUnfolding`.
Actual play and search are scenario restrictions of that one trace; a
scenario can never select a second tree or a second living-root write.

Each trace point is already classified by the pre-emitter source law.  It
contains either its passed witness or its complete typed failed bundle.  The
trace itself is installed as one ordinary component of the existing root
projection law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UniversalRootGrammar

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u

/-- Source-fixed vocabulary for one dependent-face calculation trace.

`actualScenario` is the sole scenario allowed to own an actual-write token.
Every other scenario receives the identity-disposition interface below. -/
structure SourceNativeDependentFaceVocabulary
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  Scenario : Type u
  scenarioDecidableEq : DecidableEq Scenario
  actualScenario : Scenario
  FaceAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current → Type u
  PassedAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    Scenario → FaceAt occurrence → Type u
  ResidualBearerAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    Scenario → FaceAt occurrence → Type u
  SourceOwnershipAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    (scenario : Scenario) →
    (face : FaceAt occurrence) →
    ResidualBearerAt occurrence scenario face → Type u
  ConsumerAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    (scenario : Scenario) →
    (face : FaceAt occurrence) →
    ResidualBearerAt occurrence scenario face → Type u
  DispositionAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    (scenario : Scenario) →
    (face : FaceAt occurrence) →
    (bearer : ResidualBearerAt occurrence scenario face) →
    ConsumerAt occurrence scenario face bearer → Type u

/-- A real failed point.  Its whole-ledger image is not a field: the exact
source compiler is reapplied to `occurrence` below. -/
structure SourceGeneratedFailedDependentFaceAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (vocabulary : SourceNativeDependentFaceVocabulary source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (scenario : vocabulary.Scenario)
    (face : vocabulary.FaceAt occurrence) : Type u where
  passedEmpty : IsEmpty (vocabulary.PassedAt occurrence scenario face)
  residualBearer : vocabulary.ResidualBearerAt occurrence scenario face
  sourceOwned : vocabulary.SourceOwnershipAt occurrence scenario face
    residualBearer
  consumer : vocabulary.ConsumerAt occurrence scenario face residualBearer
  disposition : vocabulary.DispositionAt occurrence scenario face
    residualBearer consumer

namespace SourceGeneratedFailedDependentFaceAt

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource N V}
  {vocabulary : SourceNativeDependentFaceVocabulary source}
  {current : V.Current}
  {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
  {scenario : vocabulary.Scenario}
  {face : vocabulary.FaceAt occurrence}
  (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
    scenario face)

include failed in
/-- A failed classification cannot simultaneously be reported as passed. -/
theorem falselyReportedPass_isEmpty :
    IsEmpty (vocabulary.PassedAt occurrence scenario face) :=
  failed.passedEmpty

include failed in
theorem passed_failed_disjoint
    (passed : vocabulary.PassedAt occurrence scenario face) : False :=
  failed.passedEmpty.false passed

def wholeLedgerWriteBack
    (_failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) :=
  source.ledgerCompiler.compile occurrence

def localDisposition
    (_failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face)
    (entry : OpenResponsibilityAt N
      (source.source.toRootSource.account.supportOf occurrence)) :
    LedgerEntryDispositionAt N entry :=
  (source.ledgerCompiler.compile occurrence).entryDisposition entry

@[simp] theorem localDisposition_eq
    (entry : OpenResponsibilityAt N
      (source.source.toRootSource.account.supportOf occurrence)) :
    failed.localDisposition entry =
      (source.ledgerCompiler.compile occurrence).entryDisposition
        entry :=
  rfl

end SourceGeneratedFailedDependentFaceAt

/-- One point of the unique trace.  Scenario is part of point identity, not
an argument used to generate a second trace. -/
structure SourceGeneratedClassifiedDependentFacePointAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (vocabulary : SourceNativeDependentFaceVocabulary source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    Type u where
  scenario : vocabulary.Scenario
  face : vocabulary.FaceAt occurrence
  outcome : vocabulary.PassedAt occurrence scenario face ⊕
    SourceGeneratedFailedDependentFaceAt vocabulary occurrence scenario face

/-- The one payload installed at the source projection coordinate.

`actualScenario` is stored as authority-bearing data and accompanied by its
exact source-law equality.  Consequently a trace installation cannot be
reused while silently relabelling which scenario owns actual-write authority. -/
structure SourceNativeInstalledDependentFaceTraceAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (vocabulary : SourceNativeDependentFaceVocabulary source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    Type u where
  actualScenario : vocabulary.Scenario
  actualScenarioExact : actualScenario = vocabulary.actualScenario
  trace : RootedAccountedUnfolding
    (SourceGeneratedClassifiedDependentFacePointAt vocabulary occurrence)

namespace SourceNativeInstalledDependentFaceTraceAt

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource N V}
  {vocabulary : SourceNativeDependentFaceVocabulary source}
  {current : V.Current}
  {occurrence : source.source.toRootSource.actual.OccurrenceAt current}

/-- Any two payload values of the same installed carrier agree on actual
authority; the equality is forced by the source vocabulary, not the caller. -/
theorem actualScenario_unique
    (left right : SourceNativeInstalledDependentFaceTraceAt vocabulary
      occurrence) :
    left.actualScenario = right.actualScenario :=
  left.actualScenarioExact.trans right.actualScenarioExact.symm

end SourceNativeInstalledDependentFaceTraceAt

/-- One pre-emitter law generates one trace and proves exact coverage.

Every scenario is represented.  More strongly, every scenario/bearing-face
pair occurs exactly once in the trace. -/
structure SourceNativeDependentFaceFamilyLaw
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  vocabulary : SourceNativeDependentFaceVocabulary source
  traceAt : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      RootedAccountedUnfolding
        (SourceGeneratedClassifiedDependentFacePointAt vocabulary occurrence)
  traceNodup : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      (traceAt occurrence).trace.Nodup
  scenarioNonempty : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    (scenario : vocabulary.Scenario) →
      ∃ point ∈ (traceAt occurrence).trace,
        point.scenario = scenario
  scenarioFaceExactlyOnce : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    (scenario : vocabulary.Scenario) →
    (face : vocabulary.FaceAt occurrence) →
      ∃! point : SourceGeneratedClassifiedDependentFacePointAt
          vocabulary occurrence,
        point ∈ (traceAt occurrence).trace ∧
          point.scenario = scenario ∧ point.face = face

namespace SourceNativeDependentFaceFamilyLaw

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource N V}

/-- Source-generated installed carrier at one exact occurrence. -/
def installedTraceAt (law : SourceNativeDependentFaceFamilyLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeInstalledDependentFaceTraceAt law.vocabulary occurrence where
  actualScenario := law.vocabulary.actualScenario
  actualScenarioExact := rfl
  trace := law.traceAt occurrence

/-- The unique complete trace is the sole payload of one installed
projection coordinate. -/
def toProjectionLaw (law : SourceNativeDependentFaceFamilyLaw source) :
    SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _active =>
    SourceNativeInstalledDependentFaceTraceAt law.vocabulary occurrence
  project := fun _ {_current} occurrence _active =>
    law.installedTraceAt occurrence

end SourceNativeDependentFaceFamilyLaw

/-- Recognition that a living root was born with the trace component. -/
structure SourceNativeDependentFaceFamilyRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) : Type (u + 2) where
  law : SourceNativeDependentFaceFamilyLaw
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt law.toProjectionLaw
    root.toAuthoritativeRoot.source.projectionLaw

namespace SourceNativeDependentFaceFamilyRecognitionAt

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)

def rootProjection :
    root.toAuthoritativeRoot.source.projectionLaw.Projection :=
  recognition.installation.embed PUnit.unit

/-- The installed payload, including the exact actual-scenario authority. -/
def installedPayloadAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeInstalledDependentFaceTraceAt recognition.law.vocabulary
      (root.emitted visit.current) :=
  recognition.law.installedTraceAt (root.emitted visit.current)

def installedActualScenarioAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    recognition.law.vocabulary.Scenario :=
  (recognition.installedPayloadAt visit).actualScenario

theorem installedActualScenario_eq
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    recognition.installedActualScenarioAt visit =
      recognition.law.vocabulary.actualScenario :=
  (recognition.installedPayloadAt visit).actualScenarioExact

/-- An attempted relabel supplies a scenario claimed to be the installed
actual authority while also claiming it differs from the source law. -/
structure ExactInstalledActualScenarioRelabelAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type u where
  relabelled : recognition.law.vocabulary.Scenario
  installedAsActual : relabelled = recognition.installedActualScenarioAt visit
  differsFromSource : relabelled ≠
    recognition.law.vocabulary.actualScenario

theorem installedActualScenarioRelabel_isEmpty
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    IsEmpty (recognition.ExactInstalledActualScenarioRelabelAt visit) :=
  ⟨fun relabel => relabel.differsFromSource
    (relabel.installedAsActual.trans
      (recognition.installedActualScenario_eq visit))⟩

abbrev PointAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :=
  SourceGeneratedClassifiedDependentFacePointAt recognition.law.vocabulary
    (root.emitted visit.current)

/-- The one trace shared by every scenario restriction. -/
def traceAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    RootedAccountedUnfolding (recognition.PointAt visit) :=
  (recognition.installedPayloadAt visit).trace

theorem traceAt_eq_lawTrace
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    recognition.traceAt visit =
    recognition.law.traceAt (root.emitted visit.current) :=
  rfl

theorem trace_nodup
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    (recognition.traceAt visit).trace.Nodup :=
  recognition.law.traceNodup (root.emitted visit.current)

theorem scenario_nonempty
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) :
    ∃ point ∈ (recognition.traceAt visit).trace,
      point.scenario = scenario :=
  recognition.law.scenarioNonempty (root.emitted visit.current) scenario

theorem scenario_face_exactlyOnce
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario)
    (face : recognition.law.vocabulary.FaceAt
      (root.emitted visit.current)) :
    ∃! point : recognition.PointAt visit,
      point ∈ (recognition.traceAt visit).trace ∧
        point.scenario = scenario ∧ point.face = face :=
  recognition.law.scenarioFaceExactlyOnce
    (root.emitted visit.current) scenario face

def installedFiberAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeProjectionFiberAt recognition.law.toProjectionLaw PUnit.unit
      (root.emitted visit.current) :=
  .inl ⟨PUnit.unit, recognition.installedPayloadAt visit⟩

theorem componentOutcome_eq_installedFiber
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    recognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (root.emitted visit.current) = recognition.installedFiberAt visit :=
  rfl

def exactEventAt
    (_recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot
      visit :=
  root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit

def wholeLedgerWriteBackAt
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :=
  (recognition.exactEventAt visit).wholeLedgerWriteBack

def generatedNextAt
    (_recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  root.generatedNextCurrentAt visit

theorem installedTraceAuthority_factorizes
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          recognition.rootProjection)
        (recognition.installedFiberAt visit) ∧
      HEq (recognition.wholeLedgerWriteBackAt visit)
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      evolution.nextCurrent = recognition.generatedNextAt visit := by
  dsimp only
  have factorization :=
    (root.canonicalCausalAnswerAndNext
      (ULift.up visit)).installedSubsystemAuthority_factorizes
        recognition.installation PUnit.unit
  exact
    ⟨factorization.1,
      factorization.2.1.trans
        (heq_of_eq (recognition.componentOutcome_eq_installedFiber visit)),
      HEq.rfl, factorization.2.2⟩

end SourceNativeDependentFaceFamilyRecognitionAt

/-! ## Actual-write / search-identity separation -/

/-- Actual-write authority belongs only to the source-declared actual
scenario.  It contains no write payload. -/
inductive SourceNativeScenarioActualWriteAuthorityAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (vocabulary : SourceNativeDependentFaceVocabulary source)
    : vocabulary.Scenario → Type u
  | actual : SourceNativeScenarioActualWriteAuthorityAt vocabulary
      vocabulary.actualScenario

theorem searchScenario_actualWriteAuthority_isEmpty
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (vocabulary : SourceNativeDependentFaceVocabulary source)
    (scenario : vocabulary.Scenario)
    (search : scenario ≠ vocabulary.actualScenario) :
    IsEmpty (SourceNativeScenarioActualWriteAuthorityAt vocabulary scenario) :=
  ⟨fun authority => by
    cases authority
    exact search rfl⟩

/-- A search restriction has only the identity disposition of the source
ledger at the observed occurrence.  It cannot select the actual root write. -/
def SourceNativeSearchIdentityDispositionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    Type u :=
  let ledger : CompleteLiveLedgerAt N :=
    ⟨source.source.toRootSource.account.supportOf occurrence⟩
  LedgerWriteEvolutionAt N ledger ledger

def sourceNativeSearchIdentityDispositionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeSearchIdentityDispositionAt occurrence :=
  LedgerWriteEvolutionAt.identity
    ⟨source.source.toRootSource.account.supportOf occurrence⟩

/-! ## Exact deletion controls -/

structure ExactFailedFaceResidualBearerDeletionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {vocabulary : SourceNativeDependentFaceVocabulary source}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {scenario : vocabulary.Scenario}
    {face : vocabulary.FaceAt occurrence}
    (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) : Prop where
  deleted : IsEmpty
    (vocabulary.ResidualBearerAt occurrence scenario face)

theorem failedFaceResidualBearerDeletion_isFalse
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {vocabulary : SourceNativeDependentFaceVocabulary source}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {scenario : vocabulary.Scenario}
    {face : vocabulary.FaceAt occurrence}
    (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) :
    ¬ ExactFailedFaceResidualBearerDeletionAt failed :=
  fun deletion => deletion.deleted.false failed.residualBearer

structure ExactFailedFaceSourceOwnershipDeletionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {vocabulary : SourceNativeDependentFaceVocabulary source}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {scenario : vocabulary.Scenario}
    {face : vocabulary.FaceAt occurrence}
    (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) : Prop where
  deleted : IsEmpty (vocabulary.SourceOwnershipAt occurrence scenario face
    failed.residualBearer)

theorem failedFaceSourceOwnershipDeletion_isFalse
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {vocabulary : SourceNativeDependentFaceVocabulary source}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {scenario : vocabulary.Scenario}
    {face : vocabulary.FaceAt occurrence}
    (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) :
    ¬ ExactFailedFaceSourceOwnershipDeletionAt failed :=
  fun deletion => deletion.deleted.false failed.sourceOwned

structure ExactFailedFaceConsumerDeletionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {vocabulary : SourceNativeDependentFaceVocabulary source}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {scenario : vocabulary.Scenario}
    {face : vocabulary.FaceAt occurrence}
    (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) : Prop where
  deleted : IsEmpty (vocabulary.ConsumerAt occurrence scenario face
    failed.residualBearer)

theorem failedFaceConsumerDeletion_isFalse
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {vocabulary : SourceNativeDependentFaceVocabulary source}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {scenario : vocabulary.Scenario}
    {face : vocabulary.FaceAt occurrence}
    (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) :
    ¬ ExactFailedFaceConsumerDeletionAt failed :=
  fun deletion => deletion.deleted.false failed.consumer

structure ExactFailedFaceDispositionDeletionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {vocabulary : SourceNativeDependentFaceVocabulary source}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {scenario : vocabulary.Scenario}
    {face : vocabulary.FaceAt occurrence}
    (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) : Prop where
  deleted : IsEmpty (vocabulary.DispositionAt occurrence scenario face
    failed.residualBearer failed.consumer)

theorem failedFaceDispositionDeletion_isFalse
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {vocabulary : SourceNativeDependentFaceVocabulary source}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    {scenario : vocabulary.Scenario}
    {face : vocabulary.FaceAt occurrence}
    (failed : SourceGeneratedFailedDependentFaceAt vocabulary occurrence
      scenario face) :
    ¬ ExactFailedFaceDispositionDeletionAt failed :=
  fun deletion => deletion.deleted.false failed.disposition

structure ExactDependentFaceTraceDeletionAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Prop where
  deleted : IsEmpty (recognition.PointAt visit)

theorem dependentFaceTraceDeletion_isFalse
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    ¬ ExactDependentFaceTraceDeletionAt recognition visit :=
  fun deletion => deletion.deleted.false (recognition.traceAt visit).root

end UniversalRootGrammar
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeDependentFaceFamilyRecognitionAt.installedTraceAuthority_factorizes
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeDependentFaceFamilyRecognitionAt.installedActualScenarioRelabel_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.searchScenario_actualWriteAuthority_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceGeneratedFailedDependentFaceAt.falselyReportedPass_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.failedFaceDispositionDeletion_isFalse
