import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.SourceNativeDependentFaceLaw

/-!
# Source-native universal Society root grammar

The grammar is a readout of the one dependent-face occurrence installed at
the living root.  It first audits every classified point by folding that
exact occurrence, then compiles any scenario by another fold of the same
tree.  A scenario is therefore a restriction coordinate, never a second
occurrence and never a second write authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UniversalRootGrammar

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u

/-! ## The complete occurrence audit -/

/-- The audit algebra retains the current classified point and concatenates
the complete audits of every source-generated child. -/
def sourceGeneratedDependentFaceAuditAlgebra {Point : Type u}
    (point : Point) (children : List (List Point)) : List Point :=
  point :: children.flatten

/-- Full audit of one exact source-generated occurrence. -/
def sourceGeneratedDependentFaceAudit {Point : Type u}
    (occurrence : RootedAccountedUnfolding Point) : List Point :=
  occurrence.fold sourceGeneratedDependentFaceAuditAlgebra

private theorem candidateValues_trace_flatten_eq_traceBranches
    {Point : Type u} (branches : AccountedBranches Point) :
    (RootedAccountedUnfolding.candidateValues
      RootedAccountedUnfolding.trace branches).flatten =
        RootedAccountedUnfolding.traceBranches branches :=
  AccountedBranches.rec
    (motive_1 := fun _occurrence => True)
    (motive_2 := fun childBranches =>
      (RootedAccountedUnfolding.candidateValues
        RootedAccountedUnfolding.trace childBranches).flatten =
          RootedAccountedUnfolding.traceBranches childBranches)
    (fun _origin _childBranches _branchResult => True.intro)
    rfl
    (fun head tail _headResult tailResult => by
      change RootedAccountedUnfolding.trace head ++
          (RootedAccountedUnfolding.candidateValues
            RootedAccountedUnfolding.trace tail).flatten =
        RootedAccountedUnfolding.trace head ++
          RootedAccountedUnfolding.traceBranches tail
      exact congrArg
        (fun suffix => RootedAccountedUnfolding.trace head ++ suffix)
        tailResult)
    branches

private theorem trace_commutes_with_dependentFaceAuditAlgebra
    {Point : Type u} (origin : Point)
    (branches : AccountedBranches Point) :
    RootedAccountedUnfolding.trace
        (RootedAccountedUnfolding.occur origin branches) =
      sourceGeneratedDependentFaceAuditAlgebra origin
        (RootedAccountedUnfolding.candidateValues
          RootedAccountedUnfolding.trace branches) := by
  change origin :: RootedAccountedUnfolding.traceBranches branches =
    origin :: (RootedAccountedUnfolding.candidateValues
      RootedAccountedUnfolding.trace branches).flatten
  exact congrArg (List.cons origin)
    (candidateValues_trace_flatten_eq_traceBranches branches).symm

/-- The fold audit is exactly the kernel's complete provenance trace.  This
is a direct `fold_unique` factorization, not a second recursive observer. -/
theorem sourceGeneratedDependentFaceAudit_eq_trace
    {Point : Type u} (occurrence : RootedAccountedUnfolding Point) :
    sourceGeneratedDependentFaceAudit occurrence = occurrence.trace := by
  exact
    (RootedAccountedUnfolding.fold_unique
      sourceGeneratedDependentFaceAuditAlgebra
      RootedAccountedUnfolding.trace
      trace_commutes_with_dependentFaceAuditAlgebra occurrence).symm

namespace SourceNativeDependentFaceFamilyRecognitionAt

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)

/-- Full outcome-preserving audit of the one installed trace. -/
def fullAuditAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    List (recognition.PointAt visit) :=
  sourceGeneratedDependentFaceAudit (recognition.traceAt visit)

theorem fullAudit_eq_trace
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    recognition.fullAuditAt visit = (recognition.traceAt visit).trace :=
  sourceGeneratedDependentFaceAudit_eq_trace _

/-- Membership in the fold audit is exactly occurrence membership.  Since a
classified point carries its `outcome`, this equality preserves every passed
witness and every complete failed bundle without rebuilding either. -/
theorem point_mem_fullAudit_iff
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (point : recognition.PointAt visit) :
    point ∈ recognition.fullAuditAt visit ↔
      point ∈ (recognition.traceAt visit).trace := by
  rw [recognition.fullAudit_eq_trace visit]

/-- A scenario is selected only by filtering the full audit of the already
fixed occurrence. -/
def scenarioRestrictionAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) :
    List (recognition.PointAt visit) :=
  letI : DecidableEq recognition.law.vocabulary.Scenario :=
    recognition.law.vocabulary.scenarioDecidableEq
  (recognition.fullAuditAt visit).filter
    (fun point => decide (point.scenario = scenario))

theorem point_mem_scenarioRestriction_iff
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario)
    (point : recognition.PointAt visit) :
    point ∈ recognition.scenarioRestrictionAt visit scenario ↔
      point ∈ (recognition.traceAt visit).trace ∧
        point.scenario = scenario := by
  unfold scenarioRestrictionAt
  constructor
  · intro membership
    have filtered := List.mem_filter.mp membership
    exact
      ⟨(recognition.point_mem_fullAudit_iff visit point).1 filtered.1,
        @of_decide_eq_true (point.scenario = scenario)
          (recognition.law.vocabulary.scenarioDecidableEq _ _) filtered.2⟩
  · intro property
    apply List.mem_filter.mpr
    exact
      ⟨(recognition.point_mem_fullAudit_iff visit point).2 property.1,
        @decide_eq_true (point.scenario = scenario)
          (recognition.law.vocabulary.scenarioDecidableEq _ _) property.2⟩

/-- Native carrier of a scenario restriction.  Its membership and scenario
equality come directly from the pre-emitter trace law, independently of the
filtered-list readout above. -/
structure SourceNativeScenarioRestrictionPointAt
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) : Type u where
  point : recognition.PointAt visit
  occurrenceMembership : point ∈ (recognition.traceAt visit).trace
  scenarioExact : point.scenario = scenario

/-- Every scenario has a native restriction point before any list observer
is applied. -/
theorem scenarioRestrictionPoint_nonempty
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) :
    Nonempty (recognition.SourceNativeScenarioRestrictionPointAt
      visit scenario) := by
  rcases recognition.scenario_nonempty visit scenario with
    ⟨point, point_mem, scenarioExact⟩
  exact ⟨⟨point, point_mem, scenarioExact⟩⟩

/-- Every source-declared scenario has a real point in its restriction. -/
theorem scenarioRestriction_nonempty
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) :
    Nonempty { point : recognition.PointAt visit //
      point ∈ recognition.scenarioRestrictionAt visit scenario } := by
  rcases recognition.scenario_nonempty visit scenario with
    ⟨point, point_mem, scenarioExact⟩
  exact ⟨⟨point,
    (recognition.point_mem_scenarioRestriction_iff
      visit scenario point).2 ⟨point_mem, scenarioExact⟩⟩⟩

/-- Exact once coverage survives restriction: every scenario/bearing-face
pair occurs once and only once in the selected audit. -/
theorem scenarioFace_exactlyOnce_inRestriction
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario)
    (face : recognition.law.vocabulary.FaceAt
      (root.emitted visit.current)) :
    ∃! point : recognition.PointAt visit,
      point ∈ recognition.scenarioRestrictionAt visit scenario ∧
        point.face = face := by
  rcases recognition.scenario_face_exactlyOnce visit scenario face with
    ⟨point, point_property, point_unique⟩
  refine ⟨point, ?_, ?_⟩
  · exact
      ⟨(recognition.point_mem_scenarioRestriction_iff
          visit scenario point).2
          ⟨point_property.1, point_property.2.1⟩,
        point_property.2.2⟩
  · intro candidate candidate_property
    apply point_unique candidate
    have candidate_mem :=
      (recognition.point_mem_scenarioRestriction_iff
        visit scenario candidate).1 candidate_property.1
    exact ⟨candidate_mem.1, candidate_mem.2, candidate_property.2⟩

end SourceNativeDependentFaceFamilyRecognitionAt

/-! ## Scenario compiler on the same trace -/

/-- A passed point retained by one scenario compilation. -/
structure SourceGeneratedPassedDependentFaceAuditAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) : Type u where
  point : recognition.PointAt visit
  scenarioExact : point.scenario = scenario
  passed : recognition.law.vocabulary.PassedAt
    (root.emitted visit.current) point.scenario point.face

/-- A failed point retained with its bearer, source ownership, consumer and
disposition bundle. -/
structure SourceGeneratedFailedDependentFaceAuditAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) : Type u where
  point : recognition.PointAt visit
  scenarioExact : point.scenario = scenario
  failed : SourceGeneratedFailedDependentFaceAt recognition.law.vocabulary
    (root.emitted visit.current) point.scenario point.face

/-- Total disposition of one scenario restriction.  The positive branch
retains every passed point; the negative branch retains a real typed failure. -/
inductive SourceNativeUniversalRootGrammarDispositionAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) : Type u
  | canonical (passed : List
      (SourceGeneratedPassedDependentFaceAuditAt recognition visit scenario))
  | failed
      (failure : SourceGeneratedFailedDependentFaceAuditAt recognition visit
        scenario)

namespace SourceNativeUniversalRootGrammarDispositionAt

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
  {visit : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot}
  {scenario : recognition.law.vocabulary.Scenario}

/-- Left-to-right combination of already folded child dispositions. -/
def combine :
    SourceNativeUniversalRootGrammarDispositionAt recognition visit scenario →
    SourceNativeUniversalRootGrammarDispositionAt recognition visit scenario →
      SourceNativeUniversalRootGrammarDispositionAt recognition visit scenario
  | .failed failure, _ => .failed failure
  | .canonical _, .failed failure => .failed failure
  | .canonical left, .canonical right => .canonical (left ++ right)

end SourceNativeUniversalRootGrammarDispositionAt

/-- One constructor algebra for a fixed scenario.  Points of other scenarios
are ignored as restrictions, while all children still run through the same
fold. -/
def sourceNativeUniversalRootGrammarAlgebraAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario)
    (point : recognition.PointAt visit)
    (children : List
      (SourceNativeUniversalRootGrammarDispositionAt recognition visit
        scenario)) :
    SourceNativeUniversalRootGrammarDispositionAt recognition visit
      scenario := by
  letI : DecidableEq recognition.law.vocabulary.Scenario :=
    recognition.law.vocabulary.scenarioDecidableEq
  let descendants := children.foldr
    SourceNativeUniversalRootGrammarDispositionAt.combine (.canonical [])
  exact if scenarioExact : point.scenario = scenario then
    match point.outcome with
    | .inl passed =>
        SourceNativeUniversalRootGrammarDispositionAt.combine
          (.canonical [⟨point, scenarioExact, passed⟩]) descendants
    | .inr failed => .failed ⟨point, scenarioExact, failed⟩
  else descendants

/-- Public compiler: one scenario fold of the already installed trace. -/
def compileUniversalSocietyRootGrammarAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) :
    SourceNativeUniversalRootGrammarDispositionAt recognition visit
      scenario :=
  (recognition.traceAt visit).fold
    (sourceNativeUniversalRootGrammarAlgebraAt recognition visit scenario)

/-- Any constructor-compatible compiler is forced to the scenario fold of
the installed occurrence. -/
theorem compileUniversalSocietyRootGrammarAt_unique
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario)
    (candidate : RootedAccountedUnfolding (recognition.PointAt visit) →
      SourceNativeUniversalRootGrammarDispositionAt recognition visit
        scenario)
    (commutes : ∀ (point : recognition.PointAt visit)
      (branches : AccountedBranches (recognition.PointAt visit)),
      candidate (.occur point branches) =
        sourceNativeUniversalRootGrammarAlgebraAt recognition visit scenario
          point (RootedAccountedUnfolding.candidateValues candidate
            branches)) :
    candidate (recognition.traceAt visit) =
      compileUniversalSocietyRootGrammarAt recognition visit scenario :=
  RootedAccountedUnfolding.fold_unique
    (sourceNativeUniversalRootGrammarAlgebraAt recognition visit scenario)
    candidate commutes (recognition.traceAt visit)

/-- Two scenario compilers are literally restrictions/folds of one and the
same installed trace. -/
theorem scenarioCompilers_shareInstalledTrace
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (left right : recognition.law.vocabulary.Scenario) :
    compileUniversalSocietyRootGrammarAt recognition visit left =
        (recognition.traceAt visit).fold
          (sourceNativeUniversalRootGrammarAlgebraAt recognition visit left) ∧
      compileUniversalSocietyRootGrammarAt recognition visit right =
        (recognition.traceAt visit).fold
          (sourceNativeUniversalRootGrammarAlgebraAt recognition visit right) :=
  ⟨rfl, rfl⟩

/-! ## Root-owned facade and authority factorization -/

/-- Payload-free certificate that the universal grammar was read from the
installed trace.  Every public value below is recomputed from `recognition`. -/
inductive SourceGeneratedUniversalRootGrammarAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) : Type
  | generated

def sourceGeneratedUniversalRootGrammarAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) :
    SourceGeneratedUniversalRootGrammarAt recognition visit scenario :=
  .generated

namespace SourceGeneratedUniversalRootGrammarAt

variable {N : WorldRelationNetwork.{u}}
  {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
  {visit : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot}
  {scenario : recognition.law.vocabulary.Scenario}
  (grammar : SourceGeneratedUniversalRootGrammarAt recognition visit scenario)

def fullAudit
    (_grammar : SourceGeneratedUniversalRootGrammarAt recognition visit
      scenario) : List (recognition.PointAt visit) :=
  recognition.fullAuditAt visit

def restriction
    (_grammar : SourceGeneratedUniversalRootGrammarAt recognition visit
      scenario) : List (recognition.PointAt visit) :=
  recognition.scenarioRestrictionAt visit scenario

def disposition
    (_grammar : SourceGeneratedUniversalRootGrammarAt recognition visit
      scenario) :
    SourceNativeUniversalRootGrammarDispositionAt recognition visit
      scenario :=
  compileUniversalSocietyRootGrammarAt recognition visit scenario

def exactEvent
    (_grammar : SourceGeneratedUniversalRootGrammarAt recognition visit
      scenario) :=
  recognition.exactEventAt visit

def wholeLedgerWriteBack
    (_grammar : SourceGeneratedUniversalRootGrammarAt recognition visit
      scenario) :=
  recognition.wholeLedgerWriteBackAt visit

def generatedNext
    (_grammar : SourceGeneratedUniversalRootGrammarAt recognition visit
      scenario) : SourceNativeAuthoritativeRootCurrentAt N :=
  recognition.generatedNextAt visit

theorem fullAudit_eq_installedTrace :
    grammar.fullAudit = (recognition.traceAt visit).trace :=
  recognition.fullAudit_eq_trace visit

theorem disposition_eq_installedTraceFold :
    grammar.disposition =
      (recognition.traceAt visit).fold
        (sourceNativeUniversalRootGrammarAlgebraAt recognition visit
          scenario) :=
  rfl

/-- Whole-ledger output is definitionally the source compiler image of the
same emitted occurrence; failure bundles cannot select a sibling ledger. -/
theorem wholeLedgerWriteBack_eq_sourceCompiler :
    grammar.wholeLedgerWriteBack =
      root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
        (root.emitted visit.current) :=
  rfl

/-- The installed trace coordinate, exact root event, whole-ledger write and
generated next current all factor through the existing living-root answer. -/
theorem rootLedgerAndNext_factorize :
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          recognition.rootProjection)
        (recognition.installedFiberAt visit) ∧
      HEq grammar.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      evolution.nextCurrent = grammar.generatedNext := by
  exact recognition.installedTraceAuthority_factorizes visit

/-- Non-actual scenarios have no actual-write authority. -/
theorem searchActualWriteAuthority_isEmpty
    (search : scenario ≠ recognition.law.vocabulary.actualScenario) :
    IsEmpty (SourceNativeScenarioActualWriteAuthorityAt
      recognition.law.vocabulary scenario) :=
  searchScenario_actualWriteAuthority_isEmpty recognition.law.vocabulary
    scenario search

/-- Their only ledger action is the canonical identity disposition at the
same observed occurrence. -/
def searchIdentityDisposition
    (_search : scenario ≠ recognition.law.vocabulary.actualScenario) :
    @SourceNativeSearchIdentityDispositionAt N V
      root.toAuthoritativeRoot.toLedgerRoot.source visit.current
        (root.emitted visit.current) :=
  @sourceNativeSearchIdentityDispositionAt N V
    root.toAuthoritativeRoot.toLedgerRoot.source visit.current
      (root.emitted visit.current)

end SourceGeneratedUniversalRootGrammarAt

/-! ## Exact deletion control -/

structure ExactScenarioRestrictionDeletionAt
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) : Prop where
  deleted : IsEmpty
    (recognition.SourceNativeScenarioRestrictionPointAt visit scenario)

theorem scenarioRestrictionDeletion_isFalse
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeDependentFaceFamilyRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (scenario : recognition.law.vocabulary.Scenario) :
    ¬ ExactScenarioRestrictionDeletionAt recognition visit scenario :=
  fun deletion =>
    (recognition.scenarioRestrictionPoint_nonempty visit scenario).elim
      (fun point => deletion.deleted.false point)

end UniversalRootGrammar
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceGeneratedDependentFaceAudit_eq_trace
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.compileUniversalSocietyRootGrammarAt_unique
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceGeneratedUniversalRootGrammarAt.rootLedgerAndNext_factorize
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.scenarioRestrictionDeletion_isFalse
