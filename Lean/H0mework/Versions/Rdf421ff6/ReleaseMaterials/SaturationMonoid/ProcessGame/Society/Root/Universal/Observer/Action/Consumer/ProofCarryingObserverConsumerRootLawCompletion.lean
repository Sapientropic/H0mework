import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler
import H0mework.Versions.R2.Foundation.Inquiry.RevisionRecovery

/-!
# Proof-carrying completion of observer / consumer root law

This file enriches the existing four-way legislation compiler without adding
another authority carrier.  Presentation and rejection remain non-writing;
rejection exposes its exact generated submission as residual bearer.  The
installed-action class has a sequential-action leaf and a debt-admission leaf,
each exposing its first whole-ledger successor and generated next; the U8 class
exposes the exact same-row U8 realization.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UniversalRootGrammar

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery

universe u v w x

section

variable
    {N : WorldRelationNetwork.{u}}
    {V : ConstructiveRoot.Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    {scenario : recognition.law.vocabulary.Scenario}
    {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
    {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario
      Visible Output ClaimedEffect}
    {submissionProgram :
      SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {program : SourceNativeObserverConsumerLegislationProgramAt
      submissionProgram}
    {execution : SourceGeneratedObserverConsumerLegislationAt program}
    {disposition : SourceNativeObserverConsumerUseDispositionAt
      program.generatedSubmission}
    {inquiryOutput : SourceNativeInquiryCompilationAt
      root visit program.U7 program.calculus
      root.toAuthoritativeRoot.source.lawSurface
      sourceNativeObserverLegislationQuery
      (ULift.up.{u + 1, u} (root.emitted visit.current))
      program.entry program.entryAuthority}

/-- A lawful presentation, including a rooted inquiry answered by installed
law, has no world-writing branch. -/
structure LawfulPresentationNoWriteAt
    (compiled : SourceNativeCompiledObserverConsumerLegislationAt execution
      disposition inquiryOutput) : Type (max (u + 12) v w x) where
  branch : Nonempty compiled.LawfulPresentationBranchAt
  worldWritingEmpty : IsEmpty compiled.WorldWritingBranchAt

/-- Typed rejection exposes the exact program-generated occurrence as its
visible residual bearer while preserving that occurrence's root, whole-ledger
and generated-next factorization. -/
structure TypedRejectionVisibleResidualAt
    (compiled : SourceNativeCompiledObserverConsumerLegislationAt execution
      disposition inquiryOutput) : Type (max (u + 12) v w x) where
  branch : Nonempty compiled.RejectedBranchAt
  rejection : SourceNativeObserverConsumerRejectionAt
    program.generatedSubmission
  dispositionExact : disposition = .rejected rejection
  residualBearer : AnySourceGeneratedObserverConsumerSubmissionAt attempt
  residualBearerExact : residualBearer =
    SourceNativeObserverConsumerRejectionAt.residualBearer
      (generated := program.generatedSubmission)
  rootLedgerAndNextFactorize :
    type_of% program.generatedSubmission.rootLedgerAndNext_factorize
  worldWritingEmpty : IsEmpty compiled.WorldWritingBranchAt

/-- A writing sequential action retains the exact rooted authority, source
action, target first whole-ledger successor and target generated next. -/
structure RootedSequentialActionWholeLedgerNextAt
    (compiled : SourceNativeCompiledObserverConsumerLegislationAt execution
      disposition inquiryOutput) : Type (max (u + 12) v w x) where
  branch : Nonempty compiled.InstalledActionAt
  worldWriting : Nonempty compiled.WorldWritingBranchAt
  rooted : SourceNativeObserverConsumerRootedAuthorityAt
    program.generatedSubmission
  actionProgram : SourceNativeSequentialActualActionProgramAt
    root visit program.entry program.entryAuthority
  sourceEvent : ExactTemporalCausalRootEventAt
    root.toAuthoritativeRoot.toLedgerRoot visit
  action : SourceGeneratedSequentialActualActionAt actionProgram sourceEvent
  dispositionExact : disposition = .rooted rooted
  inquiryOutputExact : inquiryOutput = .actualAction action
  installedOutputExact :
    ((.actualAction action) : SourceNativeInquiryCompilationAt
      root visit program.U7 program.calculus
      root.toAuthoritativeRoot.source.lawSurface
      sourceNativeObserverLegislationQuery
      (ULift.up.{u + 1, u} (root.emitted visit.current))
      program.entry program.entryAuthority) =
        program.inquiryProgram.generate.output
  firstWholeLedgerWrite : type_of% action.target.firstSuccessor
  generatedNextExact : type_of% action.target.targetAnswerAndNext_next_eq

/-- A writing debt admission retains the exact rooted authority, source
admission, the fresh-row first write, the target first whole-ledger successor
and the target generated next. -/
structure RootedDebtAdmissionWholeLedgerNextAt
    (compiled : SourceNativeCompiledObserverConsumerLegislationAt execution
      disposition inquiryOutput) : Type (max (u + 12) v w x) where
  branch : Nonempty compiled.InstalledActionAt
  worldWriting : Nonempty compiled.WorldWritingBranchAt
  rooted : SourceNativeObserverConsumerRootedAuthorityAt
    program.generatedSubmission
  admissionProgram : SourceNativeDebtAdmissionActualActionProgramAt
    root visit program.entry program.entryAuthority
  sourceEvent : ExactTemporalCausalRootEventAt
    root.toAuthoritativeRoot.toLedgerRoot visit
  admission : SourceGeneratedDebtAdmissionActualActionAt admissionProgram
    sourceEvent
  dispositionExact : disposition = .rooted rooted
  inquiryOutputExact : inquiryOutput = .debtAdmission admission
  installedOutputExact :
    ((.debtAdmission admission) : SourceNativeInquiryCompilationAt
      root visit program.U7 program.calculus
      root.toAuthoritativeRoot.source.lawSurface
      sourceNativeObserverLegislationQuery
      (ULift.up.{u + 1, u} (root.emitted visit.current))
      program.entry program.entryAuthority) =
        program.inquiryProgram.generate.output
  freshRowFirstWrite : type_of% admission.target.admission
  firstWholeLedgerWrite : type_of% admission.target.firstSuccessor
  generatedNextExact : type_of% admission.target.targetAnswerAndNext_next_eq

/-- The installed-action class.  Both leaves write the world through rooted
authority, a source-generated action, a first whole-ledger successor and a
generated next. -/
inductive RootedActionWholeLedgerNextAt
    (compiled : SourceNativeCompiledObserverConsumerLegislationAt execution
      disposition inquiryOutput) : Type (max (u + 12) v w x)
  | sequential (leaf : RootedSequentialActionWholeLedgerNextAt compiled)
  | debtAdmission (leaf : RootedDebtAdmissionWholeLedgerNextAt compiled)

namespace RootedActionWholeLedgerNextAt

variable {compiled : SourceNativeCompiledObserverConsumerLegislationAt
  execution disposition inquiryOutput}

theorem branch :
    RootedActionWholeLedgerNextAt compiled →
      Nonempty compiled.InstalledActionAt
  | .sequential leaf => leaf.branch
  | .debtAdmission leaf => leaf.branch

theorem worldWriting :
    RootedActionWholeLedgerNextAt compiled →
      Nonempty compiled.WorldWritingBranchAt
  | .sequential leaf => leaf.worldWriting
  | .debtAdmission leaf => leaf.worldWriting

def rooted :
    RootedActionWholeLedgerNextAt compiled →
      SourceNativeObserverConsumerRootedAuthorityAt
        program.generatedSubmission
  | .sequential leaf => leaf.rooted
  | .debtAdmission leaf => leaf.rooted

theorem dispositionExact :
    (action : RootedActionWholeLedgerNextAt compiled) →
      disposition = .rooted action.rooted
  | .sequential leaf => leaf.dispositionExact
  | .debtAdmission leaf => leaf.dispositionExact

end RootedActionWholeLedgerNextAt

/-- The U8 writing leaf retains the rooted obstruction, exact failure, same
old-row entry, first revised whole-ledger write and both generated row-next
consumers.  Nothing here can be supplied after observing the compiler output. -/
structure ExactFailureSameRowConditionalU8At
    (compiled : SourceNativeCompiledObserverConsumerLegislationAt execution
      disposition inquiryOutput) : Type (max (u + 12) v w x) where
  branch : Nonempty compiled.SameOccurrenceU8At
  worldWriting : Nonempty compiled.WorldWritingBranchAt
  rooted : SourceNativeObserverConsumerRootedAuthorityAt
    program.generatedSubmission
  obstruction : N.ObstructionAt
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))
  gate : SourceNativeU7TheoryAuditAt program.calculus
    (program.calculus.generated obstruction).1
  failure : ActualExpressibilityFailure
    root.toAuthoritativeRoot.source.lawSurface obstruction
  core : SourceGeneratedInquiryU8RevisionCoreAt
    root visit program.U7 program.calculus
    root.toAuthoritativeRoot.source.lawSurface
    sourceNativeObserverLegislationQuery
    (ULift.up.{u + 1, u} (root.emitted visit.current))
    program.entry program.entryAuthority obstruction gate failure
  dispositionExact : disposition = .rooted rooted
  inquiryOutputExact : inquiryOutput =
    .requiresU8 obstruction gate failure core
  installedOutputExact :
    ((.requiresU8 obstruction gate failure core) :
      SourceNativeInquiryCompilationAt
        root visit program.U7 program.calculus
        root.toAuthoritativeRoot.source.lawSurface
        sourceNativeObserverLegislationQuery
        (ULift.up.{u + 1, u} (root.emitted visit.current))
        program.entry program.entryAuthority) =
      program.inquiryProgram.generate.output
  sameRow : type_of% core.rootEntry_eq
  cofaceFactorization : type_of% core.cofaceFactorization
  revisedFirstWholeLedgerWrite : type_of% core.revision.generate.firstWrite
  revisedOldRowNext :
    type_of% (generatedOldTargetAnswerAndNext core.revision)
  revisedNewRowNext :
    type_of% (generatedNewTargetAnswerAndNext core.revision)

/-- Rich four-class exhaustion.  This is a readout of the existing compiled
value, not a second outcome registry. -/
theorem rich_exhaustive_fourClasses
    (compiled : SourceNativeCompiledObserverConsumerLegislationAt execution
      disposition inquiryOutput) :
    Nonempty (LawfulPresentationNoWriteAt compiled) ∨
      Nonempty (TypedRejectionVisibleResidualAt compiled) ∨
        Nonempty (RootedActionWholeLedgerNextAt compiled) ∨
          Nonempty (ExactFailureSameRowConditionalU8At compiled) := by
  cases compiled with
  | observerPresentation =>
      exact .inl ⟨
        { branch := ⟨PUnit.unit⟩
          worldWritingEmpty := ⟨fun impossible => nomatch impossible⟩ }⟩
  | rejected rejection =>
      exact .inr (.inl ⟨
        { branch := ⟨PUnit.unit⟩
          rejection := rejection
          dispositionExact := rfl
          residualBearer :=
            SourceNativeObserverConsumerRejectionAt.residualBearer
              (generated := program.generatedSubmission)
          residualBearerExact := rfl
          rootLedgerAndNextFactorize :=
            program.generatedSubmission.rootLedgerAndNext_factorize
          worldWritingEmpty := ⟨fun impossible => nomatch impossible⟩ }⟩)
  | rootedAnswered _ _ _ _ =>
      exact .inl ⟨
        { branch := ⟨PUnit.unit⟩
          worldWritingEmpty := ⟨fun impossible => nomatch impossible⟩ }⟩
  | rootedU7Answered _ _ _ _ _ _ =>
      exact .inl ⟨
        { branch := ⟨PUnit.unit⟩
          worldWritingEmpty := ⟨fun impossible => nomatch impossible⟩ }⟩
  | rootedOldLanguageAnswered _ _ _ _ _ _ _ =>
      exact .inl ⟨
        { branch := ⟨PUnit.unit⟩
          worldWritingEmpty := ⟨fun impossible => nomatch impossible⟩ }⟩
  | installedAction rooted action outputExact =>
      exact .inr (.inr (.inl ⟨.sequential
        { branch := ⟨PUnit.unit⟩
          worldWriting := ⟨PUnit.unit⟩
          rooted := rooted
          actionProgram := _
          sourceEvent := _
          action := action
          dispositionExact := rfl
          inquiryOutputExact := rfl
          installedOutputExact := outputExact
          firstWholeLedgerWrite := action.target.firstSuccessor
          generatedNextExact := action.target.targetAnswerAndNext_next_eq }⟩))
  | installedDebtAdmission rooted admission outputExact =>
      exact .inr (.inr (.inl ⟨.debtAdmission
        { branch := ⟨PUnit.unit⟩
          worldWriting := ⟨PUnit.unit⟩
          rooted := rooted
          admissionProgram := _
          sourceEvent := _
          admission := admission
          dispositionExact := rfl
          inquiryOutputExact := rfl
          installedOutputExact := outputExact
          freshRowFirstWrite := admission.target.admission
          firstWholeLedgerWrite := admission.target.firstSuccessor
          generatedNextExact :=
            admission.target.targetAnswerAndNext_next_eq }⟩))
  | sameOccurrenceU8 rooted obstruction gate failure core outputExact =>
      exact .inr (.inr (.inr ⟨
        { branch := ⟨PUnit.unit⟩
          worldWriting := ⟨PUnit.unit⟩
          rooted := rooted
          obstruction := obstruction
          gate := gate
          failure := failure
          core := core
          dispositionExact := rfl
          inquiryOutputExact := rfl
          installedOutputExact := outputExact
          sameRow := core.rootEntry_eq
          cofaceFactorization := core.cofaceFactorization
          revisedFirstWholeLedgerWrite := core.revision.generate.firstWrite
          revisedOldRowNext := generatedOldTargetAnswerAndNext core.revision
          revisedNewRowNext := generatedNewTargetAnswerAndNext core.revision }⟩))

/-- Per-execution root-law completion: rich four-class exhaustion, exact
world-writing boundary and no fifth authority class. -/
structure SourceNativeRootLawCompleteAt
    (execution : SourceGeneratedObserverConsumerLegislationAt program) : Prop where
  richExhaustive :
    let compiled := compileSourceNativeObserverConsumerLegislationAt execution
    Nonempty (LawfulPresentationNoWriteAt compiled) ∨
      Nonempty (TypedRejectionVisibleResidualAt compiled) ∨
        Nonempty (RootedActionWholeLedgerNextAt compiled) ∨
          Nonempty (ExactFailureSameRowConditionalU8At compiled)
  noFifthClass :
    type_of% (compiledObserverConsumerLegislation_hasNoFifthClass execution)
  worldWritingIffActionOrU8 :
    type_of% (compileSourceNativeObserverConsumerLegislationAt execution
      ).worldWritingBranch_iff_action_or_u8
  worldWritingImpliesRooted :
    type_of% (compileSourceNativeObserverConsumerLegislationAt execution
      ).worldWritingBranch_implies_rooted
  presentationCannotWrite :
    type_of% (compileSourceNativeObserverConsumerLegislationAt execution
      ).presentation_worldWritingBranch_isEmpty
  rejectionCannotWrite :
    type_of% (compileSourceNativeObserverConsumerLegislationAt execution
      ).rejection_worldWritingBranch_isEmpty
  actionAndU8Disjoint :
    type_of% (compileSourceNativeObserverConsumerLegislationAt execution
      ).action_u8_disjoint

theorem sourceNativeRootLawComplete
    (execution : SourceGeneratedObserverConsumerLegislationAt program) :
    SourceNativeRootLawCompleteAt execution where
  richExhaustive :=
    rich_exhaustive_fourClasses
      (compileSourceNativeObserverConsumerLegislationAt execution)
  noFifthClass :=
    compiledObserverConsumerLegislation_hasNoFifthClass execution
  worldWritingIffActionOrU8 :=
    (compileSourceNativeObserverConsumerLegislationAt execution
      ).worldWritingBranch_iff_action_or_u8
  worldWritingImpliesRooted :=
    (compileSourceNativeObserverConsumerLegislationAt execution
      ).worldWritingBranch_implies_rooted
  presentationCannotWrite :=
    (compileSourceNativeObserverConsumerLegislationAt execution
      ).presentation_worldWritingBranch_isEmpty
  rejectionCannotWrite :=
    (compileSourceNativeObserverConsumerLegislationAt execution
      ).rejection_worldWritingBranch_isEmpty
  actionAndU8Disjoint :=
    (compileSourceNativeObserverConsumerLegislationAt execution
      ).action_u8_disjoint

/-- U8 is permanently conditionally available: whenever the deterministic
compiler has selected its U8 leaf, that leaf exposes the complete exact
failure/same-row/first-write/next package.  It does not assert that U8 fires on
non-U8 executions. -/
def SourceNativeU8AvailableAt
    (execution : SourceGeneratedObserverConsumerLegislationAt program) : Prop :=
  let compiled := compileSourceNativeObserverConsumerLegislationAt execution
  Nonempty compiled.SameOccurrenceU8At →
    Nonempty (ExactFailureSameRowConditionalU8At compiled)

theorem sourceNativeU8Available
    (execution : SourceGeneratedObserverConsumerLegislationAt program) :
    SourceNativeU8AvailableAt execution := by
  let compiled := compileSourceNativeObserverConsumerLegislationAt execution
  intro selected
  change Nonempty (ExactFailureSameRowConditionalU8At compiled)
  rcases rich_exhaustive_fourClasses compiled with
    presented | rejected | action | revised
  · rcases presented with ⟨facts⟩
    have write := (sourceNativeRootLawComplete execution
      ).worldWritingIffActionOrU8.mpr (.inr selected)
    exact False.elim
      (facts.worldWritingEmpty.false (Classical.choice write))
  · rcases rejected with ⟨facts⟩
    have write := (sourceNativeRootLawComplete execution
      ).worldWritingIffActionOrU8.mpr (.inr selected)
    exact False.elim
      (facts.worldWritingEmpty.false (Classical.choice write))
  · rcases action with ⟨facts⟩
    exact False.elim
      ((sourceNativeRootLawComplete execution).actionAndU8Disjoint.false
        ⟨Classical.choice facts.branch, Classical.choice selected⟩)
  · exact revised

end

end UniversalRootGrammar
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.rich_exhaustive_fourClasses
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeRootLawComplete
#print axioms SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeU8Available
