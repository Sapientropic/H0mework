import H0mework.Foundation.Inquiry.Protocol

/-!
# Source-native root inquiry engine

This kernel executes the U7-first inquiry foundation as one source process.
`Engine.ask` is the raw compiler readout.  Reality authority is added only
by `SourceNativeInquiryRuntime`, whose reachable-state tick seals this
readout; answer, receipt and next are dependent restrictions of that token.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootInquiryCompletion

open ObstructionGeneratedMinimalCoface
open TypedSemanticWorldNetworkU8
open TypedSemanticWorldNetworkU8Lifecycle
open TypedSemanticWorldNetworkU8Recovery

universe u

namespace SourceGeneratedInquiryU8RevisionAt

private def oldRowAnswerAndNext
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {state : RootInquiryStateAt N V} {query : state.Query}
    {obstruction : N.ObstructionAt state.support}
    {u7Gate : state.U7RequestsTheoryAuditAt obstruction}
    {failure : ActualExpressibilityFailure state.oldTheory obstruction}
    (completion : SourceGeneratedInquiryU8RevisionAt
      state query obstruction u7Gate failure) :=
  generatedOldTargetAnswerAndNext completion.revision

private def newRowAnswerAndNext
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {state : RootInquiryStateAt N V} {query : state.Query}
    {obstruction : N.ObstructionAt state.support}
    {u7Gate : state.U7RequestsTheoryAuditAt obstruction}
    {failure : ActualExpressibilityFailure state.oldTheory obstruction}
    (completion : SourceGeneratedInquiryU8RevisionAt
      state query obstruction u7Gate failure) :=
  generatedNewTargetAnswerAndNext completion.revision

/-- Full U8 receipt: initial coface universal factorization, first-write
realization, and both live-row answer-and-next tokens. -/
abbrev CofaceAnswerAndNextReceiptAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {state : RootInquiryStateAt N V} {query : state.Query}
    {obstruction : N.ObstructionAt state.support}
    {u7Gate : state.U7RequestsTheoryAuditAt obstruction}
    {failure : ActualExpressibilityFailure state.oldTheory obstruction}
    (completion : SourceGeneratedInquiryU8RevisionAt
      state query obstruction u7Gate failure) :=
  (FaithfulCofaceMorphism
        (root_obstruction_generates_minimal_coface completion.frontier.rooted)
        completion.revision.generate.toAdmissibleMinimalCoface ×
      SourceGeneratedAttachedCofaceRealizationAt completion.revision.generate) ×
    (SourceNativeLivingCausalEntryAnswerAndNextAt
        completion.revision.generate.newLivingRoot
        (oldFirstWriteSuccessor completion.revision).targetVisit
        (oldFirstWriteSuccessor completion.revision).targetEntry
        (oldFirstWriteTargetAuthority completion.revision) ×
      SourceNativeLivingCausalEntryAnswerAndNextAt
        completion.revision.generate.newLivingRoot
        (newFirstWriteSuccessor completion.revision).targetVisit
        (newFirstWriteSuccessor completion.revision).targetEntry
        (newFirstWriteTargetAuthority completion.revision))

private def cofaceAnswerAndNextReceipt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {state : RootInquiryStateAt N V} {query : state.Query}
    {obstruction : N.ObstructionAt state.support}
    {u7Gate : state.U7RequestsTheoryAuditAt obstruction}
    {failure : ActualExpressibilityFailure state.oldTheory obstruction}
    (completion : SourceGeneratedInquiryU8RevisionAt
      state query obstruction u7Gate failure) :
    completion.CofaceAnswerAndNextReceiptAt :=
  factorizesThroughInitialCofaceAnswerAndNext completion.revision

end SourceGeneratedInquiryU8RevisionAt

namespace SourceGeneratedInquiryU8CompletionAt

private def answerReadout
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {base : RootInquiryStateAt N V} {query : base.Query}
    {obstruction : N.ObstructionAt base.support}
    {u7Gate : base.U7RequestsTheoryAuditAt obstruction}
    {failure : ActualExpressibilityFailure base.oldTheory obstruction}
    (generated : SourceGeneratedInquiryU8CompletionAt
      base query obstruction u7Gate failure) : generated.AnswerAt :=
  generated.revisionReceipt.cofaceAnswer

end SourceGeneratedInquiryU8CompletionAt

/-- Full source law at one engine state.  The complete direct/U7/U8 result is
already the root-installed image of `base.compileInquiry`; there is no second
gearbox field. -/
structure RootInquiryEngineStateAt
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 12) where
  private mk ::
  base : RootInquiryStateAt N V

/-- Build one complete inquiry source state.  Every branch payload is already
inside the source-native compiler image authenticated by `compilationFaceAt`. -/
def RootInquiryEngineStateAt.create
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : RootInquiryStateAt N V) :
    RootInquiryEngineStateAt N V :=
  ⟨base⟩

namespace RootInquiryEngineStateAt

/-- The complete compiler image, including any U8 realization, is indexed by
one exact temporal root occurrence. -/
theorem generatedCompilation_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (state : RootInquiryEngineStateAt N V) (query : state.base.Query) :
    let face := state.base.compilationFaceAt query
    let generated := state.base.root.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit state.base.visit
    HEq
      (state.base.root.toAuthoritativeRoot.source.projectionLaw.project
        face.projection generated.occurrence face.active)
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := state.base.entryAt query)
        (query := query)
        (event := state.base.emitInquiry query)
        (audit := (state.base.compileInquiry query).audit)
        (state.base.compileInquiry query).answerReadout) ∧
      (state.base.root.toAuthoritativeRoot.toLedgerRoot
        |>.exactTemporalCausalEventAt state.base.visit) = generated := by
  dsimp only
  exact ⟨(state.base.compilationFaceAt query).installedAuthority_factorizes,
    rfl⟩

end RootInquiryEngineStateAt

/-- Heterogeneous authoritative current used only as the erasure target of
the process registry.  A revised U8 root may change both network and
vocabulary, so equality has to retain the network index. -/
structure AnyAuthoritativeRootCurrent : Type (u + 4) where
  N : WorldRelationNetwork.{u}
  current : SourceNativeAuthoritativeRootCurrentAt N

/-- Existential state presentation.  The query source, U7 calculus, theory,
root, and exact temporal current are one process-state identity. -/
structure RootInquiryStatePresentation : Type (u + 13) where
  N : WorldRelationNetwork.{u}
  V : Vocabulary.{u}
  state : RootInquiryEngineStateAt N V

namespace RootInquiryStatePresentation

abbrev Query (state : RootInquiryStatePresentation) : Type u :=
  state.state.base.Query

def erase (state : RootInquiryStatePresentation) :
    AnyAuthoritativeRootCurrent :=
  ⟨state.N,
    ⟨state.V, state.state.base.root.toAuthoritativeRoot,
      state.state.base.visit⟩⟩

end RootInquiryStatePresentation

/-- Internal gearbox receipt.  U7 runs first.  Only its theory-audit demand
may enter the theory audit, and only an exact old-language expression
and realization failure may open the fixed-root U8 coface.

The constructors are intentionally not the public API.  They are emitted by
the engine process compiler and retained inside the exact transition. -/
inductive InternalInquiryResolutionAt
    (state : RootInquiryStatePresentation.{u})
    (query : state.Query) : Type (u + 12)
  | directlyAnswered
      (answerFace : SourceNativeRootSemanticFaceAt
        state.state.base.root state.state.base.visit)
      (consumer : SourceNativeInquiryAnswerConsumerAt
        query (state.state.base.emitInquiry query)
          (state.state.base.entryAt query) answerFace) :
      InternalInquiryResolutionAt state query
  | u7Answered
      (obstruction : state.N.ObstructionAt state.state.base.support)
      (disposition : state.state.base.U7AnswersAt obstruction)
      (answerFace : SourceNativeRootSemanticFaceAt
        state.state.base.root state.state.base.visit)
      (consumer : SourceNativeInquiryAnswerConsumerAt
        query (state.state.base.emitInquiry query)
          (state.state.base.entryAt query) answerFace) :
      InternalInquiryResolutionAt state query
  | oldLanguageAnswered
      (obstruction : state.N.ObstructionAt state.state.base.support)
      (u7Gate : state.state.base.U7RequestsTheoryAuditAt obstruction)
      (answer : OldLanguageAnswerAt state.state.base.oldTheory
        obstruction)
      (answerFace : SourceNativeRootSemanticFaceAt
        state.state.base.root state.state.base.visit)
      (consumer : SourceNativeInquiryAnswerConsumerAt
        query (state.state.base.emitInquiry query)
          (state.state.base.entryAt query) answerFace) :
      InternalInquiryResolutionAt state query
  | actualAction
      {program : SourceNativeSequentialActualActionProgramAt
        state.state.base.root state.state.base.visit
          (state.state.base.entryAt query)
          (state.state.base.authorityAt query)}
      {sourceEvent : ExactTemporalCausalRootEventAt
        state.state.base.root.toAuthoritativeRoot.toLedgerRoot
          state.state.base.visit}
      (generated : SourceGeneratedSequentialActualActionAt
        program sourceEvent) :
      InternalInquiryResolutionAt state query
  | revised
      (obstruction : state.N.ObstructionAt state.state.base.support)
      (u7Gate : state.state.base.U7RequestsTheoryAuditAt obstruction)
      (failure : ActualExpressibilityFailure state.state.base.oldTheory
        obstruction)
      (generated : SourceGeneratedInquiryU8CompletionAt
        state.state.base query obstruction u7Gate failure) :
      InternalInquiryResolutionAt state query

/-- Pure presentation of an inquiry branch already selected by the private
source compiler.  It has no map back into `InternalInquiryResolutionAt`. -/
inductive InquiryResolutionKind
  | directlyAnswered
  | u7Answered
  | oldLanguageAnswered
  | actualAction
  | revised

/-- Canonical gearbox compiler.  Its event index is already the fixed root
occurrence; U8 is invoked only by the exact `requiresU8` compiler image. -/
private def RootInquiryStatePresentation.resolve
    (state : RootInquiryStatePresentation.{u}) (query : state.Query) :
    InternalInquiryResolutionAt state query :=
  let base := state.state.base
  match base.compileInquiry query with
  | .answered answerFace consumer =>
      .directlyAnswered answerFace consumer
  | .u7Answered obstruction disposition answerFace consumer =>
      .u7Answered obstruction disposition answerFace consumer
  | .oldLanguageAnswered obstruction gate answer answerFace consumer =>
      .oldLanguageAnswered obstruction gate answer answerFace consumer
  | .actualAction generated => .actualAction generated
  | .requiresU8 obstruction gate failure generated =>
      .revised obstruction gate failure generated

/-- The exact inquiry compilation consumed by `resolve` is the installed face
of the same authoritative temporal occurrence. -/
theorem RootInquiryStatePresentation.resolveCompilation_factorizes
    (state : RootInquiryStatePresentation.{u}) (query : state.Query) :
    let face := state.state.base.compilationFaceAt query
    let generated := state.state.base.root.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit state.state.base.visit
    HEq
      (state.state.base.root.toAuthoritativeRoot.source.projectionLaw.project
        face.projection generated.occurrence face.active)
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := state.state.base.entryAt query)
        (query := query)
        (event := state.state.base.emitInquiry query)
        (audit := (state.state.base.compileInquiry query).audit)
        (state.state.base.compileInquiry query).answerReadout) := by
  dsimp only
  exact (state.state.base.compilationFaceAt query).installedAuthority_factorizes

namespace InternalInquiryResolutionAt

/-- U8 never precedes U7.  Every revised resolution retains the exact
source-generated U7 theory-audit gate that opened the revision path. -/
def U7GateBeforeU8At
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query) : Type u :=
  match resolution with
  | .directlyAnswered _ _ => PUnit
  | .u7Answered _ _ _ _ => PUnit
  | .oldLanguageAnswered obstruction _ _ _ _ =>
      SourceNativeU7TheoryAuditAt state.state.base.calculus
        (state.state.base.u7Event obstruction)
  | .actualAction _ => PUnit
  | .revised obstruction _ _ _ =>
      SourceNativeU7TheoryAuditAt state.state.base.calculus
        (state.state.base.u7Event obstruction)

def u7GateBeforeU8
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query) :
    resolution.U7GateBeforeU8At := by
  cases resolution with
  | directlyAnswered _ _ => exact PUnit.unit
  | u7Answered _ _ _ _ => exact PUnit.unit
  | oldLanguageAnswered _ gate _ _ _ => exact gate
  | actualAction _ => exact PUnit.unit
  | revised _ gate _ _ => exact gate

/-- The answer presentation is derived from the actual root face selected by
this resolution.  Different branches may expose different restriction types;
there is no language-independent result type beside the occurrence. -/
def AnswerAt
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query) : Type u :=
  match resolution with
  | .directlyAnswered face _ => face.Restriction
  | .u7Answered _ _ face _ => face.Restriction
  | .oldLanguageAnswered _ _ _ face _ => face.Restriction
  | .actualAction generated => generated.target.Answer
  | .revised _ _ _ generated =>
      generated.AnswerAt

private def answer
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query)
    (_generated_eq : resolution = state.resolve query) :
    resolution.AnswerAt := by
  cases resolution with
  | directlyAnswered face _ => exact face.rootRead
  | u7Answered _ _ face _ => exact face.rootRead
  | oldLanguageAnswered _ _ _ face _ => exact face.rootRead
  | actualAction generated => exact generated.answer
  | revised _ _ _ generated => exact generated.answerReadout

/-- Branch-specific ledger and consumer receipt generated by the inquiry
occurrence. -/
def BranchReceiptAt
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query) : Type (u + 3) :=
  match resolution with
  | .directlyAnswered face _ =>
      SourceNativeInquiryAnswerConsumerAt
          query (state.state.base.emitInquiry query)
            (state.state.base.entryAt query) face ×
        SourceNativeLivingCausalEntryAnswerAndNextAt
          state.state.base.root state.state.base.visit
          (state.state.base.entryAt query)
          (state.state.base.authorityAt query)
  | .u7Answered _ _ face _ =>
      SourceNativeInquiryAnswerConsumerAt
          query (state.state.base.emitInquiry query)
            (state.state.base.entryAt query) face ×
        SourceNativeLivingCausalEntryAnswerAndNextAt
          state.state.base.root state.state.base.visit
          (state.state.base.entryAt query)
          (state.state.base.authorityAt query)
  | .oldLanguageAnswered obstruction _ _ face _ =>
      SourceNativeInquiryAnswerConsumerAt
          query (state.state.base.emitInquiry query)
            (state.state.base.entryAt query) face ×
        (OldLanguageAnswerAt state.state.base.oldTheory obstruction ×
          SourceNativeLivingCausalEntryAnswerAndNextAt
            state.state.base.root state.state.base.visit
              (state.state.base.entryAt query)
              (state.state.base.authorityAt query))
  | .actualAction generated =>
      generated.target.Receipt generated.answer
  | .revised _ _ _ generated =>
      let revisionReceipt := generated.revisionReceipt
      revisionReceipt.CofaceAnswerAndNextReceiptAt

/-- Complete receipt: the exact temporal root occurrence together with the
branch-specific ledger and consumer readout. -/
def ReceiptAt
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query) : Type (u + 3) :=
  ExactTemporalCausalRootEventAt
      state.state.base.root.toAuthoritativeRoot.toLedgerRoot
      state.state.base.visit ×
    resolution.BranchReceiptAt

private def branchReceipt
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query)
    (_generated_eq : resolution = state.resolve query) :
    resolution.BranchReceiptAt := by
  cases resolution with
  | directlyAnswered _ consumer =>
      exact ⟨consumer, state.state.base.oldAnswerAndNext query⟩
  | u7Answered _ _ _ consumer =>
      exact ⟨consumer, state.state.base.oldAnswerAndNext query⟩
  | oldLanguageAnswered _ _ oldAnswer _ consumer =>
      exact ⟨consumer, oldAnswer, state.state.base.oldAnswerAndNext query⟩
  | actualAction generated => exact generated.receipt
  | revised _ _ _ generated =>
      let revisionReceipt := generated.revisionReceipt
      exact revisionReceipt.cofaceAnswerAndNextReceipt

private def receipt
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query)
    (generated_eq : resolution = state.resolve query) :
    resolution.ReceiptAt :=
  ⟨state.state.base.root.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt state.state.base.visit,
    resolution.branchReceipt generated_eq⟩

/-- Root current actually generated after the answer.  The caller cannot
select whether the network remains old or becomes revised. -/
private def nextRootCurrent
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query)
    (_generated_eq : resolution = state.resolve query) :
    AnyAuthoritativeRootCurrent :=
  match resolution with
  | .directlyAnswered _ _ =>
      ⟨state.N, (state.state.base.oldAnswerAndNext query).nextCurrent⟩
  | .u7Answered _ _ _ _ =>
      ⟨state.N, (state.state.base.oldAnswerAndNext query).nextCurrent⟩
  | .oldLanguageAnswered _ _ _ _ _ =>
      ⟨state.N, (state.state.base.oldAnswerAndNext query).nextCurrent⟩
  | .actualAction generated =>
      ⟨generated.target.TargetN,
        generated.target.targetAnswerAndNext.nextCurrent⟩
  | .revised _ _ _ generated =>
      ⟨generated.revisionReceipt.revision.generate.NewN,
        (generatedNewTargetAnswerAndNext
          generated.revisionReceipt.revision).nextCurrent⟩

end InternalInquiryResolutionAt

/-- One process node is either inquiry-ready or the local interface has
answered one exact prior query.  The latter has no query fibre, but its world
current is definitionally the prior occurrence's generated target; no caller
may install an arbitrary dormant current and call it local completion. -/
inductive RootInquiryProcessNode : Type (u + 14)
  | active (state : RootInquiryStatePresentation.{u})
  | answered
      (state : RootInquiryStatePresentation.{u})
      (query : state.Query)

namespace RootInquiryProcessNode

def Query (node : RootInquiryProcessNode.{u}) : Type u :=
  match node with
  | .active state => state.Query
  | .answered _ _ => PEmpty

def erase (node : RootInquiryProcessNode.{u}) : AnyAuthoritativeRootCurrent.{u} :=
  match node with
  | .active state => state.erase
  | .answered state query =>
      InternalInquiryResolutionAt.nextRootCurrent (state.resolve query) rfl

/-- Local inquiry completion erases to the retained query's generated target. -/
@[simp] theorem answered_erases_to_generated
    (state : RootInquiryStatePresentation.{u}) (query : state.Query) :
    (RootInquiryProcessNode.answered state query).erase =
      InternalInquiryResolutionAt.nextRootCurrent (state.resolve query) rfl :=
  rfl

def ResolutionAt
    (node : RootInquiryProcessNode.{u}) (query : node.Query) : Type (u + 12) :=
  match node with
  | .active state => InternalInquiryResolutionAt state query
  | .answered _ _ => nomatch query

/-- Read only the outer constructor of a generated resolution.  The exact
obstruction, failure, receipt, answer, and next remain in the dependent
resolution value. -/
def resolutionKind
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query) : InquiryResolutionKind :=
  match node with
  | .active _ =>
      match resolution with
      | .directlyAnswered .. => .directlyAnswered
      | .u7Answered .. => .u7Answered
      | .oldLanguageAnswered .. => .oldLanguageAnswered
      | .actualAction .. => .actualAction
      | .revised .. => .revised
  | .answered _ _ => nomatch query

private def resolve
    (node : RootInquiryProcessNode.{u}) (query : node.Query) :
    node.ResolutionAt query :=
  match node with
  | .active state => state.resolve query
  | .answered _ _ => nomatch query

def AnswerAt
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query) : Type u :=
  match node with
  | .active _ => InternalInquiryResolutionAt.AnswerAt resolution
  | .answered _ _ => nomatch query

private def answer
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query)
    (generated_eq : resolution = node.resolve query) : AnswerAt resolution :=
  match node with
  | .active _ => InternalInquiryResolutionAt.answer resolution generated_eq
  | .answered _ _ => nomatch query

def ReceiptAt
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query) : Type (u + 3) :=
  match node with
  | .active _ => InternalInquiryResolutionAt.ReceiptAt resolution
  | .answered _ _ => nomatch query

private def receipt
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query)
    (generated_eq : resolution = node.resolve query) : ReceiptAt resolution :=
  match node with
  | .active _ => InternalInquiryResolutionAt.receipt resolution generated_eq
  | .answered _ _ => nomatch query

private def nextRootCurrent
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query)
    (generated_eq : resolution = node.resolve query) :
    AnyAuthoritativeRootCurrent.{u} :=
  match node with
  | .active _ =>
      InternalInquiryResolutionAt.nextRootCurrent resolution generated_eq
  | .answered _ _ => nomatch query

private theorem nextRootCurrent_eq_generated
    {node : RootInquiryProcessNode.{u}} {query : node.Query}
    (resolution : node.ResolutionAt query)
    (generated_eq : resolution = node.resolve query) :
    nextRootCurrent resolution generated_eq =
      nextRootCurrent (node.resolve query) rfl := by
  subst resolution
  rfl

end RootInquiryProcessNode

/-- Complete living-law conservation for one inquiry successor.

Ordinary answered branches may keep the source root or cross a source-fixed
faithful-terminal handoff; on every continuing structural branch the complete
living root is preserved.  A revised branch must instead use the exact living
root generated by that rooted U8 completion.  The target may be a local
`answered` node, which carries no further inquiry authority; every active
target is checked here before it can re-enter `Engine.ask`. -/
def InternalInquiryResolutionAt.PreservesTargetLivingRootAt
    {state : RootInquiryStatePresentation.{u}} {query : state.Query}
    (resolution : InternalInquiryResolutionAt state query)
    (target : RootInquiryStatePresentation.{u}) : Prop :=
  match resolution with
  | .directlyAnswered ..
  | .u7Answered ..
  | .oldLanguageAnswered .. =>
      match state.state.base.root.toAuthoritativeRoot.toLedgerRoot
          |>.generatedLedgerAt state.state.base.visit.current with
      | .faithfulTerminal .. => True
      | .nativeWrite ..
      | .relationWrite ..
      | .continuedTransport ..
      | .borromeanRedirect .. =>
          HEq target.state.base.root state.state.base.root
  | .actualAction generated =>
      HEq target.state.base.root generated.target.targetRoot
  | .revised _obstruction _u7Gate _failure generated =>
      HEq target.state.base.root
        generated.revisionReceipt.revision.generate.newLivingRoot

/-- A successor which remains inquiry-active must preserve the complete
living law selected by the canonical resolution.  A local answered node has
no query fibre and therefore exposes no subsequent authority mouth. -/
def RootInquiryProcessNode.PreservesGeneratedLivingLawAt
    (source : RootInquiryProcessNode.{u}) (query : source.Query)
    (target : RootInquiryProcessNode.{u}) : Prop :=
  match source with
  | .answered _ _ => nomatch query
  | .active sourceState =>
      match target with
      | .answered _ _ => True
      | .active targetState =>
          (sourceState.resolve query).PreservesTargetLivingRootAt targetState

namespace RootInquiryProcessNode

/-- Public proof bridge for an ordinary source-compiled answer followed by
another inquiry-active state.

The private gearbox owns `resolve` and `nextRootCurrent`; downstream runtimes
should not unfold those implementation details to justify an ordinary
successor.  Instead they supply the exact installed `.answered` compiler
image, the target's generated erased current, and preservation of the same
complete living root.  This helper eliminates the private resolution inside
the kernel and returns exactly the two proofs required by
`SourceNativeInquiryEngineProcess.successorAt`. -/
theorem active_directlyAnswered_successor_valid
    (source target : RootInquiryStatePresentation.{u})
    (query : source.Query)
    (answerFace : SourceNativeRootSemanticFaceAt
      source.state.base.root source.state.base.visit)
    (consumer : SourceNativeInquiryAnswerConsumerAt
      query (source.state.base.emitInquiry query)
        (source.state.base.entryAt query) answerFace)
    (compile_eq : source.state.base.compileInquiry query =
      .answered answerFace consumer)
    (target_erase_eq : target.erase =
      ⟨source.N, (source.state.base.oldAnswerAndNext query).nextCurrent⟩)
    (target_root_heq : HEq target.state.base.root source.state.base.root) :
    ((RootInquiryProcessNode.active target).erase =
        RootInquiryProcessNode.nextRootCurrent
          ((RootInquiryProcessNode.active source).resolve query) rfl) ∧
      (RootInquiryProcessNode.active source).PreservesGeneratedLivingLawAt
        query (RootInquiryProcessNode.active target) := by
  have resolve_eq : source.resolve query =
      .directlyAnswered answerFace consumer := by
    unfold RootInquiryStatePresentation.resolve
    dsimp only
    generalize generated_eq :
      source.state.base.compileInquiry query = generated at compile_eq ⊢
    cases generated <;> cases compile_eq
    rfl
  constructor
  · calc
      target.erase =
          ⟨source.N,
            (source.state.base.oldAnswerAndNext query).nextCurrent⟩ :=
        target_erase_eq
      _ = RootInquiryProcessNode.nextRootCurrent
          (node := RootInquiryProcessNode.active source) (query := query)
          ((InternalInquiryResolutionAt.directlyAnswered answerFace consumer) :
            InternalInquiryResolutionAt source query) resolve_eq.symm := rfl
      _ = RootInquiryProcessNode.nextRootCurrent
          ((RootInquiryProcessNode.active source).resolve query) rfl :=
        RootInquiryProcessNode.nextRootCurrent_eq_generated
          (node := RootInquiryProcessNode.active source) (query := query)
          ((InternalInquiryResolutionAt.directlyAnswered answerFace consumer) :
            InternalInquiryResolutionAt source query) resolve_eq.symm
  · change (source.resolve query).PreservesTargetLivingRootAt target
    have directPreserves :
        (InternalInquiryResolutionAt.directlyAnswered answerFace consumer)
          |>.PreservesTargetLivingRootAt target := by
      unfold InternalInquiryResolutionAt.PreservesTargetLivingRootAt
      dsimp only
      cases generated_eq :
          source.state.base.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            source.state.base.visit.current with
      | nativeWrite => exact target_root_heq
      | relationWrite => exact target_root_heq
      | continuedTransport => exact target_root_heq
      | borromeanRedirect => exact target_root_heq
      | faithfulTerminal => trivial
    exact Eq.mpr
      (congrArg
        (fun resolution => resolution.PreservesTargetLivingRootAt target)
        resolve_eq) directPreserves

/-- Public integration bridge for an ordinary answer at an exact faithful
terminal occurrence.

Unlike a continuing answer, the generated successor is the terminal-handoff
root fixed in the complete living source law.  Requiring heterogeneous
equality with the terminal source root would make that lawful cross-root
branch uninhabitable, so this theorem consumes the exact admitted terminal
authority instead. -/
theorem active_directlyAnswered_terminalHandoff_successor_valid
    (source target : RootInquiryStatePresentation.{u})
    (query : source.Query)
    (answerFace : SourceNativeRootSemanticFaceAt
      source.state.base.root source.state.base.visit)
    (consumer : SourceNativeInquiryAnswerConsumerAt
      query (source.state.base.emitInquiry query)
        (source.state.base.entryAt query) answerFace)
    (compile_eq : source.state.base.compileInquiry query =
      .answered answerFace consumer)
    (terminal : SourceFaithfulTerminalOccurrenceAt
      source.state.base.root.source.base
      (source.state.base.root.emitted source.state.base.visit.current))
    (target_erase_eq : target.erase =
      ⟨source.N, (source.state.base.oldAnswerAndNext query).nextCurrent⟩) :
    ((RootInquiryProcessNode.active target).erase =
        RootInquiryProcessNode.nextRootCurrent
          ((RootInquiryProcessNode.active source).resolve query) rfl) ∧
      (RootInquiryProcessNode.active source).PreservesGeneratedLivingLawAt
        query (RootInquiryProcessNode.active target) := by
  have resolve_eq : source.resolve query =
      .directlyAnswered answerFace consumer := by
    unfold RootInquiryStatePresentation.resolve
    dsimp only
    generalize generated_eq :
      source.state.base.compileInquiry query = generated at compile_eq ⊢
    cases generated <;> cases compile_eq
    rfl
  constructor
  · calc
      target.erase =
          ⟨source.N,
            (source.state.base.oldAnswerAndNext query).nextCurrent⟩ :=
        target_erase_eq
      _ = RootInquiryProcessNode.nextRootCurrent
          (node := RootInquiryProcessNode.active source) (query := query)
          ((InternalInquiryResolutionAt.directlyAnswered answerFace consumer) :
            InternalInquiryResolutionAt source query) resolve_eq.symm := rfl
      _ = RootInquiryProcessNode.nextRootCurrent
          ((RootInquiryProcessNode.active source).resolve query) rfl :=
        RootInquiryProcessNode.nextRootCurrent_eq_generated
          (node := RootInquiryProcessNode.active source) (query := query)
          ((InternalInquiryResolutionAt.directlyAnswered answerFace consumer) :
            InternalInquiryResolutionAt source query) resolve_eq.symm
  · change (source.resolve query).PreservesTargetLivingRootAt target
    have directPreserves :
        (InternalInquiryResolutionAt.directlyAnswered answerFace consumer)
          |>.PreservesTargetLivingRootAt target := by
      unfold InternalInquiryResolutionAt.PreservesTargetLivingRootAt
      dsimp only
      have generated_eq :
          source.state.base.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
              source.state.base.visit.current =
            .faithfulTerminal terminal.terminal terminal.structural_eq
              terminal.ledgerEvolution :=
        terminal.generated_eq
      rw [generated_eq]
      trivial
    exact Eq.mpr
      (congrArg
        (fun resolution => resolution.PreservesTargetLivingRootAt target)
        resolve_eq) directPreserves

/-- Public integration bridge for a cross-root sequential actual action.

The action token is already the output of the state's exact-occurrence
compiler program.  The caller proves only that its fixed process target is
the target root compiler's generated answer-and-next and preserves that
complete target living root; it cannot submit a target to the action. -/
theorem active_actualAction_successor_valid
    (source target : RootInquiryStatePresentation.{u})
    (query : source.Query)
    {program : SourceNativeSequentialActualActionProgramAt
      source.state.base.root source.state.base.visit
        (source.state.base.entryAt query)
        (source.state.base.authorityAt query)}
    {sourceEvent : ExactTemporalCausalRootEventAt
      source.state.base.root.toAuthoritativeRoot.toLedgerRoot
        source.state.base.visit}
    (generated : SourceGeneratedSequentialActualActionAt
      program sourceEvent)
    (compile_eq : source.state.base.compileInquiry query =
      .actualAction generated)
    (target_erase_eq : target.erase =
      ⟨generated.target.TargetN,
        generated.target.targetAnswerAndNext.nextCurrent⟩)
    (target_root_heq : HEq target.state.base.root
      generated.target.targetRoot) :
    ((RootInquiryProcessNode.active target).erase =
        RootInquiryProcessNode.nextRootCurrent
          ((RootInquiryProcessNode.active source).resolve query) rfl) ∧
      (RootInquiryProcessNode.active source).PreservesGeneratedLivingLawAt
        query (RootInquiryProcessNode.active target) := by
  have resolve_eq : source.resolve query = .actualAction generated := by
    unfold RootInquiryStatePresentation.resolve
    dsimp only
    generalize generated_eq :
      source.state.base.compileInquiry query = compiled at compile_eq ⊢
    cases compiled <;> cases compile_eq
    rfl
  constructor
  · calc
      target.erase =
          ⟨generated.target.TargetN,
            generated.target.targetAnswerAndNext.nextCurrent⟩ :=
        target_erase_eq
      _ = RootInquiryProcessNode.nextRootCurrent
          (node := RootInquiryProcessNode.active source) (query := query)
          ((InternalInquiryResolutionAt.actualAction generated) :
            InternalInquiryResolutionAt source query) resolve_eq.symm := rfl
      _ = RootInquiryProcessNode.nextRootCurrent
          ((RootInquiryProcessNode.active source).resolve query) rfl :=
        RootInquiryProcessNode.nextRootCurrent_eq_generated
          (node := RootInquiryProcessNode.active source) (query := query)
          ((InternalInquiryResolutionAt.actualAction generated) :
            InternalInquiryResolutionAt source query) resolve_eq.symm
  · change (source.resolve query).PreservesTargetLivingRootAt target
    have actionPreserves :
        (InternalInquiryResolutionAt.actualAction generated)
          |>.PreservesTargetLivingRootAt target := by
      unfold InternalInquiryResolutionAt.PreservesTargetLivingRootAt
      exact target_root_heq
    exact Eq.mpr
      (congrArg
        (fun resolution => resolution.PreservesTargetLivingRootAt target)
        resolve_eq) actionPreserves

end RootInquiryProcessNode

/-- A single source-owned meta-process registry.  `stateAt` contains every
current root/query law.  Injectivity after authoritative erasure forbids two
engine states from attaching different future query laws to the same exact
root current.  `successorAt` additionally preserves the complete living root
on ordinary continuation and the exact generated revised root after U8, so
the erased current cannot hide a replacement terminal-handoff law.  Inquiry
and revision events are emitted by `stateAt`; the process has no second branch
compiler. -/
structure SourceNativeInquiryEngineProcess : Type (u + 14) where
  State : Type u
  stateAt : State -> RootInquiryProcessNode.{u}
  erase_injective :
    ∀ {left right : State}
      {leftState rightState : RootInquiryStatePresentation.{u}},
      stateAt left = .active leftState ->
      stateAt right = .active rightState ->
      leftState.erase = rightState.erase ->
      left = right
  initial : State
  successorAt : (state : State) -> (query : (stateAt state).Query) ->
      { successor : State //
        ((stateAt successor).erase =
          RootInquiryProcessNode.nextRootCurrent
            ((stateAt state).resolve query) rfl) ∧
        (stateAt state).PreservesGeneratedLivingLawAt query
          (stateAt successor) }

/-- Canonical single-inquiry process.  A domain supplies one fixed root
presentation; the answered node retains the exact prior query and derives its
world current from that occurrence's compiler-generated successor. -/
private def RootInquiryStatePresentation.oneShotProcessNode
    (state : RootInquiryStatePresentation.{u}) :
    Option state.Query -> RootInquiryProcessNode.{u}
  | none => .active state
  | some query => .answered state query

def RootInquiryStatePresentation.oneShotProcess
    (state : RootInquiryStatePresentation.{u}) :
    SourceNativeInquiryEngineProcess.{u} where
  State := Option state.Query
  stateAt := state.oneShotProcessNode
  erase_injective := by
    intro left right leftState rightState leftActive rightActive _
    cases left with
    | none =>
        cases right with
        | none => rfl
        | some _ => cases rightActive
    | some _ => cases leftActive
  initial := none
  successorAt := by
    intro source query
    cases source with
    | none => exact ⟨some query, rfl, trivial⟩
    | some _ =>
        change PEmpty at query
        exact nomatch query

/-- Raw running engine.  Root, current, U7, failure and revision are hidden
behind its private process state, but this carrier alone is not world
authority; canonical runtime activation supplies that additional index. -/
structure Engine (process : SourceNativeInquiryEngineProcess.{u}) :
    Type (u + 13) where
  private mk ::
  private state : process.State

namespace Engine

def initial
    (process : SourceNativeInquiryEngineProcess.{u}) : Engine process :=
  ⟨process.initial⟩

/-- Current process node as a readout of the private engine state. -/
def node
    {process : SourceNativeInquiryEngineProcess.{u}}
    (engine : Engine process) : RootInquiryProcessNode.{u} :=
  process.stateAt engine.state

abbrev Query
    {process : SourceNativeInquiryEngineProcess.{u}}
    (engine : Engine process) : Type u :=
  engine.node.Query

/-- A query may enter the autonomous authority mouth only through a sealed
activation.  The current constructor is deliberately limited to a unique
query fibre; nontrivial external queries require a registered input producer
rather than a caller-selected value. -/
structure SourceNativeInquiryActivationAt
    {process : SourceNativeInquiryEngineProcess.{u}}
    (engine : Engine process) : Type u where
  private mk ::
  private selectedQuery : engine.Query

namespace SourceNativeInquiryActivationAt

def query
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process}
    (activation : SourceNativeInquiryActivationAt engine) : engine.Query :=
  activation.selectedQuery

end SourceNativeInquiryActivationAt

/-- Explicit zero-choice activation.  Supplying a query is harmless only
when every value in the current query fibre is propositionally that value. -/
def uniqueInquiryActivation
    {process : SourceNativeInquiryEngineProcess.{u}}
    (engine : Engine process)
    (query : engine.Query)
    (_query_unique : ∀ candidate : engine.Query, candidate = query) :
    SourceNativeInquiryActivationAt engine :=
  ⟨query⟩

@[simp] theorem uniqueInquiryActivation_query
    {process : SourceNativeInquiryEngineProcess.{u}}
    (engine : Engine process)
    (query : engine.Query)
    (query_unique : ∀ candidate : engine.Query, candidate = query) :
    (engine.uniqueInquiryActivation query query_unique).query = query :=
  rfl

/-- Zero-information autonomous query activation.  `Unique` rules out a
hidden query-selection bit; richer query carriers must arrive through a
future registered-input constructor, not through this mouth. -/
def canonicalInquiryActivation
    {process : SourceNativeInquiryEngineProcess.{u}}
    (engine : Engine process) [Unique engine.Query] :
    SourceNativeInquiryActivationAt engine :=
  engine.uniqueInquiryActivation default (fun _candidate => Subsingleton.elim _ _)

/-- Source-owned autonomous query law for one complete inquiry process.

The initial activation belongs to the fixed process.  Every later activation
is generated from the preceding activation and that inquiry's exact
successor.  Thus the law does not store a completed state-indexed query table,
and a local one-shot process cannot inhabit it after reaching its empty query
fibre. -/
structure SourceNativeInquiryActivationLaw
    (process : SourceNativeInquiryEngineProcess.{u}) : Type (u + 13) where
  initial : SourceNativeInquiryActivationAt (Engine.initial process)
  nextAt :
    (state : process.State) →
    (activation : SourceNativeInquiryActivationAt
      (⟨state⟩ : Engine process)) →
    SourceNativeInquiryActivationAt
      (⟨(process.successorAt state activation.query).1⟩ : Engine process)

namespace SourceNativeInquiryActivationLaw

/-- Build a zero-choice recursive source law.  Only the initial query and the
query generated after the current exact transition are supplied; there is no
free activation at an arbitrary process state. -/
def ofUnique
    {process : SourceNativeInquiryEngineProcess.{u}}
    (initialQuery : (process.stateAt process.initial).Query)
    (initialQuery_unique :
      ∀ candidate : (process.stateAt process.initial).Query,
        candidate = initialQuery)
    (nextQueryAt :
      (state : process.State) →
      (query : (process.stateAt state).Query) →
      (process.stateAt (process.successorAt state query).1).Query)
    (nextQuery_unique :
      (state : process.State) →
      (query : (process.stateAt state).Query) →
      ∀ candidate :
        (process.stateAt (process.successorAt state query).1).Query,
        candidate = nextQueryAt state query) :
    SourceNativeInquiryActivationLaw process where
  initial :=
    (Engine.initial process).uniqueInquiryActivation
      initialQuery initialQuery_unique
  nextAt := fun state activation =>
    (⟨(process.successorAt state activation.query).1⟩ : Engine process)
      |>.uniqueInquiryActivation
        (nextQueryAt state activation.query)
        (nextQuery_unique state activation.query)

end SourceNativeInquiryActivationLaw

/-- Raw inquiry occurrence indexed by one engine and query.  It is the exact
compiler model read by canonical runtime activation, not an authority token
which may be replayed across runtimes. -/
structure ExactRootInquiryOccurrenceAt
    {process : SourceNativeInquiryEngineProcess.{u}}
    (engine : Engine process) (query : engine.Query) : Type (u + 13) where
  private mk ::
  private generatedResolution :
    (process.stateAt engine.state).ResolutionAt query
  private generated_eq : generatedResolution =
    (process.stateAt engine.state).resolve query

namespace ExactRootInquiryOccurrenceAt

def resolution
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
    (occurrence : ExactRootInquiryOccurrenceAt engine query) :
    (process.stateAt engine.state).ResolutionAt query :=
  occurrence.generatedResolution

theorem resolution_eq_generated
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
    (occurrence : ExactRootInquiryOccurrenceAt engine query) :
    occurrence.resolution = (process.stateAt engine.state).resolve query :=
  occurrence.generated_eq

def answer
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
    (occurrence : ExactRootInquiryOccurrenceAt engine query) :
    RootInquiryProcessNode.AnswerAt occurrence.resolution :=
  RootInquiryProcessNode.answer occurrence.resolution
    occurrence.resolution_eq_generated

def receipt
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
    (occurrence : ExactRootInquiryOccurrenceAt engine query) :
    RootInquiryProcessNode.ReceiptAt occurrence.resolution :=
  RootInquiryProcessNode.receipt occurrence.resolution
    occurrence.resolution_eq_generated

def next
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
    (_occurrence : ExactRootInquiryOccurrenceAt engine query) : Engine process :=
  ⟨(process.successorAt engine.state query).1⟩

theorem next_erases_to_generated
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
  (occurrence : ExactRootInquiryOccurrenceAt engine query) :
    (process.stateAt occurrence.next.state).erase =
      RootInquiryProcessNode.nextRootCurrent occurrence.resolution
        occurrence.resolution_eq_generated := by
  calc
    (process.stateAt occurrence.next.state).erase =
      RootInquiryProcessNode.nextRootCurrent
          ((process.stateAt engine.state).resolve query) rfl :=
      (process.successorAt engine.state query).2.1
    _ = RootInquiryProcessNode.nextRootCurrent occurrence.resolution
          occurrence.resolution_eq_generated :=
      (RootInquiryProcessNode.nextRootCurrent_eq_generated
        occurrence.resolution occurrence.resolution_eq_generated).symm

/-- The public next engine cannot become inquiry-active under a sibling
terminal-handoff or revised-root law.  This is the cross-step half of the
exact inquiry receipt; authoritative erasure alone is not sufficient. -/
theorem next_preservesGeneratedLivingLaw
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
    (occurrence : ExactRootInquiryOccurrenceAt engine query) :
    (process.stateAt engine.state).PreservesGeneratedLivingLawAt query
      (process.stateAt occurrence.next.state) :=
  (process.successorAt engine.state query).2.2

end ExactRootInquiryOccurrenceAt

/-- Raw execution readout consumes a sealed activation, not a query value.
Source, current, U7/U8 branch, failure face and concrete revision remain
internal.  Authority consumers must use the sealed canonical-runtime tick. -/
def ask
    {process : SourceNativeInquiryEngineProcess.{u}}
    (engine : Engine process)
    (activation : SourceNativeInquiryActivationAt engine) :
    ExactRootInquiryOccurrenceAt engine activation.query :=
  ⟨(process.stateAt engine.state).resolve activation.query, rfl⟩

namespace SourceNativeInquiryActivationLaw

/-- Generate the next activation from the current exact inquiry transition.
This is the only autonomous cross-step activation mouth. -/
def nextAfter
    {process : SourceNativeInquiryEngineProcess.{u}}
    (law : SourceNativeInquiryActivationLaw process)
    {engine : Engine process}
    (activation : SourceNativeInquiryActivationAt engine) :
    SourceNativeInquiryActivationAt (engine.ask activation).next := by
  rcases engine with ⟨state⟩
  exact law.nextAt state activation

end SourceNativeInquiryActivationLaw

namespace ExactRootInquiryOccurrenceAt

/-- A fixed engine and exact query emit one typed inquiry occurrence.
Answer, receipt, and successor diversity must therefore enter through a
different engine source or a different registered query; it cannot hide in a
second realization of the same occurrence. -/
theorem eq_ask
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
    [Unique engine.Query]
    (occurrence : ExactRootInquiryOccurrenceAt engine query) :
    HEq occurrence
      (engine.ask (canonicalInquiryActivation engine)) := by
  have query_eq : query = default := Subsingleton.elim _ _
  cases query_eq
  rcases occurrence with ⟨generatedResolution, generated_eq⟩
  subst generatedResolution
  rfl

/-- Immediate detector for a caller attempting to vary any dependent readout
while retaining the same engine/query occurrence. -/
theorem eq_of_same_inquiry
    {process : SourceNativeInquiryEngineProcess.{u}}
    {engine : Engine process} {query : engine.Query}
    (left right : ExactRootInquiryOccurrenceAt engine query) :
    left = right := by
  rcases left with ⟨leftResolution, left_eq⟩
  rcases right with ⟨rightResolution, right_eq⟩
  subst leftResolution
  subst rightResolution
  rfl

end ExactRootInquiryOccurrenceAt

end Engine

end RootInquiryCompletion
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.RootInquiryProcessNode.active_directlyAnswered_successor_valid
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.RootInquiryProcessNode.active_directlyAnswered_terminalHandoff_successor_valid
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.RootInquiryProcessNode.active_actualAction_successor_valid
