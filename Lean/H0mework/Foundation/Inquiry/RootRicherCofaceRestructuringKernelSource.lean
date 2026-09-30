import H0mework.Foundation.Inquiry.SemanticRevision
import H0mework.Foundation.Ledger.Restructuring

/-!
# Source-generated richer-coface restructuring contract

A typed U8 revision already fixes its revised living root, initial occurrence,
first whole-ledger write, migrated old ledger, and minimal-coface
factorization.  This module states the additional candidate contract required
when that exact first write performs a genuine one-to-many restructuring.

The contract does not generate a split for an arbitrary revision.  An
inhabitant must exhibit two distinct target entries of the canonical initial
whole-ledger successor, show that both have the translated old target entry
as their exact origin, and consume the source-fixed restructuring compiler's
`SourceNativeSplitCoverageAt`.  Strict child debits and bearer separation are
therefore read from the same receipt and occurrence.

No root, occurrence, ledger, child family, coverage table, first write, or
completed future is constructed here.  The structure is a candidate mouth
for later source realizations; obstruction lemmas make its missing fibres
explicit.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedRicherCofaceRestructuring

open ObstructionGeneratedMinimalCoface
open TypedSemanticWorldNetworkU8

universe u

variable
    {N : WorldRelationNetwork.{u}}
    {OldV : Vocabulary.{u}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N}
    {oldTheory : TheoryState N}
    {support : N.Support}
    {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldWorld oldVisit U7 failure}

/-! ## Exact revised-source readouts -/

/-- The restructuring law is already fixed inside the revised root source.
It is not accepted by the later split action. -/
def sourceFixedRestructuringLaw
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :
    SourceNativeLedgerRestructuringLaw
      revision.newRoot.source.restructuringSource.source :=
  revision.newRoot.source.restructuringSource.compiler.restructuringLaw

/-- Canonical first temporal visit of the revised root. -/
def initialVisit
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :
    SourceNativeTemporalVisitAt revision.newRoot.toLedgerRoot :=
  .finite revision.newRoot.toRoot.initialVisit

/-- Canonical compiler image at the revised root's first visit. -/
def initialGenerated
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      revision.newRoot.toLedgerRoot (initialVisit revision) :=
  revision.newRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit revision)

/-- Exact initial occurrence emitted by the revised root. -/
def initialOccurrence
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :=
  (initialGenerated revision).occurrence

/-- Exact first whole-ledger compiler image. -/
def initialWholeLedgerWriteBack
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :=
  (initialGenerated revision).wholeLedgerWriteBack

/-- Exact old target responsibility retained by the rooted failure. -/
def oldParent
    (_revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :=
  rooted.oldTargetEntry

/-- The same old parent inside the revised initial ledger. -/
def translatedParent
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :=
  revision.oldTargetOpenLedger.forward (oldParent revision)

/-- Eliminate the terminal branch using the exact successor token and recover
the restructuring certification selected by the revised source compiler.
This is the provenance bridge used below; it does not search for or choose a
split classification. -/
def exactRestructuringCertification
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted)
    (successor : SourceNativeLedgerGeneratedSuccessorAt
      (initialOccurrence revision) (initialWholeLedgerWriteBack revision)) :
    ExactLedgerRestructuringCertificationAt
      (sourceFixedRestructuringLaw revision) (initialOccurrence revision)
      successor.ledgerEvolution := by
  generalize generated_eq :
    initialWholeLedgerWriteBack revision = generated at successor ⊢
  have certified :=
    revision.newRoot.source.restructuringSource.compiler.certifyRestructuring
      (initialOccurrence revision)
  change
    revision.newRoot.source.restructuringSource.compiler.ledgerCompiler.compile
        (initialOccurrence revision) = generated at generated_eq
  rw [generated_eq] at certified
  cases generated with
  | nativeWrite => exact certified
  | relationWrite => exact certified
  | continuedTransport => exact certified
  | borromeanRedirect => exact certified
  | faithfulTerminal => exact nomatch successor

/-! ## Grounded default-side loss-allocation action -/

/-- A default-side loss-allocation action is the central richer-U8 genuine
split itself, plus its law-surface grounding and bearer separation.

It does not duplicate successor, children, coverage, or compiler-selection
fields beside `SourceGeneratedFirstWriteGenuineSplitAt`; consequently the
no-dormant initial ledger and all-target-origin coverage cannot diverge from
the split consumed here.  The name deliberately does not claim a complete
risk pool: multi-source merge is a later generated action. -/
structure SourceGeneratedDefaultSideLossAllocationAt
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :
    Type (u + 9) where
  private mk ::
  genuineSplit : revision.SourceGeneratedFirstWriteGenuineSplitAt
  lawSurface_heq : HEq revision.newLivingRoot.source.base.lawSurface
    (TheoryState.rootSemantic revision.NewN)
  bearers_distinct :
    ((sourceFixedRestructuringLaw revision).obligationAt
      (initialOccurrence revision) genuineSplit.left).bearer ≠
    ((sourceFixedRestructuringLaw revision).obligationAt
      (initialOccurrence revision) genuineSplit.right).bearer

/-- Public assembler for one already source-generated central split.  No
parallel root, occurrence, ledger, children, coverage receipt, first write,
or next current is accepted here. -/
def SourceGeneratedDefaultSideLossAllocationAt.ofGroundedFirstWriteSplit
    (revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted)
    (genuineSplit : revision.SourceGeneratedFirstWriteGenuineSplitAt)
    (lawSurface_heq : HEq revision.newLivingRoot.source.base.lawSurface
      (TheoryState.rootSemantic revision.NewN))
    (bearers_distinct :
      ((sourceFixedRestructuringLaw revision).obligationAt
        (initialOccurrence revision) genuineSplit.left).bearer ≠
      ((sourceFixedRestructuringLaw revision).obligationAt
        (initialOccurrence revision) genuineSplit.right).bearer) :
    SourceGeneratedDefaultSideLossAllocationAt revision :=
  ⟨genuineSplit, lawSurface_heq, bearers_distinct⟩

namespace SourceGeneratedDefaultSideLossAllocationAt

variable {revision : GeneratedTypedSemanticWorldNetworkRevisionAt rooted}

abbrev successor
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :=
  action.genuineSplit.successor

abbrev left
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :=
  action.genuineSplit.left

abbrev right
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :=
  action.genuineSplit.right

abbrev origin_eq
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :=
  action.genuineSplit.origin_eq

abbrev split
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :=
  action.genuineSplit.split

/-- The central split and its exact law surface generate the same richer
grounding installed by the unique typed-U8 candidate. -/
theorem richerGrounding
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    revision.SourceGeneratedFaithfulRicherCofaceRestructuringAt where
  lawSurface_heq := action.lawSurface_heq
  genuineFirstWriteSplit := ⟨action.genuineSplit⟩

/-- Reuse the existing unique revision carrier; this is not a second U8. -/
def fieldGroundedRevision
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted :=
  FieldGroundedTypedSemanticWorldNetworkRevisionAt.ofSourceGeneratedRestructuring
    revision action.richerGrounding

@[simp] theorem fieldGroundedRevision_generate
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    action.fieldGroundedRevision.generate = revision :=
  rfl

@[simp] theorem fieldGroundedRevision_uses_richer_grounding
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    action.fieldGroundedRevision.revisionGrounding =
      GeneratedTypedSemanticWorldNetworkRevisionAt.RevisionGroundingAt.richer
        action.richerGrounding :=
  rfl

/-- The action carries the original causal authority rather than minting an
authority token beside the U8 frontier. -/
def oldBoundaryAuthoritativeAuthority
    (_action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      oldWorld oldVisit rooted.rootEntry :=
  rooted.authority

/-- The old parent is reached through the rooted failure's canonical causal
successor. -/
def oldParentSuccessor
    (_action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    CausalEntrySuccessorAt oldWorld.toLedgerRoot oldVisit rooted.rootEntry :=
  rooted.oldSuccessor

@[simp] theorem oldParentSuccessor_targetEntry
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    action.oldParentSuccessor.targetEntry = oldParent revision :=
  rfl

/-- The split source is exactly the translated old target entry. -/
theorem translatedParent_eq_origin_left
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    translatedParent revision =
      (action.successor.ledgerEvolution.origin action.left).1 :=
  action.genuineSplit.parent_origin_eq.symm

/-- The right child has the same exact translated parent. -/
theorem translatedParent_eq_origin_right
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    translatedParent revision =
      (action.successor.ledgerEvolution.origin action.right).1 := by
  exact action.genuineSplit.parent_origin_eq.symm.trans action.origin_eq

/-- The exact revised-source compiler, rather than a compatible sibling
receipt, selects this split classification. -/
theorem compiler_selects_exact_split
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    (exactRestructuringCertification revision action.successor).split
        action.left action.right action.origin_eq =
      SourceNativeSplitClassificationAt.split action.split :=
  action.genuineSplit.compilerSelectsSplit

/-- First child debit generated by the split coverage receipt. -/
theorem left_budget_strictly_debited
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    action.left.progressBudget < (translatedParent revision).progressBudget := by
  exact action.genuineSplit.left_budget_strictly_debited

/-- Second child debit generated by the same split coverage receipt. -/
theorem right_budget_strictly_debited
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    action.right.progressBudget <
      (translatedParent revision).progressBudget := by
  exact action.genuineSplit.right_budget_strictly_debited

/-- Distinct bearer readouts force distinct source-law obligations; no
caller-supplied slot or registry is needed for this separation. -/
theorem child_obligations_distinct
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    (sourceFixedRestructuringLaw revision).obligationAt
        (initialOccurrence revision) action.left ≠
      (sourceFixedRestructuringLaw revision).obligationAt
        (initialOccurrence revision) action.right := by
  intro equality
  exact action.bearers_distinct
    (congrArg AdmittedObligation.bearer equality)

/-- The successor token and the canonical first-write token expose the same
structural target. -/
theorem successor_target_eq_firstWrite
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    action.successor.targetCurrent = revision.firstWrite.target := by
  have successorNext := action.successor.next_eq
  have firstWriteNext := revision.firstWrite.next_eq
  change
    (revision.newRoot.toLedgerRoot.source.source.toRootSource.actual.compile
      (initialOccurrence revision)).nextCurrent? =
        some revision.firstWrite.target at firstWriteNext
  exact Option.some.inj (successorNext.symm.trans firstWriteNext)

/-- Canonical revised-root answer-and-next.  The action stores no next root. -/
def answerAndNext
    (_action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    SourceNativeLivingRootCausalEvolutionAt revision.newLivingRoot
      (ULift.up (initialVisit revision)) :=
  revision.newLivingRoot.canonicalCausalAnswerAndNext
    (ULift.up (initialVisit revision))

@[simp] theorem answerAndNext_generated_exact
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    action.answerAndNext.generated = initialGenerated revision :=
  rfl

@[simp] theorem answerAndNext_next_exact
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    action.answerAndNext.nextCurrent =
      revision.newLivingRoot.generatedNextCurrentAt
        (initialVisit revision) :=
  rfl

/-- The revised source's first whole-ledger write commutes with its own
emitter. -/
theorem firstWholeLedgerWriteBack_commutes
    (_action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    (initialWholeLedgerWriteBack revision).CommutesWith
      revision.newRoot.emitted :=
  revision.newRoot.compiler_commutes
    revision.newRoot.toRoot.source.initial

/-- Initial minimal-coface factorization and attached first-write realization
remain exactly those already generated by the typed revision. -/
def minimalCofaceFactorization
    (_action : SourceGeneratedDefaultSideLossAllocationAt revision) :=
  revision.factorizesThroughInitialCoface

/-- Compact direct-consumer contract: the same revision supplies the
minimal-coface factorization, exact first whole-ledger commuting, and both
strict child debits. -/
def factorization_firstWrite_and_bothDebits
    (action : SourceGeneratedDefaultSideLossAllocationAt revision) :
    (FaithfulCofaceMorphism
        (root_obstruction_generates_minimal_coface rooted)
        revision.toAdmissibleMinimalCoface ×
      SourceGeneratedAttachedCofaceRealizationAt revision) ×
      PLift
        ((exactRestructuringCertification revision action.successor).split
            action.left action.right action.origin_eq =
          SourceNativeSplitClassificationAt.split action.split) ×
      PLift ((initialWholeLedgerWriteBack revision).CommutesWith
        revision.newRoot.emitted) ×
      PLift (action.left.progressBudget <
        (translatedParent revision).progressBudget) ×
      PLift (action.right.progressBudget <
        (translatedParent revision).progressBudget) :=
  ⟨action.minimalCofaceFactorization,
    ⟨action.compiler_selects_exact_split⟩,
    ⟨action.firstWholeLedgerWriteBack_commutes⟩,
    ⟨action.left_budget_strictly_debited⟩,
    ⟨action.right_budget_strictly_debited⟩⟩

/-! ## Exact obstruction lemmas -/

/-- Any candidate whose exact first-write target ledger is subsingleton has
no genuine two-child split action. -/
theorem isEmpty_of_targetEntry_subsingleton
    (allSubsingleton :
      (successor : SourceNativeLedgerGeneratedSuccessorAt
        (initialOccurrence revision)
        (initialWholeLedgerWriteBack revision)) →
      Subsingleton (OpenResponsibilityAt revision.NewN
        (revision.newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          successor.targetOccurrence))) :
    IsEmpty (SourceGeneratedDefaultSideLossAllocationAt revision) := by
  refine ⟨fun action => ?_⟩
  exact action.genuineSplit.children_distinct
    ((allSubsingleton action.successor).elim action.left action.right)

/-- If the source-fixed restructuring compiler has no split coverage at the
exact first-write evolution, the candidate action fibre is empty. -/
theorem isEmpty_of_splitCoverage_empty
    (noCoverage :
      (successor : SourceNativeLedgerGeneratedSuccessorAt
        (initialOccurrence revision)
        (initialWholeLedgerWriteBack revision)) →
      (left right : OpenResponsibilityAt revision.NewN
        (revision.newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          successor.targetOccurrence)) →
      (origin_eq :
        (successor.ledgerEvolution.origin left).1 =
          (successor.ledgerEvolution.origin right).1) →
      IsEmpty (SourceNativeSplitCoverageAt
        (sourceFixedRestructuringLaw revision) (initialOccurrence revision)
          successor.ledgerEvolution left right origin_eq)) :
    IsEmpty (SourceGeneratedDefaultSideLossAllocationAt revision) := by
  refine ⟨fun action => ?_⟩
  exact (noCoverage action.successor action.left action.right
    action.origin_eq).false action.split

end SourceGeneratedDefaultSideLossAllocationAt

end SourceGeneratedRicherCofaceRestructuring
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.sourceFixedRestructuringLaw
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.ofGroundedFirstWriteSplit
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.richerGrounding
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.fieldGroundedRevision
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.fieldGroundedRevision_uses_richer_grounding
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.compiler_selects_exact_split
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.left_budget_strictly_debited
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.factorization_firstWrite_and_bothDebits
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.isEmpty_of_targetEntry_subsingleton
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring.SourceGeneratedDefaultSideLossAllocationAt.isEmpty_of_splitCoverage_empty
