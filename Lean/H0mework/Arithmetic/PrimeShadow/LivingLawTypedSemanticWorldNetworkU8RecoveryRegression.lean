import H0mework.Foundation.Inquiry.RevisionRecovery

/-!
# Regression: typed semantic U8 reaches root causal answer-and-next

The exact selected event generates the revised root and carries both emitted
rows into the living root's causal answer-and-next compiler.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace TypedSemanticWorldNetworkU8RecoveryRegression

open ObstructionGeneratedMinimalCoface
open TypedSemanticWorldNetworkU8
open TypedSemanticWorldNetworkU8Lifecycle
open TypedSemanticWorldNetworkU8Recovery

universe u

variable
    {N : WorldRelationNetwork.{u}}
    {OldV : Vocabulary.{u}}
    {oldRoot : SourceNativeAuthoritativeRootClosure N OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N}
    {oldTheory : TheoryState N}
    {support : N.Support}
    {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt
      oldRoot oldVisit U7 failure}
    (source : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted)

/-- If an extra coordinate is actually emitted as a revised initial row, its
lineage cannot be washed into a fresh target identity or left without a
disposition. -/
def every_generated_initial_entry_is_carried_and_answered
    (entry : OpenResponsibilityAt source.generate.NewN
      (source.generate.newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (source.generate.newRoot.emitted
          source.generate.newRoot.toRoot.source.initial)))
    (row : (source.generate.newRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite source.generate.newRoot.toRoot.initialVisit)).GeneratedEntryRowAt
        entry) :=
  generatedInitialEntryAnswerAndNext source entry row

def old_target_answer_and_next :=
  generatedOldTargetAnswerAndNext source

def new_target_answer_and_next :=
  generatedNewTargetAnswerAndNext source

/-- The row is first carried through the revised first write; its public next
current is then the living compiler image at that exact target visit. -/
theorem generated_initial_entry_next_is_recovery_next
    (entry : OpenResponsibilityAt source.generate.NewN
      (source.generate.newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (source.generate.newRoot.emitted
          source.generate.newRoot.toRoot.source.initial)))
    (row : (source.generate.newRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite source.generate.newRoot.toRoot.initialVisit)).GeneratedEntryRowAt
        entry) :
    (generatedInitialEntryAnswerAndNext source entry row).nextCurrent =
      (generatedOldTargetAnswerAndNext source).nextCurrent :=
  rfl

/-- The old causal row is already the exact demand event generated at the
selected old-root occurrence; recovery accepts no second recognition. -/
theorem rooted_failure_entry_is_source_event :
    oldEntryAtFailureSupport rooted =
      U7ActualSuccessorSource.demandEntry rooted.u7Event :=
  rooted.rootEntryAtFailure_eq

/-- The occurrence-local U7 event is the canonical event of the source-owned
calculus fixed before root emission. -/
theorem rooted_failure_entry_is_canonical_u7_event :
    oldEntryAtFailureSupport rooted =
      U7ActualSuccessorSource.demandEntry
        (rooted.calculus.source.emit obstruction) := by
  calc
    oldEntryAtFailureSupport rooted =
        U7ActualSuccessorSource.demandEntry rooted.u7Event :=
      rooted_failure_entry_is_source_event
    _ = U7ActualSuccessorSource.demandEntry
        (rooted.calculus.source.emit obstruction) :=
      congrArg U7ActualSuccessorSource.demandEntry rooted.u7Event_eq_emit

/-- The post-root failure-entry court has been removed from the recovery
source mouth. -/
theorem recovery_exposes_no_post_root_failure_entry_court : True := by
  fail_if_success
    exact fun
      (candidate : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) =>
        candidate.failureEntry
  trivial

#print axioms every_generated_initial_entry_is_carried_and_answered
#print axioms old_target_answer_and_next
#print axioms new_target_answer_and_next
#print axioms generated_initial_entry_next_is_recovery_next

end TypedSemanticWorldNetworkU8RecoveryRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
