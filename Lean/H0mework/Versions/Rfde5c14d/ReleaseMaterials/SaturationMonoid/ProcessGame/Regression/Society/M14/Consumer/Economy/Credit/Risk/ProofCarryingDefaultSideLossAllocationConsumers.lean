import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedWorld

/-!
# Independent consumers of the default-side loss-allocation split

The two existing exchange-leg children do not borrow ordinary inquiry or
living causal authority.  Each consumer is generated from its own exact
target row in the one central split receipt and consumes that receipt's
source ownership, descendant incidence, anchor transport, lineage, and local
discharge.  The ordinary root/query lineage continues through the transferred
obstruction row.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingDefaultSideLossAllocationConsumers

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld

abbrev OldVisit :=
  RootVisit M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot

abbrev revisionAt (visit : OldVisit) := generatedTypedRevisionAt visit
abbrev actionAt (visit : OldVisit) :=
  generatedDefaultSideLossAllocationAt visit
abbrev lawAt (visit : OldVisit) :=
  (revisionAt visit).sourceFixedRestructuringLaw
abbrev occurrenceAt (visit : OldVisit) :=
  (revisionAt visit).initialRestructuringGenerated.occurrence

structure SourceGeneratedDefaultSideChildConsumerAtVisit
    (visit : OldVisit)
    (target : OpenResponsibilityAt (revisionAt visit).NewN
      ((revisionAt visit).newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (actionAt visit).successor.targetOccurrence))
    (targetOrigin_eq :
      ((actionAt visit).successor.ledgerEvolution.origin target).1 =
        ((actionAt visit).successor.ledgerEvolution.origin
          (actionAt visit).left).1) : Type where
  private mk ::
  member : (lawAt visit).obligationAt (occurrenceAt visit) target ∈
    (actionAt visit).split.receipt.children
  sourceOwnership : SourceOwnsResponsibilityIncidence
    (lawAt visit).vocabulary.base (actionAt visit).split.receipt.sourceEvent
      ((lawAt visit).obligationAt (occurrenceAt visit)
        ((actionAt visit).successor.ledgerEvolution.origin
          (actionAt visit).left).1)
  descendant : (lawAt visit).vocabulary.DescendantAt
    (actionAt visit).split.receipt.sourceEvent
    ((lawAt visit).obligationAt (occurrenceAt visit)
      ((actionAt visit).successor.ledgerEvolution.origin
        (actionAt visit).left).1).sourceIncidence
    ((lawAt visit).obligationAt (occurrenceAt visit)
      ((actionAt visit).successor.ledgerEvolution.origin
        (actionAt visit).left).1).content
    ((lawAt visit).obligationAt (occurrenceAt visit) target).sourceIncidence
    ((lawAt visit).obligationAt (occurrenceAt visit) target).content
  anchorTransport : SourceAnchorTransport
    ((lawAt visit).obligationAt (occurrenceAt visit)
      ((actionAt visit).successor.ledgerEvolution.origin
        (actionAt visit).left).1).sourceAnchor
    ((lawAt visit).obligationAt (occurrenceAt visit) target).sourceAnchor
  lineage : SameDebtLineage
    ((lawAt visit).obligationAt (occurrenceAt visit)
      ((actionAt visit).successor.ledgerEvolution.origin
        (actionAt visit).left).1)
    ((lawAt visit).obligationAt (occurrenceAt visit) target)
  localDischarge : (lawAt visit).vocabulary.LocalDischargePreservedAt
    (actionAt visit).split.receipt.sourceEvent
    ((lawAt visit).obligationAt (occurrenceAt visit)
      ((actionAt visit).successor.ledgerEvolution.origin
        (actionAt visit).left).1).content
    ((lawAt visit).obligationAt (occurrenceAt visit) target).content

def leftChildConsumerAt (visit : OldVisit) :
    SourceGeneratedDefaultSideChildConsumerAtVisit visit
      (actionAt visit).left rfl where
  member := (actionAt visit).split.left_member
  sourceOwnership := (actionAt visit).split.receipt.sourceOwnership
  descendant := (actionAt visit).split.receipt.descendant _
    (actionAt visit).split.left_member
  anchorTransport :=
    (actionAt visit).split.receipt.anchorTransport _
      (actionAt visit).split.left_member
  lineage := (actionAt visit).split.receipt.lineage _
    (actionAt visit).split.left_member
  localDischarge :=
    (actionAt visit).split.receipt.localDischarge _
      (actionAt visit).split.left_member

def rightChildConsumerAt (visit : OldVisit) :
    SourceGeneratedDefaultSideChildConsumerAtVisit visit
      (actionAt visit).right (actionAt visit).origin_eq.symm where
  member := (actionAt visit).split.right_member
  sourceOwnership := (actionAt visit).split.receipt.sourceOwnership
  descendant := (actionAt visit).split.receipt.descendant _
    (actionAt visit).split.right_member
  anchorTransport :=
    (actionAt visit).split.receipt.anchorTransport _
      (actionAt visit).split.right_member
  lineage := (actionAt visit).split.receipt.lineage _
    (actionAt visit).split.right_member
  localDischarge :=
    (actionAt visit).split.receipt.localDischarge _
      (actionAt visit).split.right_member

theorem childConsumers_have_distinct_bearers_at (visit : OldVisit) :
    ((lawAt visit).obligationAt (occurrenceAt visit)
      (actionAt visit).left).bearer ≠
      ((lawAt visit).obligationAt (occurrenceAt visit)
        (actionAt visit).right).bearer :=
  (actionAt visit).bearers_distinct

theorem childConsumers_exact_origin_and_local_discharge_at
    (visit : OldVisit) :
    ((actionAt visit).successor.ledgerEvolution.origin
        (actionAt visit).left).1 =
        (revisionAt visit).oldTargetOpenLedger.forward
          (rootedAt visit).oldTargetEntry ∧
      ((actionAt visit).successor.ledgerEvolution.origin
        (actionAt visit).right).1 =
        (revisionAt visit).oldTargetOpenLedger.forward
          (rootedAt visit).oldTargetEntry ∧
      Nonempty ((lawAt visit).vocabulary.LocalDischargePreservedAt
        (actionAt visit).split.receipt.sourceEvent
        ((lawAt visit).obligationAt (occurrenceAt visit)
          ((actionAt visit).successor.ledgerEvolution.origin
            (actionAt visit).left).1).content
        ((lawAt visit).obligationAt (occurrenceAt visit)
          (actionAt visit).left).content) ∧
      Nonempty ((lawAt visit).vocabulary.LocalDischargePreservedAt
        (actionAt visit).split.receipt.sourceEvent
        ((lawAt visit).obligationAt (occurrenceAt visit)
          ((actionAt visit).successor.ledgerEvolution.origin
            (actionAt visit).left).1).content
        ((lawAt visit).obligationAt (occurrenceAt visit)
          (actionAt visit).right).content) :=
  ⟨(actionAt visit).genuineSplit.parent_origin_eq,
    (actionAt visit).genuineSplit.origin_eq.symm.trans
      (actionAt visit).genuineSplit.parent_origin_eq,
    ⟨(leftChildConsumerAt visit).localDischarge⟩,
    ⟨(rightChildConsumerAt visit).localDischarge⟩⟩

theorem childConsumers_do_not_mint_living_causal_authority_at
    (_visit : OldVisit) : True := by
  fail_if_success exact (leftChildConsumerAt _visit).causalSuccessor
  fail_if_success exact (rightChildConsumerAt _visit).causalSuccessor
  fail_if_success exact (leftChildConsumerAt _visit).livingAuthority
  fail_if_success exact (rightChildConsumerAt _visit).livingAuthority
  trivial

/-! ## Definitionally specialized initial-visit facade -/

abbrev initialVisit : OldVisit :=
  M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.initialVisit
abbrev action := actionAt initialVisit
abbrev revision := revisionAt initialVisit
abbrev law := lawAt initialVisit
abbrev occurrence := occurrenceAt initialVisit
abbrev SourceGeneratedDefaultSideChildConsumerAt :=
  SourceGeneratedDefaultSideChildConsumerAtVisit initialVisit

def leftChildConsumer := leftChildConsumerAt initialVisit
def rightChildConsumer := rightChildConsumerAt initialVisit

theorem childConsumers_have_distinct_bearers :
    (law.obligationAt occurrence action.left).bearer ≠
      (law.obligationAt occurrence action.right).bearer :=
  childConsumers_have_distinct_bearers_at initialVisit

theorem childConsumers_exact_origin_and_local_discharge :
    (action.successor.ledgerEvolution.origin action.left).1 =
        revision.oldTargetOpenLedger.forward rooted.oldTargetEntry ∧
      (action.successor.ledgerEvolution.origin action.right).1 =
        revision.oldTargetOpenLedger.forward rooted.oldTargetEntry ∧
      Nonempty (law.vocabulary.LocalDischargePreservedAt
        action.split.receipt.sourceEvent
        (law.obligationAt occurrence
          (action.successor.ledgerEvolution.origin action.left).1).content
        (law.obligationAt occurrence action.left).content) ∧
      Nonempty (law.vocabulary.LocalDischargePreservedAt
        action.split.receipt.sourceEvent
        (law.obligationAt occurrence
          (action.successor.ledgerEvolution.origin action.left).1).content
        (law.obligationAt occurrence action.right).content) :=
  childConsumers_exact_origin_and_local_discharge_at initialVisit

theorem childConsumers_do_not_mint_living_causal_authority : True :=
  childConsumers_do_not_mint_living_causal_authority_at initialVisit

end
end M14ProofCarryingDefaultSideLossAllocationConsumers
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingDefaultSideLossAllocationConsumers.leftChildConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingDefaultSideLossAllocationConsumers.rightChildConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingDefaultSideLossAllocationConsumers.childConsumers_exact_origin_and_local_discharge
