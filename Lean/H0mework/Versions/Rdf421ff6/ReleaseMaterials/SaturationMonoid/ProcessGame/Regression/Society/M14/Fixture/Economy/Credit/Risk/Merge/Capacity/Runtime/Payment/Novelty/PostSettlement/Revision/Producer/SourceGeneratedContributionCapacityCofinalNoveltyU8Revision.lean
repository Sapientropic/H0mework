import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Failure.Producer.SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Revision
import H0mework.Versions.R2.Foundation.Inquiry.RevisionRecovery
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Revision.SourceGeneratedPostSettlementObserverSubmissionFirstRowU8Revision

/-!
# Cofinal novelty consumes the existing visit-polymorphic U8 revision

The exact external payment visits selected by one cofinal novelty already
index the established M9 failure frontier, typed revision source, faithful
coface factorization and first whole-ledger write.  This file installs no new
revision compiler or recovery court; it only packages those existing
visit-polymorphic producers behind the paid novelty source.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open ConstructiveRoot.TypedSemanticWorldNetworkU8Lifecycle
open ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8Revision
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
open M14SourceGeneratedPostSettlementObserverSubmissionU8

inductive SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary}
    (rootedBridge :
      SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
        novelty) : Type 31
  | private generated

def sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary}
    (rootedBridge :
      SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
        novelty) :
    SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
      rootedBridge :=
  .generated

namespace SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary}
  {rootedBridge :
    SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty}
  (revisionBridge :
    SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
      rootedBridge)

def leftRootVisit := by
  cases revisionBridge
  exact rootedBridge.leftRootVisit

def rightRootVisit := by
  cases revisionBridge
  exact rootedBridge.rightRootVisit

def leftCore :=
  jointCoreAt (leftRootVisit revisionBridge)

def rightCore :=
  by
    cases revisionBridge
    exact augmentedU8CoreAt oldVisit sourceIndex boundary

set_option linter.defProp false in
def leftRealizationCertification :=
  realizationCertificationAt (leftRootVisit revisionBridge)

set_option linter.defProp false in
def rightRealizationCertification :=
  by
    cases revisionBridge
    exact augmentedRealizationCertificationAt oldVisit sourceIndex boundary

def leftCofaceFactorization :=
  (leftCore revisionBridge).cofaceFactorization

def rightCofaceFactorization :=
  (rightCore revisionBridge).cofaceFactorization

def leftFirstWrite :=
  (leftCofaceFactorization revisionBridge).2.firstWrite

def rightFirstWrite :=
  (rightCofaceFactorization revisionBridge).2.firstWrite

def leftFirstWriteConsumes :=
  (leftCofaceFactorization revisionBridge).2.firstWriteConsumes

def rightFirstWriteConsumes :=
  (rightCofaceFactorization revisionBridge).2.firstWriteConsumes

def leftRecovery :=
  factorizesThroughInitialCofaceAnswerAndNext
    (leftCore revisionBridge).revision

def rightRecovery :=
  factorizesThroughInitialCofaceAnswerAndNext
    (rightCore revisionBridge).revision

def leftRevisedLivingRoot :=
  (leftCore revisionBridge).revision.generate.newLivingRoot

def rightRevisedLivingRoot :=
  (rightCore revisionBridge).revision.generate.newLivingRoot

@[simp] theorem leftCore_rooted_exact :
    (leftCore revisionBridge).frontier.rooted =
      rootedBridge.leftRootedFailure :=
  frontier_rooted_eq_at (leftRootVisit revisionBridge)

@[simp] theorem rightCore_rooted_exact :
    (rightCore revisionBridge).frontier.rooted =
      rootedBridge.rightRootedFailure :=
  frontier_rooted_eq_at (rightRootVisit revisionBridge)

@[simp] theorem leftCore_coface_exact :
    (leftCore revisionBridge).frontier.coface =
      rootedBridge.leftMinimalCoface :=
  frontier_coface_eq_at (leftRootVisit revisionBridge)

@[simp] theorem rightCore_coface_exact :
    (rightCore revisionBridge).frontier.coface =
      rootedBridge.rightMinimalCoface :=
  frontier_coface_eq_at (rightRootVisit revisionBridge)

theorem leftRevisionCertified :
    SourceNativeInquiryCofaceRealizationCertificationAt
      (realizationCandidateAt (leftRootVisit revisionBridge))
      (leftCore revisionBridge) :=
  leftRealizationCertification revisionBridge

theorem rightRevisionCertified :
    SourceNativeInquiryCofaceRealizationCertificationAt
      (realizationCandidateAt (rightRootVisit revisionBridge))
      (rightCore revisionBridge) :=
  rightRealizationCertification revisionBridge

theorem bothFaithfulCofaceFactorizations :
    Nonempty
        (FaithfulCofaceMorphism
          rootedBridge.leftMinimalCoface
          (leftCore revisionBridge).revision.generate.toAdmissibleMinimalCoface) ∧
      Nonempty
        (FaithfulCofaceMorphism
          rootedBridge.rightMinimalCoface
          (rightCore revisionBridge).revision.generate.toAdmissibleMinimalCoface) := by
  rw [← leftCore_coface_exact revisionBridge,
    ← rightCore_coface_exact revisionBridge]
  exact
    ⟨⟨(leftCofaceFactorization revisionBridge).1⟩,
      ⟨(rightCofaceFactorization revisionBridge).1⟩⟩

theorem bothAttachedFirstWrites :
    Nonempty
        (SourceGeneratedAttachedCofaceRealizationAt
          (leftCore revisionBridge).revision.generate) ∧
      Nonempty
        (SourceGeneratedAttachedCofaceRealizationAt
          (rightCore revisionBridge).revision.generate) :=
  ⟨⟨(leftCofaceFactorization revisionBridge).2⟩,
    ⟨(rightCofaceFactorization revisionBridge).2⟩⟩

theorem bothIndependentRecoveryCourts :
    Nonempty
        (SourceNativeLivingCausalEntryAnswerAndNextAt
          (leftCore revisionBridge).revision.generate.newLivingRoot
          (oldFirstWriteSuccessor (leftCore revisionBridge).revision).targetVisit
          (oldFirstWriteSuccessor (leftCore revisionBridge).revision).targetEntry
          (oldFirstWriteTargetAuthority
            (leftCore revisionBridge).revision)) ∧
      Nonempty
        (SourceNativeLivingCausalEntryAnswerAndNextAt
          (rightCore revisionBridge).revision.generate.newLivingRoot
          (newFirstWriteSuccessor
            (rightCore revisionBridge).revision).targetVisit
          (newFirstWriteSuccessor
            (rightCore revisionBridge).revision).targetEntry
          (newFirstWriteTargetAuthority
            (rightCore revisionBridge).revision)) :=
  ⟨⟨(leftRecovery revisionBridge).2.1⟩,
    ⟨(rightRecovery revisionBridge).2.2⟩⟩

theorem leftFirstWrite_isCompilerGenerated :
    leftFirstWrite revisionBridge =
      (leftCore revisionBridge).cofaceFactorization.2.firstWrite :=
  rfl

theorem rightFirstWrite_isCompilerGenerated :
    rightFirstWrite revisionBridge =
      (rightCore revisionBridge).cofaceFactorization.2.firstWrite :=
  rfl

end SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt

theorem contributionCapacityCofinalNovelty_generatesU8Revision
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ boundary : Nat,
      let novelty :=
        sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
          sourceIndex boundary
      let rootedBridge :=
        sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
          novelty
      Nonempty
        (SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
          rootedBridge) :=
  fun boundary =>
    ⟨sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
      (sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
        (sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
          sourceIndex boundary))⟩

theorem cofinalNoveltyU8Revision_hasNoCallerCofaceOrTarget
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : True := by
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  let rootedBridge :=
    sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
  let revisionBridge :=
    sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt rootedBridge
  fail_if_success exact revisionBridge.coface
  fail_if_success exact revisionBridge.revision
  fail_if_success exact revisionBridge.firstWrite
  fail_if_success exact revisionBridge.targetRoot
  fail_if_success exact revisionBridge.coverage
  fail_if_success exact revisionBridge.recoveryCourt
  fail_if_success exact revisionBridge.future
  fail_if_success exact revisionBridge.registry
  trivial

end
end M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision.sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision.SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt.bothFaithfulCofaceFactorizations
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision.SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt.bothAttachedFirstWrites
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision.SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt.bothIndependentRecoveryCourts
