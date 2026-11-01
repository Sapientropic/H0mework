import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Code.SourceGeneratedContributionCapacityFinitePrefixOperationalCode
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Root.SourceInstalledPostSettlementObserverSubmissionRevisedRoot
import H0mework.Versions.R2.Foundation.Source.SequentialAction

/-!
# Source material for the representation-intent action

The action starts at current `1` of the already installed augmented revised-Q
root.  Its current-`0` split has therefore already happened: the source ledger
is the existing three-row loss-allocation target ledger.  The selected source
entry is its existing target-obstruction row.

The private material seal joins that exact source occurrence to the canonical
finite-prefix breaking.  It stores no target world, theory, failure, U7 choice,
ledger, successor or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference
open M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking
open M14SourceGeneratedContributionCapacityFinitePrefixOperationalCode
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedPostSettlementObserverSubmissionU8

abbrev ActionSourceNAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  AugmentedNewNAt oldVisit sourceIndex boundary

def representationIntentActionSourceRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  augmentedRevisedLivingRootAt oldVisit sourceIndex boundary

/-- The sequential action consumes the first post-split revised-Q current. -/
def representationIntentActionSourceVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  (augmentedInitialVisitAt oldVisit sourceIndex boundary).next rfl

def representationIntentActionSourceEntryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    OpenResponsibilityAt (ActionSourceNAt oldVisit sourceIndex boundary)
      ((representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          ((representationIntentActionSourceRootAt oldVisit sourceIndex
            boundary).emitted
              (representationIntentActionSourceVisitAt oldVisit sourceIndex
                boundary).current)) :=
  (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
    ).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext rfl
      (M9ProofCarryingRenewalU8RevisedLedger.newRevisedEntryAt
        (oldRootVisitAt oldVisit sourceIndex boundary))

def representationIntentActionSourceAuthorityAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary)
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)
      (representationIntentActionSourceEntryAt oldVisit sourceIndex boundary) :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (representationIntentActionSourceRootAt oldVisit sourceIndex boundary)
    (M9ProofCarryingRenewalU8RevisedLedger.newRevisedEntryAt
      (oldRootVisitAt oldVisit sourceIndex boundary))
    (augmentedNewEntryRowAt oldVisit sourceIndex boundary)).next rfl

def representationIntentActionExactSourceEventAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary) :=
  (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
    ).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)

@[simp] theorem representationIntentActionSourceVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary
      ).current = 1 :=
  rfl

@[simp] theorem representationIntentActionExactSourceEvent_occurrence_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentActionExactSourceEventAt oldVisit sourceIndex
      boundary).occurrence =
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).emitted 1 :=
  rfl

@[simp] theorem representationIntentActionSourceEntry_existingTarget_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (representationIntentActionSourceEntryAt oldVisit sourceIndex boundary)
      (M9ProofCarryingRenewalU8RevisedLedger.revisedTargetObstructionAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  HEq.rfl

/-- Private event-local join between the existing current-`1` occurrence and
the canonical later-pair breaking. -/
structure SourceGeneratedRepresentationIntentActionMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)) :
    Type 32 where
  private mk ::
  sourceOccurrenceExact : sourceEvent.occurrence =
    (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
      ).emitted 1
  breakingGenerated :
    M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking.CanonicalFinitePrefixRepresentationBreakingAt
      oldVisit sourceIndex boundary

def sourceGeneratedRepresentationIntentActionMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)) :
    SourceGeneratedRepresentationIntentActionMaterialAt oldVisit sourceIndex
      boundary sourceEvent where
  sourceOccurrenceExact := by
    have generated_eq := congrArg
      (fun generated => generated.occurrence) sourceEvent.eq_generated
    change sourceEvent.occurrence =
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).emitted 1 at generated_eq
    exact generated_eq
  breakingGenerated :=
    sourceGeneratedFinitePrefixRepresentationBreakingAt oldVisit sourceIndex
      boundary

theorem representationIntentActionMaterial_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let sourceEvent :=
      representationIntentActionExactSourceEventAt oldVisit sourceIndex boundary
    let material := sourceGeneratedRepresentationIntentActionMaterialAt
      oldVisit sourceIndex boundary sourceEvent
    (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary
      ).current = 1 ∧
      type_of%
        (representationIntentActionSourceEntry_existingTarget_exact oldVisit
          sourceIndex boundary) ∧
      type_of% material.sourceOccurrenceExact ∧
      type_of% material.breakingGenerated.sameInstalledVisibleDifferentK ∧
      type_of% material.breakingGenerated.exactPaymentsConsumed ∧
      (∀ channel : EssentialAccessChannel,
        type_of%
          (material.breakingGenerated.independentConsumerReturnsEveryChannel
            channel)) ∧
      type_of% material.breakingGenerated.independentConsumerOwnsAndConsumes := by
  dsimp
  exact
    ⟨rfl, representationIntentActionSourceEntry_existingTarget_exact oldVisit
      sourceIndex boundary,
      (sourceGeneratedRepresentationIntentActionMaterialAt oldVisit sourceIndex
        boundary
        (representationIntentActionExactSourceEventAt oldVisit sourceIndex
          boundary)).sourceOccurrenceExact,
      (sourceGeneratedRepresentationIntentActionMaterialAt oldVisit sourceIndex
        boundary
        (representationIntentActionExactSourceEventAt oldVisit sourceIndex
          boundary)).breakingGenerated.sameInstalledVisibleDifferentK,
      (sourceGeneratedRepresentationIntentActionMaterialAt oldVisit sourceIndex
        boundary
        (representationIntentActionExactSourceEventAt oldVisit sourceIndex
          boundary)).breakingGenerated.exactPaymentsConsumed,
      (sourceGeneratedRepresentationIntentActionMaterialAt oldVisit sourceIndex
        boundary
        (representationIntentActionExactSourceEventAt oldVisit sourceIndex
          boundary)).breakingGenerated.independentConsumerReturnsEveryChannel,
      (sourceGeneratedRepresentationIntentActionMaterialAt oldVisit sourceIndex
        boundary
        (representationIntentActionExactSourceEventAt oldVisit sourceIndex
          boundary)).breakingGenerated.independentConsumerOwnsAndConsumes⟩

end
end M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial.sourceGeneratedRepresentationIntentActionMaterialAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial.representationIntentActionMaterial_directConsumer
