import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Transport.SourceGeneratedContributionCapacityFinitePrefixRepresentationBreakingU8Transport
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Execution.Runtime.Consumer.ProofCarryingContributionCapacityRepresentationPairIntentSelfU8

/-!
# External-Q first-write to PairIntent open-runtime cascade

The existing external-Q self-U8 first write generates the exact current-`1`
source occurrence consumed by the PairIntent sequential action.  This module
closes that root/visit/row/authority/occurrence seam, then follows the already
generated local self-U8 into its all-finite-depth named runtime.

The causal splice does not identify the two revision courts.  The external-Q
revised current carrier is `Nat`; the local PairIntent revised carrier is
`Bool`.  Exact current and generated-next packages therefore remain distinct
at every finite local runtime depth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityExternalQPairIntentOpenRuntimeCascade

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8Lifecycle
open ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreaking
open M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreakingU8Transport
open M14SourceGeneratedContributionCapacityFinitePrefixRepresentationBreakingU8Transport.SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision.SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial
open M14SourceGeneratedSequentialContributionCapacityRepresentationPairIntent
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime
open M14ProofCarryingContributionCapacityRepresentationPairIntentSelfU8

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {breaking :
    CanonicalFinitePrefixRepresentationBreakingAt oldVisit sourceIndex
      boundary}

def externalQFirstWriteCore
    (transport :
      SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
        breaking) :=
  (externalSpan transport).targetRevisionBridge.rightCore

/-- The right first write of the external-Q self-U8 generates exactly the
root, visit, entry, authority and temporal occurrence used by the PairIntent
sequential action. -/
theorem externalQFirstWrite_pairIntentSource_exact
    (transport :
      SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
        breaking) :
    let core := externalQFirstWriteCore transport
    (externalSpan transport).targetRevisionBridge.rightFirstWrite =
        core.cofaceFactorization.2.firstWrite ∧
      HEq core.revision.generate.newLivingRoot
        (representationIntentActionSourceRootAt oldVisit sourceIndex
          boundary) ∧
      HEq (newFirstWriteSuccessor core.revision).targetVisit
        (representationIntentActionSourceVisitAt oldVisit sourceIndex
          boundary) ∧
      HEq (newFirstWriteSuccessor core.revision).targetEntry
        (representationIntentActionSourceEntryAt oldVisit sourceIndex
          boundary) ∧
      HEq (newFirstWriteTargetAuthority core.revision)
        (representationIntentActionSourceAuthorityAt oldVisit sourceIndex
          boundary) ∧
      HEq
        (core.revision.generate.newLivingRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt
            (newFirstWriteSuccessor core.revision).targetVisit)
        (representationIntentActionExactSourceEventAt oldVisit sourceIndex
          boundary) := by
  cases transport
  exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

def externalQFirstWriteTargetCurrent
    (transport :
      SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
        breaking) : AnyAuthoritativeRootCurrent :=
  let core := externalQFirstWriteCore transport
  { N := AugmentedNewNAt oldVisit sourceIndex boundary
    current :=
      { V := AugmentedNewVAt oldVisit sourceIndex boundary
        root := core.revision.generate.newLivingRoot.toAuthoritativeRoot
        visit := (newFirstWriteSuccessor core.revision).targetVisit } }

def externalQSelfU8GeneratedNext
    (transport :
      SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
        breaking) : AnyAuthoritativeRootCurrent :=
  { N := AugmentedNewNAt oldVisit sourceIndex boundary
    current := (externalSpan transport).targetSelfU8
      |>.newRowAnswerAndNext.nextCurrent }

def localPairIntentRevisedCurrent
    (oldVisit : OldVisit) (sourceIndex boundary depth : Nat) :
    AnyAuthoritativeRootCurrent :=
  ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
    (depth + 1)).engine.node.erase

def localPairIntentRevisedNext
    (oldVisit : OldVisit) (sourceIndex boundary depth : Nat) :
    AnyAuthoritativeRootCurrent :=
  ((representationIntentU8Runtime oldVisit sourceIndex boundary).tickAt
    (depth + 1)).next.node.erase

@[simp] theorem externalQFirstWriteTargetCurrent_currentCarrier
    (transport :
      SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
        breaking) :
    (externalQFirstWriteTargetCurrent transport).current.V.Current = Nat :=
  rfl

@[simp] theorem externalQSelfU8GeneratedNext_currentCarrier
    (transport :
      SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
        breaking) :
    (externalQSelfU8GeneratedNext transport).current.V.Current = Nat :=
  rfl

@[simp] theorem localPairIntentRevisedCurrent_currentCarrier
    (oldVisit : OldVisit) (sourceIndex boundary depth : Nat) :
    (localPairIntentRevisedCurrent oldVisit sourceIndex boundary depth
      ).current.V.Current = Bool := by
  unfold localPairIntentRevisedCurrent
  rw [representationIntentU8Runtime_stateAt_succ_node_exact]
  rfl

@[simp] theorem localPairIntentRevisedNext_currentCarrier
    (oldVisit : OldVisit) (sourceIndex boundary depth : Nat) :
    (localPairIntentRevisedNext oldVisit sourceIndex boundary depth
      ).current.V.Current = Bool := by
  unfold localPairIntentRevisedNext
  rw [representationIntentU8EveryRevisedTick_generatesNext]
  rfl

/-- The causal splice is not an authority collapse.  The exact external-Q
first-write target and its row-generated self-U8 next remain distinct from
both the current and next of every local PairIntent revised tick. -/
theorem externalQPairIntentAuthorityNoncollapse
    (transport :
      SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
        breaking)
    (depth : Nat) :
    externalQFirstWriteTargetCurrent transport ≠
        localPairIntentRevisedCurrent oldVisit sourceIndex boundary depth ∧
      externalQSelfU8GeneratedNext transport ≠
        localPairIntentRevisedCurrent oldVisit sourceIndex boundary depth ∧
      externalQSelfU8GeneratedNext transport ≠
        localPairIntentRevisedNext oldVisit sourceIndex boundary depth := by
  have carrierCard_ne : Nat.card Nat ≠ Nat.card Bool := by simp
  constructor
  · intro equality
    have cardEquality := congrArg
      (fun erased : AnyAuthoritativeRootCurrent =>
        Nat.card erased.current.V.Current) equality
    rw [externalQFirstWriteTargetCurrent_currentCarrier,
      localPairIntentRevisedCurrent_currentCarrier] at cardEquality
    exact carrierCard_ne cardEquality
  constructor
  · intro equality
    have cardEquality := congrArg
      (fun erased : AnyAuthoritativeRootCurrent =>
        Nat.card erased.current.V.Current) equality
    rw [externalQSelfU8GeneratedNext_currentCarrier,
      localPairIntentRevisedCurrent_currentCarrier] at cardEquality
    exact carrierCard_ne cardEquality
  · intro equality
    have cardEquality := congrArg
      (fun erased : AnyAuthoritativeRootCurrent =>
        Nat.card erased.current.V.Current) equality
    rw [externalQSelfU8GeneratedNext_currentCarrier,
      localPairIntentRevisedNext_currentCarrier] at cardEquality
    exact carrierCard_ne cardEquality

/-- Direct positive cascade: external-Q self-U8 generates the PairIntent
action source; that source generates the local reflexive self-U8; the same
named local runtime then remains query-generated and nonperiodic at every
finite depth. -/
theorem externalQFirstWrite_generatesPairIntentOpenRuntime
    (transport :
      SourceGeneratedFinitePrefixRepresentationBreakingU8TransportAt
        breaking) :
    type_of% (selfU8_firstWrite_isExistingCompilerWrite transport) ∧
      type_of% (externalQFirstWrite_pairIntentSource_exact transport) ∧
      type_of%
        (generatedRepresentationIntentAction_directConsumer oldVisit
          sourceIndex boundary) ∧
      type_of%
        (representationIntentReflexiveSelfU8_sameOccurrence oldVisit
          sourceIndex boundary) ∧
      type_of%
        (representationIntentU8Runtime_allFiniteGeneratedContinuation oldVisit
          sourceIndex boundary) ∧
      (∀ depth : Nat,
        type_of% (externalQPairIntentAuthorityNoncollapse transport depth)) :=
  ⟨selfU8_firstWrite_isExistingCompilerWrite transport,
    externalQFirstWrite_pairIntentSource_exact transport,
    generatedRepresentationIntentAction_directConsumer oldVisit sourceIndex
      boundary,
    representationIntentReflexiveSelfU8_sameOccurrence oldVisit sourceIndex
      boundary,
    representationIntentU8Runtime_allFiniteGeneratedContinuation oldVisit
      sourceIndex boundary,
    externalQPairIntentAuthorityNoncollapse transport⟩

end
end M14SourceGeneratedContributionCapacityExternalQPairIntentOpenRuntimeCascade
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityExternalQPairIntentOpenRuntimeCascade.externalQFirstWrite_pairIntentSource_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityExternalQPairIntentOpenRuntimeCascade.externalQPairIntentAuthorityNoncollapse
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityExternalQPairIntentOpenRuntimeCascade.externalQFirstWrite_generatesPairIntentOpenRuntime
