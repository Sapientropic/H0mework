import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Producer.SourceGeneratedContributionCapacityCofinalProductiveNovelty

/-!
# Proof-carrying cofinal productive novelty

The consumer keeps both later paid replays, their exact Payments, canonical
paid steps and channel witness returns live while consuming the cross-path
kernel obstruction.  It also certifies that the current post-root
`rootSemantic` epoch has no expressibility-failure inhabitant, so the novelty
cannot be mislabeled as an already installed self-U8.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityCofinalProductiveNovelty

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M3FiniteExchangeFixture
open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty

inductive ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary) :
    Type 29
  | private consumed

def proofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary) :
    ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt
      novelty :=
  .consumed

namespace ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary}
  (consumer :
    ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt
      novelty)

def leftReplay := by
  cases consumer
  exact novelty.leftReplay

def rightReplay := by
  cases consumer
  exact novelty.rightReplay

def leftPayment := (leftReplay consumer).2.payment

def rightPayment := (rightReplay consumer).2.payment

def leftPaidStep := (leftReplay consumer).2.paidStep

def rightPaidStep := (rightReplay consumer).2.paidStep

def leftChannel (channel : EssentialAccessChannel) :=
  (leftReplay consumer).2.channel channel

def rightChannel (channel : EssentialAccessChannel) :=
  (rightReplay consumer).2.channel channel

def leftWitnessReturn (channel : EssentialAccessChannel) :=
  (leftReplay consumer).2.witnessReturn channel

def rightWitnessReturn (channel : EssentialAccessChannel) :=
  (rightReplay consumer).2.witnessReturn channel

def kernelPair := by
  cases consumer
  exact novelty.kernelPair

theorem bothStrictlyLater :
    boundary < (leftReplay consumer).2.current ∧
      boundary < (rightReplay consumer).2.current := by
  cases consumer
  exact ⟨novelty.leftLater, novelty.rightLater⟩

theorem actualPathsDifferent :
    (leftReplay consumer).2.actualPath ≠
      (rightReplay consumer).2.actualPath := by
  cases consumer
  exact novelty.actualPaths_ne

theorem exactPaymentsConsumed :
    (leftPaidStep consumer).2.sourcePayment = leftPayment consumer ∧
      (rightPaidStep consumer).2.sourcePayment = rightPayment consumer := by
  cases consumer
  exact
    ⟨(novelty.leftReplay).2.paidStep_consumes_exactPayment,
      (novelty.rightReplay).2.paidStep_consumes_exactPayment⟩

theorem channelWitnessesReturnToEachSource
    (channel : EssentialAccessChannel) :
    (leftWitnessReturn consumer channel).1.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          (leftWitnessReturn consumer channel).1 = channelRelation channel ∧
      (rightWitnessReturn consumer channel).1.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          (rightWitnessReturn consumer channel).1 = channelRelation channel := by
  cases consumer
  exact
    ⟨(novelty.leftReplay).2.channelWitnessReturnsToSource channel |>.1,
      (novelty.leftReplay).2.channelWitnessReturnsToSource channel |>.2,
      (novelty.rightReplay).2.channelWitnessReturnsToSource channel |>.1,
      (novelty.rightReplay).2.channelWitnessReturnsToSource channel |>.2⟩

theorem channelPaymentsReturnToEachActualExit
    (channel : EssentialAccessChannel) :
    (leftChannel consumer channel).2.rootReadCarrier.existingPaymentOccurrence =
        (leftReplay consumer).2.futureBirth.actualExit.paymentOccurrence ∧
      (rightChannel consumer channel).2.rootReadCarrier.existingPaymentOccurrence =
        (rightReplay consumer).2.futureBirth.actualExit.paymentOccurrence := by
  cases consumer
  exact
    ⟨(novelty.leftReplay).2.channelPayment_exact channel,
      (novelty.rightReplay).2.channelPayment_exact channel⟩

theorem sameRealNormalForm_differentActualK :
    let observer :=
      contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex
    observer.forget (leftReplay consumer) =
        observer.forget (rightReplay consumer) ∧
      observer.authorityK (leftReplay consumer) ≠
        observer.authorityK (rightReplay consumer) := by
  cases consumer
  exact novelty.sameNormalForm_differentK

theorem noOccurrenceReconstruction
    (receipt :
      ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt
        novelty) :
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget := by
  cases receipt
  exact novelty.noOccurrenceReconstruction

theorem noAuthorityFactorization
    (receipt :
      ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt
        novelty) :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex)) := by
  cases receipt
  exact novelty.noAuthorityFactorization

theorem noFaithfulReconstruction
    (receipt :
      ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt
        novelty) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex)) := by
  cases receipt
  exact novelty.noFaithfulReconstruction

end ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt

abbrev ConsumedContributionCapacityCofinalProductiveNoveltyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  Sigma fun novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary =>
    ProofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt novelty

def proofCarryingContributionCapacityCofinalProductiveNoveltyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConsumedContributionCapacityCofinalProductiveNoveltyAt oldVisit sourceIndex
      boundary :=
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  ⟨novelty,
    proofCarryingContributionCapacityCofinalProductiveNoveltyConsumerAt
      novelty⟩

/-- The current post-root epoch deliberately uses the faithful root semantic;
there is no legal way to retype this novelty as an already installed failure. -/
theorem contributionCapacityPostSettlementRootSemantic_failureIsEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {support : (JointSettlementNAt oldVisit).Support}
    (obstruction : (JointSettlementNAt oldVisit).ObstructionAt support) :
    IsEmpty
      (ActualExpressibilityFailure
        (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
          ).source.base.lawSurface obstruction) := by
  rw [contributionCapacityPostSettlementRenewalRoot_lawSurface_exact]
  exact TheoryState.rootSemantic_actualExpressibilityFailure_isEmpty
    (JointSettlementNAt oldVisit) obstruction

structure ProofCarryingContributionCapacityCofinalProductiveNoveltyCertificateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  cofinalConsumed : ∀ boundary : Nat,
    Nonempty
      (ConsumedContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary)
  eachPairLater : ∀ boundary : Nat,
    let consumed :=
      proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary
    boundary < consumed.2.leftReplay.2.current ∧
      boundary < consumed.2.rightReplay.2.current
  eachPairPaid : ∀ boundary : Nat,
    let consumed :=
      proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary
    consumed.2.leftPaidStep.2.sourcePayment = consumed.2.leftPayment ∧
      consumed.2.rightPaidStep.2.sourcePayment = consumed.2.rightPayment
  everyChannelReturns : ∀ boundary : Nat, ∀ channel : EssentialAccessChannel,
    let consumed :=
      proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary
    (consumed.2.leftWitnessReturn channel).1.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          (consumed.2.leftWitnessReturn channel).1 = channelRelation channel ∧
      (consumed.2.rightWitnessReturn channel).1.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        channelActor channel ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          (consumed.2.rightWitnessReturn channel).1 = channelRelation channel
  eachPairDifferentPaths : ∀ boundary : Nat,
    let consumed :=
      proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary
    consumed.2.leftReplay.2.actualPath ≠
      consumed.2.rightReplay.2.actualPath
  eachPairSameNormalDifferentK : ∀ boundary : Nat,
    let consumed :=
      proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let observer :=
      contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex
    observer.forget consumed.2.leftReplay =
        observer.forget consumed.2.rightReplay ∧
      observer.authorityK consumed.2.leftReplay ≠
        observer.authorityK consumed.2.rightReplay
  noFaithfulReconstruction :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex))
  currentRootSemanticHasNoFailure :
    ∀ {support : (JointSettlementNAt oldVisit).Support},
      ∀ obstruction : (JointSettlementNAt oldVisit).ObstructionAt support,
        IsEmpty
          (ActualExpressibilityFailure
            (ContributionCapacityPostSettlementRenewalRootAt oldVisit
              sourceIndex).source.base.lawSurface obstruction)

theorem proofCarryingContributionCapacityCofinalProductiveNovelty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityCofinalProductiveNoveltyCertificateAt
      oldVisit sourceIndex where
  cofinalConsumed := fun boundary =>
    ⟨proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
      sourceIndex boundary⟩
  eachPairLater := fun boundary =>
    (proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
      sourceIndex boundary).2.bothStrictlyLater
  eachPairPaid := fun boundary =>
    (proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
      sourceIndex boundary).2.exactPaymentsConsumed
  everyChannelReturns := fun boundary channel =>
    (proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
      sourceIndex boundary).2.channelWitnessesReturnToEachSource channel
  eachPairDifferentPaths := fun boundary =>
    (proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
      sourceIndex boundary).2.actualPathsDifferent
  eachPairSameNormalDifferentK := fun boundary =>
    (proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
      sourceIndex boundary).2.sameRealNormalForm_differentActualK
  noFaithfulReconstruction :=
    M14SourceGeneratedContributionCapacityCofinalProductiveNovelty.SourceProductiveNoveltyAt.noFaithfulReconstruction
      (sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex 0)
  currentRootSemanticHasNoFailure := fun obstruction =>
    contributionCapacityPostSettlementRootSemantic_failureIsEmpty oldVisit
      sourceIndex obstruction

set_option linter.unusedVariables false in
theorem bareReadoutsCannotRetypeAsCofinalProductiveNovelty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : True := by
  let leftReplay :=
    contributionCapacityPostSettlementNoveltyLeftReplayAt oldVisit sourceIndex
      boundary
  fail_if_success exact
    (leftReplay : SourceProductiveNoveltyAt oldVisit sourceIndex boundary)
  fail_if_success exact
    (leftReplay.2.payment :
      SourceProductiveNoveltyAt oldVisit sourceIndex boundary)
  fail_if_success exact
    (leftReplay.2.singletonPulse :
      SourceProductiveNoveltyAt oldVisit sourceIndex boundary)
  fail_if_success exact
    (leftReplay.2.authorityK :
      SourceProductiveNoveltyAt oldVisit sourceIndex boundary)
  fail_if_success exact
    (leftReplay.2.channel tenureAuthority :
      SourceProductiveNoveltyAt oldVisit sourceIndex boundary)
  trivial

end
end M14ProofCarryingContributionCapacityCofinalProductiveNovelty
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityCofinalProductiveNovelty.proofCarryingContributionCapacityCofinalProductiveNovelty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityCofinalProductiveNovelty.contributionCapacityPostSettlementRootSemantic_failureIsEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityCofinalProductiveNovelty.bareReadoutsCannotRetypeAsCofinalProductiveNovelty
