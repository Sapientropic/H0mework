import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Pulse.Producer.SourceGeneratedContributionCapacityFutureBirthPulse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Producer.SourceGeneratedContributionCapacityPostSettlementFutureBirth

/-!
# Post-settlement future-birth pulse

Finite post-root frontiers are generated on demand and observed only through
their length.  The strongest two-point counterexample crosses the actual
settlement boundary: reopening current three and post-settlement current
fifteen have the same singleton pulse normal form, while both their actual
service authority `K` and their compiler-generated next are different.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacitySettlementNoEmptyHandoff
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14UBIPeriodicActualServiceCapacity

abbrev AnyContributionCapacityPostSettlementFutureBirth
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Sigma fun index : Nat =>
    SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index

def contributionCapacityPostSettlementFutureBirthOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AnyContributionCapacityPostSettlementFutureBirth oldVisit sourceIndex :=
  ⟨index,
    sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index⟩

theorem contributionCapacityPostSettlementFutureBirthOccurrenceAt_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (contributionCapacityPostSettlementFutureBirthOccurrenceAt oldVisit
        sourceIndex) := by
  intro left right equality
  exact congrArg Sigma.fst equality

def sourceGeneratedFiniteContributionCapacityPostSettlementFutureBirthFrontier
    (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    List (AnyContributionCapacityPostSettlementFutureBirth oldVisit
      sourceIndex) :=
  (List.range horizon).map fun offset =>
    contributionCapacityPostSettlementFutureBirthOccurrenceAt oldVisit
      sourceIndex (start + offset)

def sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
    (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    ContributionCapacityFutureBirthPulse :=
  (sourceGeneratedFiniteContributionCapacityPostSettlementFutureBirthFrontier
    oldVisit sourceIndex start horizon).length

@[simp] theorem contributionCapacityPostSettlementFutureBirthPulse_eq_horizon
    (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
        oldVisit sourceIndex start horizon =
      horizon := by
  simp [sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse,
    sourceGeneratedFiniteContributionCapacityPostSettlementFutureBirthFrontier]

theorem contributionCapacityPostSettlementFutureBirthFrontier_nodup
    (oldVisit : OldVisit) (sourceIndex start horizon : Nat) :
    (sourceGeneratedFiniteContributionCapacityPostSettlementFutureBirthFrontier
      oldVisit sourceIndex start horizon).Nodup := by
  apply List.nodup_range.map
  intro left right equality
  have index_eq := congrArg Sigma.fst equality
  change start + left = start + right at index_eq
  omega

/-! ## Cross-settlement same-normal-form / different-authority pair -/

abbrev CrossSettlementContributionCapacityFutureBirth
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex 2 ⊕
    SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex 0

def contributionCapacityBeforeSettlementFutureBirth
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    CrossSettlementContributionCapacityFutureBirth oldVisit sourceIndex :=
  Sum.inl
    (sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex 2)

def contributionCapacityAfterSettlementFutureBirth
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    CrossSettlementContributionCapacityFutureBirth oldVisit sourceIndex :=
  Sum.inr
    (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex 0)

def contributionCapacityCrossSettlementFutureBirthPulseObserver
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AuthorityObserver
      (CrossSettlementContributionCapacityFutureBirth oldVisit sourceIndex)
      ContributionCapacityFutureBirthPulse AnyPeriodicActualServiceExit where
  forget := fun birth =>
    match birth with
    | .inl _ =>
        sourceGeneratedContributionCapacityFutureBirthPulse oldVisit
          sourceIndex 2 1
    | .inr _ =>
        sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
          oldVisit sourceIndex 0 1
  authorityK := fun birth =>
    match birth with
    | .inl _ =>
        periodicActualServiceExitOccurrenceAt
          (contributionCapacityFutureBirthDepth sourceIndex 2)
    | .inr _ =>
        periodicActualServiceExitOccurrenceAt
          (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
            sourceIndex 0)

def contributionCapacityCrossSettlementFutureBirthPulseKernelPair
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AuthorityKernelPair
      (contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
        sourceIndex) where
  left := contributionCapacityBeforeSettlementFutureBirth oldVisit sourceIndex
  right := contributionCapacityAfterSettlementFutureBirth oldVisit sourceIndex
  occurrence_ne := by
    intro equality
    cases equality
  visible_eq := by
    simp [contributionCapacityCrossSettlementFutureBirthPulseObserver,
      contributionCapacityBeforeSettlementFutureBirth,
      contributionCapacityAfterSettlementFutureBirth]
  authority_ne := by
    exact
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt.reopeningAndPostSettlementActualExitOccurrences_distinct
        (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := 0)

/-- Strong cross-occurrence theorem: the actual macro branch contains two
different births with one classical pulse normal form but different `K`. -/
theorem contributionCapacityCrossSettlement_samePulse_differentK
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let observer :=
      contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
        sourceIndex
    observer.forget
        (contributionCapacityBeforeSettlementFutureBirth oldVisit sourceIndex) =
      observer.forget
        (contributionCapacityAfterSettlementFutureBirth oldVisit sourceIndex) ∧
    observer.authorityK
        (contributionCapacityBeforeSettlementFutureBirth oldVisit sourceIndex) ≠
      observer.authorityK
        (contributionCapacityAfterSettlementFutureBirth oldVisit sourceIndex) :=
  ⟨(contributionCapacityCrossSettlementFutureBirthPulseKernelPair oldVisit
      sourceIndex).visible_eq,
    (contributionCapacityCrossSettlementFutureBirthPulseKernelPair oldVisit
      sourceIndex).authority_ne⟩

theorem contributionCapacityCrossSettlementPulse_noOccurrenceReconstruction
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        CrossSettlementContributionCapacityFutureBirth oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
          sourceIndex).forget :=
  (contributionCapacityCrossSettlementFutureBirthPulseKernelPair oldVisit
    sourceIndex).noOccurrenceLeftInverse

theorem contributionCapacityCrossSettlementPulse_noAuthorityFactorization
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
          sourceIndex)) :=
  (contributionCapacityCrossSettlementFutureBirthPulseKernelPair oldVisit
    sourceIndex).noAuthorityFactorization

theorem contributionCapacityCrossSettlementPulse_noFaithfulReconstruction
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
          sourceIndex)) :=
  (contributionCapacityCrossSettlementFutureBirthPulseKernelPair oldVisit
    sourceIndex).noFaithfulAuthorityReconstruction

/-! ## The same normal form also loses the actual macro next -/

/-- Common carrier of actual living currents indexed by their real semantic
network.  This is not a branch tag: both values below are complete generated
root/current/visit triples. -/
abbrev AnyContributionCapacityMacroAuthoritativeCurrent :=
  Sigma fun network : WorldRelationNetwork =>
    SourceNativeAuthoritativeRootCurrentAt network

/-- Actual left endpoint: the macro next selected by the paid settlement
action at reopening current three. -/
def contributionCapacitySettlementActionActualMacroNextAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AnyContributionCapacityMacroAuthoritativeCurrent :=
  ⟨ReopeningNAt oldVisit,
    (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex 0).settlementCrossRootPayment.nextPaidBy⟩

/-- Actual right endpoint: the next reachable post-payment living current. -/
def contributionCapacityPostSettlementPaymentActualMacroNextAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AnyContributionCapacityMacroAuthoritativeCurrent :=
  ⟨JointSettlementNAt oldVisit,
    ⟨PostSettlementRenewalVAt oldVisit,
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot,
      contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        1⟩⟩

theorem contributionCapacitySettlementActionActualMacroNext_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacitySettlementActionActualMacroNextAt oldVisit
      sourceIndex).2 =
      (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex 0).settlementCrossRootPayment.nextPaidBy :=
  rfl

/-- The occurrence emitted by the right common-carrier current is precisely
the `NextPaidBy` projected from the post payment. -/
theorem contributionCapacityPostSettlementPaymentActualMacroNextOccurrence_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex 0).nextPaidOccurrence =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (show Nat from
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit
            sourceIndex 1).current) := by
  rw [SourceGeneratedContributionCapacityPostSettlementFutureBirthAt.nextPaidOccurrence_exact]
  congr 1

theorem contributionCapacityActualMacroNexts_distinct
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    contributionCapacitySettlementActionActualMacroNextAt oldVisit
        sourceIndex ≠
      contributionCapacityPostSettlementPaymentActualMacroNextAt oldVisit
        sourceIndex := by
  intro equality
  have current_type_eq := congrArg
    (fun next : AnyContributionCapacityMacroAuthoritativeCurrent =>
      next.2.V.Current) equality
  change Bool = Nat at current_type_eq
  exact contributionCapacityJointSettlementBool_ne_nat current_type_eq

def contributionCapacityCrossSettlementFutureBirthNextPulseObserver
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AuthorityObserver
      (CrossSettlementContributionCapacityFutureBirth oldVisit sourceIndex)
      ContributionCapacityFutureBirthPulse
      AnyContributionCapacityMacroAuthoritativeCurrent where
  forget := fun birth =>
    match birth with
    | .inl _ =>
        sourceGeneratedContributionCapacityFutureBirthPulse oldVisit
          sourceIndex 2 1
    | .inr _ =>
        sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
          oldVisit sourceIndex 0 1
  authorityK := fun birth =>
    match birth with
    | .inl _ =>
        contributionCapacitySettlementActionActualMacroNextAt oldVisit
          sourceIndex
    | .inr _ =>
        contributionCapacityPostSettlementPaymentActualMacroNextAt oldVisit
          sourceIndex

def contributionCapacityCrossSettlementFutureBirthNextPulseKernelPair
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AuthorityKernelPair
      (contributionCapacityCrossSettlementFutureBirthNextPulseObserver
        oldVisit sourceIndex) where
  left := contributionCapacityBeforeSettlementFutureBirth oldVisit sourceIndex
  right := contributionCapacityAfterSettlementFutureBirth oldVisit sourceIndex
  occurrence_ne := by
    intro equality
    cases equality
  visible_eq := by
    simp [contributionCapacityCrossSettlementFutureBirthNextPulseObserver,
      contributionCapacityBeforeSettlementFutureBirth,
      contributionCapacityAfterSettlementFutureBirth]
  authority_ne :=
    contributionCapacityActualMacroNexts_distinct oldVisit sourceIndex

theorem contributionCapacityCrossSettlementPulse_noNextFactorization
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityCrossSettlementFutureBirthNextPulseObserver
          oldVisit sourceIndex)) :=
  (contributionCapacityCrossSettlementFutureBirthNextPulseKernelPair oldVisit
    sourceIndex).noAuthorityFactorization

set_option linter.unusedVariables false in
theorem barePostPulse_cannot_retype_asFutureBirth
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  fail_if_success exact
    ((1 : ContributionCapacityFutureBirthPulse) :
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index)
  trivial

end
end M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse.contributionCapacityPostSettlementFutureBirthPulse_eq_horizon
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse.contributionCapacityCrossSettlement_samePulse_differentK
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse.contributionCapacityCrossSettlementPulse_noAuthorityFactorization
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse.contributionCapacityCrossSettlementPulse_noNextFactorization
