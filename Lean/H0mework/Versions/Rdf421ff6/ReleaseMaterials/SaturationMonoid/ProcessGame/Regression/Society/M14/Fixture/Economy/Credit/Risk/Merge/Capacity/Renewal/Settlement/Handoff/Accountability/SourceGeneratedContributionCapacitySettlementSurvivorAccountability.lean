import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Action.SourceGeneratedContributionCapacitySettlementState

/-!
# Complete survivor-ledger accountability

The terminal handoff leaves exactly two inherited live rows.  This module
generates causal authority and an independent answer consumer for either row
at every survivor current from the same emitted occurrence.  `Fin 2` is the
already certified complete inventory presentation, not a second registry.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementState
open M14UBIPeriodicActualServiceCapacity

abbrev CanonicalSurvivorRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex

def contributionCapacitySettlementSurvivorInitialEntryRowAt
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    (contributionCapacitySettlementSurvivorInitialGenerated oldVisit
      sourceIndex
      (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
        sourceIndex)).GeneratedEntryRowAt
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex) :=
  ((contributionCapacitySettlementSurvivorInitialGenerated oldVisit
    sourceIndex
    (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
      sourceIndex)).canonicalGeneratedEntryRow?
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)
    ).get (by
      refine Fin.cases ?_ (fun tail => ?_) entryIndex
      · rfl
      · change Fin 1 at tail
        have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
        subst tail
        rfl)

theorem contributionCapacitySettlementSurvivorNextEqAt
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat) :
    ((CanonicalSurvivorRootAt oldVisit sourceIndex).toAuthoritativeRoot.toRoot
        |>.evolutionAt
          (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
            currentIndex).current).nextCurrent? =
      some
        (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          (currentIndex + 1)).current :=
  rfl

theorem contributionCapacitySettlementSurvivorNextEntry_exact
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat)
    (entryIndex : Fin 2)
    (next_eq :
      ((CanonicalSurvivorRootAt oldVisit sourceIndex).toAuthoritativeRoot.toRoot
          |>.evolutionAt
            (contributionCapacitySettlementSurvivorVisitAt oldVisit
              sourceIndex currentIndex).current).nextCurrent? =
        some
          (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
            (currentIndex + 1)).current) :
    ((CanonicalSurvivorRootAt oldVisit sourceIndex).toAuthoritativeRoot.toLedgerRoot
        |>.canonicalTargetEntryAtNext next_eq
          (contributionCapacitySettlementSurvivorEntryAt oldVisit
            entryIndex)) =
      contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex := by
  refine Fin.cases ?_ (fun tail => ?_) entryIndex
  · rfl
  · change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    rfl

def contributionCapacitySettlementSurvivorEntryAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (currentIndex : Nat) → (entryIndex : Fin 2) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (CanonicalSurvivorRootAt oldVisit sourceIndex)
        (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          currentIndex)
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)
  | 0, entryIndex =>
      SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
        (CanonicalSurvivorRootAt oldVisit sourceIndex)
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)
        (contributionCapacitySettlementSurvivorInitialEntryRowAt oldVisit
          sourceIndex entryIndex)
  | currentIndex + 1, entryIndex =>
      by
        let next_eq := contributionCapacitySettlementSurvivorNextEqAt oldVisit
          sourceIndex currentIndex
        have advanced :=
          (contributionCapacitySettlementSurvivorEntryAuthorityAt oldVisit
            sourceIndex currentIndex entryIndex).next next_eq
        have entry_eq :=
          contributionCapacitySettlementSurvivorNextEntry_exact oldVisit
            sourceIndex currentIndex entryIndex next_eq
        exact Eq.mp
          (congrArg
            (fun entry => SourceNativeLivingTemporalCausalEntryAuthorityAt
              (CanonicalSurvivorRootAt oldVisit sourceIndex)
              ((contributionCapacitySettlementSurvivorVisitAt oldVisit
                sourceIndex currentIndex).next next_eq) entry)
            entry_eq)
          advanced

def contributionCapacitySettlementSurvivorEntryInquiryEventAt
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat) :=
  contributionCapacitySettlementSurvivorInquiryEventAt oldVisit sourceIndex
    currentIndex

def contributionCapacitySettlementSurvivorEntryAnswerFaceAt
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat)
    (entryIndex : Fin 2) :
    SourceNativeRootSemanticFaceAt
      (CanonicalSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
        currentIndex) where
  projection := ContributionCapacitySettlementSurvivorProjection.answer
    entryIndex
  active := PUnit.unit
  classifier_eq := rfl

def contributionCapacitySettlementSurvivorEntryAnswerConsumerAt
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat)
    (entryIndex : Fin 2) :
    SourceNativeInquiryAnswerConsumerAt ()
      (contributionCapacitySettlementSurvivorEntryInquiryEventAt oldVisit
        sourceIndex currentIndex)
      (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)
      (contributionCapacitySettlementSurvivorEntryAnswerFaceAt oldVisit
        sourceIndex currentIndex entryIndex) where
  projection := ContributionCapacitySettlementSurvivorProjection.consumer
    entryIndex
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def contributionCapacitySettlementSurvivorEntryCompilationAt
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat)
    (entryIndex : Fin 2) :
    SourceNativeInquiryCompilationAt
      (CanonicalSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
        currentIndex)
      (contributionCapacityReopeningU7 oldVisit)
      (contributionCapacityReopeningCalculus oldVisit)
      (contributionCapacityReopeningTheory oldVisit) ()
      (contributionCapacitySettlementSurvivorEntryInquiryEventAt oldVisit
        sourceIndex currentIndex)
      (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)
      (contributionCapacitySettlementSurvivorEntryAuthorityAt oldVisit
        sourceIndex currentIndex entryIndex) :=
  .answered
    (contributionCapacitySettlementSurvivorEntryAnswerFaceAt oldVisit
      sourceIndex currentIndex entryIndex)
    (contributionCapacitySettlementSurvivorEntryAnswerConsumerAt oldVisit
      sourceIndex currentIndex entryIndex)

theorem contributionCapacitySettlementSurvivorConsumerProjections_injective :
    Function.Injective
      ContributionCapacitySettlementSurvivorProjection.consumer := by
  intro left right equality
  cases equality
  rfl

/-- A consumer for one exact row cannot be retyped as the consumer projection
of the other survivor row. -/
theorem contributionCapacitySettlementSurvivorConsumers_distinct :
    ContributionCapacitySettlementSurvivorProjection.consumer 0 ≠
      ContributionCapacitySettlementSurvivorProjection.consumer 1 := by
  intro equality
  have index_eq :=
    contributionCapacitySettlementSurvivorConsumerProjections_injective
      equality
  omega

theorem contributionCapacitySettlementSurvivorAnswerValues_heq_injective
    {left right : Fin 2}
    (equality : HEq
      (ContributionCapacitySettlementSurvivorAnswer.canonical left)
      (ContributionCapacitySettlementSurvivorAnswer.canonical right)) :
    left = right := by
  have homogeneous :
      ContributionCapacitySettlementSurvivorAnswer.canonical left =
        ContributionCapacitySettlementSurvivorAnswer.canonical right :=
    eq_of_heq equality
  cases homogeneous
  rfl

/-- The two rows do not merely receive differently named projections: their
literal root-read answer seals cannot be heterogeneously retyped. -/
theorem contributionCapacitySettlementSurvivorAnswers_distinct :
    ¬ HEq
      (ContributionCapacitySettlementSurvivorAnswer.canonical 0)
      (ContributionCapacitySettlementSurvivorAnswer.canonical 1) := by
  intro equality
  have index_eq :=
    contributionCapacitySettlementSurvivorAnswerValues_heq_injective equality
  omega

theorem contributionCapacitySettlementSurvivorInquiryAnswerConsumer_distinct
    (left right : Fin 2) :
    ContributionCapacitySettlementSurvivorProjection.inquiry left ≠
        ContributionCapacitySettlementSurvivorProjection.answer right ∧
      ContributionCapacitySettlementSurvivorProjection.inquiry left ≠
        ContributionCapacitySettlementSurvivorProjection.consumer right ∧
      ContributionCapacitySettlementSurvivorProjection.answer left ≠
        ContributionCapacitySettlementSurvivorProjection.consumer right := by
  constructor
  · intro equality
    cases equality
  constructor
  · intro equality
    cases equality
  · intro equality
    cases equality

abbrev ContributionCapacitySettlementSurvivorAccountabilityAtCurrent
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat) : Prop :=
    ∀ entryIndex : Fin 2,
      Nonempty
          (SourceNativeLivingTemporalCausalEntryAuthorityAt
            (CanonicalSurvivorRootAt oldVisit sourceIndex)
            (contributionCapacitySettlementSurvivorVisitAt oldVisit
              sourceIndex currentIndex)
            (contributionCapacitySettlementSurvivorEntryAt oldVisit
              entryIndex)) ∧
        Nonempty
          (SourceNativeInquiryAnswerConsumerAt ()
            (contributionCapacitySettlementSurvivorEntryInquiryEventAt
              oldVisit sourceIndex currentIndex)
            (contributionCapacitySettlementSurvivorEntryAt oldVisit
              entryIndex)
            (contributionCapacitySettlementSurvivorEntryAnswerFaceAt oldVisit
              sourceIndex currentIndex entryIndex)) ∧
        Nonempty
          (SourceNativeInquiryCompilationAt
            (CanonicalSurvivorRootAt oldVisit sourceIndex)
            (contributionCapacitySettlementSurvivorVisitAt oldVisit
              sourceIndex currentIndex)
            (contributionCapacityReopeningU7 oldVisit)
            (contributionCapacityReopeningCalculus oldVisit)
            (contributionCapacityReopeningTheory oldVisit) ()
            (contributionCapacitySettlementSurvivorEntryInquiryEventAt
              oldVisit sourceIndex currentIndex)
            (contributionCapacitySettlementSurvivorEntryAt oldVisit
              entryIndex)
            (contributionCapacitySettlementSurvivorEntryAuthorityAt oldVisit
              sourceIndex currentIndex entryIndex)) ∧
        Nonempty
          (Sigma fun sourceEntry :
              (contributionCapacitySettlementFullLedger oldVisit).Entry =>
            RootDebtLineageAt (ReopeningNAt oldVisit) sourceEntry
              (contributionCapacitySettlementSurvivorEntryAt oldVisit
                entryIndex)) ∧
        Nonempty
          (PeriodicActualServiceExitAt
            (contributionCapacitySettlementSurvivorInitialCurrentAt
                sourceIndex + currentIndex))

abbrev ProofCarryingContributionCapacitySettlementSurvivorAccountabilityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop :=
  Function.Injective
      ContributionCapacitySettlementSurvivorProjection.consumer ∧
    ∀ currentIndex : Nat,
      ContributionCapacitySettlementSurvivorAccountabilityAtCurrent oldVisit
        sourceIndex currentIndex

/-- Complete-live-fibre consumer: both inherited rows, at every later current,
have causal authority, an entry-indexed independent consumer, source debt
provenance, and a fresh actionable-exit occurrence. -/
theorem generatedSettlementSurvivorWholeLedgerAccountability
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacitySettlementSurvivorAccountabilityAt
      oldVisit sourceIndex := by
  refine
    ⟨contributionCapacitySettlementSurvivorConsumerProjections_injective,
      ?_⟩
  intro currentIndex entryIndex
  exact
    ⟨⟨contributionCapacitySettlementSurvivorEntryAuthorityAt oldVisit
        sourceIndex currentIndex entryIndex⟩,
      ⟨contributionCapacitySettlementSurvivorEntryAnswerConsumerAt oldVisit
        sourceIndex currentIndex entryIndex⟩,
      ⟨contributionCapacitySettlementSurvivorEntryCompilationAt oldVisit
        sourceIndex currentIndex entryIndex⟩,
      ⟨contributionCapacitySettlementSurvivorDebtOrigin oldVisit
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)⟩,
      contributionCapacitySettlementSurvivorRootGeneratedRenewalAt oldVisit
        sourceIndex
        (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
          sourceIndex)
        (contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
          currentIndex)⟩

end
end M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability.contributionCapacitySettlementSurvivorEntryAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability.contributionCapacitySettlementSurvivorEntryAnswerConsumerAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability.contributionCapacitySettlementSurvivorEntryCompilationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability.contributionCapacitySettlementSurvivorConsumers_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability.contributionCapacitySettlementSurvivorAnswers_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability.contributionCapacitySettlementSurvivorInquiryAnswerConsumer_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability.generatedSettlementSurvivorWholeLedgerAccountability
