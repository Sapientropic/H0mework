import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Credit.Risk.Merge.Capacity.Renewal.ProofCarryingContributionCapacityReopeningRuntimeRegression

/-!
# Direct consumer of authoritative reopening residual carry

The depth-6 and depth-7 reopening answers consume the generated residual row
of the one authoritative root ledger.  Its compiler-selected disposition is
exactly `.evolved (.carried ...)`; source and target budgets stay zero while
the same occurrences generate fresh actual-service UBI exit capacity.  No
parallel lifecycle vocabulary, admission, process, state or ledger exists.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityReopeningResidualCarryRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningResidualCarry
open M14UBIPeriodicActualServiceCapacity
open M14ProofCarryingContributionCapacityReopeningRuntimeRegression

abbrev CanonicalReopeningSourceEvent :=
  CanonicalReopeningSourceEventAt canonicalOldVisit 1

abbrev FirstResidualCarry :=
  SourceGeneratedReopeningResidualCarryAt canonicalOldVisit 1
    CanonicalReopeningSourceEvent 0

abbrev SecondResidualCarry :=
  SourceGeneratedReopeningResidualCarryAt canonicalOldVisit 1
    CanonicalReopeningSourceEvent 1

def firstResidualCarry : FirstResidualCarry :=
  SourceGeneratedReopeningResidualCarryAt.generate canonicalOldVisit 1
    CanonicalReopeningSourceEvent 0

def secondResidualCarry : SecondResidualCarry :=
  SourceGeneratedReopeningResidualCarryAt.generate canonicalOldVisit 1
    CanonicalReopeningSourceEvent 1

theorem first_carry_source_is_exact_root_occurrence :
    firstResidualCarry.sourceOccurrence =
      (CanonicalReopeningRootAt canonicalOldVisit 1).emitted
        (contributionCapacityReopenedVisitAt canonicalOldVisit 1 0).current :=
  rfl

theorem second_carry_source_is_exact_root_occurrence :
    secondResidualCarry.sourceOccurrence =
      (CanonicalReopeningRootAt canonicalOldVisit 1).emitted
        (contributionCapacityReopenedVisitAt canonicalOldVisit 1 1).current :=
  rfl

theorem first_carry_source_entry_is_generated_residual :
    firstResidualCarry.sourceEntry =
      contributionCapacityReopeningTargetResidual canonicalOldVisit :=
  rfl

theorem second_carry_source_entry_is_generated_residual :
    secondResidualCarry.sourceEntry =
      contributionCapacityReopeningTargetResidual canonicalOldVisit :=
  rfl

theorem first_carry_target_entry_is_generated_residual :
    firstResidualCarry.targetEntry =
      contributionCapacityReopeningTargetResidual canonicalOldVisit :=
  rfl


theorem second_carry_target_entry_is_generated_residual :
    secondResidualCarry.targetEntry =
      contributionCapacityReopeningTargetResidual canonicalOldVisit :=
  rfl

def CanonicalTerminalBranchAt
    {index : Nat}
    (carry : SourceGeneratedReopeningResidualCarryAt canonicalOldVisit 1
      CanonicalReopeningSourceEvent index) : Type :=
  Sigma fun terminal : LedgerEntryTerminalAt (ReopeningNAt canonicalOldVisit)
      carry.sourceEntry =>
    PLift
      (((contributionCapacityReopeningLedgerCompiler canonicalOldVisit 1
          CanonicalReopeningSourceEvent).compile
        carry.sourceOccurrence).entryDisposition carry.sourceEntry =
        .terminal terminal)

theorem canonical_terminal_branch_isEmpty
    {index : Nat}
    (carry : SourceGeneratedReopeningResidualCarryAt canonicalOldVisit 1
      CanonicalReopeningSourceEvent index) :
    IsEmpty (CanonicalTerminalBranchAt carry) := by
  constructor
  rintro ⟨terminal, terminal_eq⟩
  let equality := terminal_eq.down
  rw [carry.compilerDisposition_exact] at equality
  cases equality

/-- A period-6 root-row token cannot be retyped as the next root current. -/
def one_carry_witness_cannot_wrap_next_current : PUnit := by
  fail_if_success
    exact
      (contributionCapacityReopenedAnswer_generates_residualCarryAt
          canonicalOldVisit 1 0 :
        Nonempty SecondResidualCarry)
  exact PUnit.unit

structure ProofCarryingContributionCapacityReopeningResidualCarryCertificate :
    Type 6 where
  firstRuntimeAnswer :
    seventhTick.resolution =
      .directlyAnswered
        (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 0)
        (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 0)
  secondRuntimeAnswer :
    eighthTick.resolution =
      .directlyAnswered
        (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 1)
        (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 1)
  firstSourceOccurrenceExact :
    firstResidualCarry.sourceOccurrence =
      (CanonicalReopeningRootAt canonicalOldVisit 1).emitted
        (contributionCapacityReopenedVisitAt canonicalOldVisit 1 0).current
  secondSourceOccurrenceExact :
    secondResidualCarry.sourceOccurrence =
      (CanonicalReopeningRootAt canonicalOldVisit 1).emitted
        (contributionCapacityReopenedVisitAt canonicalOldVisit 1 1).current
  firstCarryGenerated : Nonempty FirstResidualCarry
  secondCarryGenerated : Nonempty SecondResidualCarry
  everyCurrentCarryGenerated : ∀ index : Nat,
    Nonempty (SourceGeneratedReopeningResidualCarryAt canonicalOldVisit 1
      CanonicalReopeningSourceEvent index)
  firstCausalAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CanonicalReopeningRootAt canonicalOldVisit 1)
      (contributionCapacityReopenedVisitAt canonicalOldVisit 1 0)
      (contributionCapacityReopeningTargetResidual canonicalOldVisit)
  secondCausalAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CanonicalReopeningRootAt canonicalOldVisit 1)
      (contributionCapacityReopenedVisitAt canonicalOldVisit 1 1)
      (contributionCapacityReopeningTargetResidual canonicalOldVisit)
  firstSourceEntryExact : firstResidualCarry.sourceEntry =
    contributionCapacityReopeningTargetResidual canonicalOldVisit
  secondSourceEntryExact : secondResidualCarry.sourceEntry =
    contributionCapacityReopeningTargetResidual canonicalOldVisit
  firstTargetEntryExact : firstResidualCarry.targetEntry =
    contributionCapacityReopeningTargetResidual canonicalOldVisit
  secondTargetEntryExact : secondResidualCarry.targetEntry =
    contributionCapacityReopeningTargetResidual canonicalOldVisit
  firstCompilerDispositionExact :
    ((contributionCapacityReopeningLedgerCompiler canonicalOldVisit 1
        CanonicalReopeningSourceEvent).compile
      firstResidualCarry.sourceOccurrence).entryDisposition
        firstResidualCarry.sourceEntry =
      .evolved firstResidualCarry.evolution
  secondCompilerDispositionExact :
    ((contributionCapacityReopeningLedgerCompiler canonicalOldVisit 1
        CanonicalReopeningSourceEvent).compile
      secondResidualCarry.sourceOccurrence).entryDisposition
        secondResidualCarry.sourceEntry =
      .evolved secondResidualCarry.evolution
  firstFoldDestinationExact :
    (reopeningResidualCarryWholeEvolutionAt canonicalOldVisit 1
      CanonicalReopeningSourceEvent 0).destination
        firstResidualCarry.sourceEntry =
      ⟨firstResidualCarry.targetEntry, firstResidualCarry.evolution⟩
  secondFoldDestinationExact :
    (reopeningResidualCarryWholeEvolutionAt canonicalOldVisit 1
      CanonicalReopeningSourceEvent 1).destination
        secondResidualCarry.sourceEntry =
      ⟨secondResidualCarry.targetEntry, secondResidualCarry.evolution⟩
  firstCanonicalTerminalEmpty : IsEmpty
    (CanonicalTerminalBranchAt firstResidualCarry)
  secondCanonicalTerminalEmpty : IsEmpty
    (CanonicalTerminalBranchAt secondResidualCarry)
  firstActualRenewal : Nonempty (PeriodicActualServiceExitAt 6)
  secondActualRenewal : Nonempty (PeriodicActualServiceExitAt 7)
  firstSourceBudgetZero : firstResidualCarry.sourceEntry.progressBudget = 0
  firstTargetBudgetZero : firstResidualCarry.targetEntry.progressBudget = 0
  secondSourceBudgetZero : secondResidualCarry.sourceEntry.progressBudget = 0
  secondTargetBudgetZero : secondResidualCarry.targetEntry.progressBudget = 0
  firstLineagePreserved :
    (ReopeningNAt canonicalOldVisit).lineageAt
        firstResidualCarry.sourceOccurrence.1 =
      (ReopeningNAt canonicalOldVisit).lineageAt
        (contributionCapacityReopeningEmitted canonicalOldVisit 1
          CanonicalReopeningSourceEvent 2).1
  secondLineagePreserved :
    (ReopeningNAt canonicalOldVisit).lineageAt
        secondResidualCarry.sourceOccurrence.1 =
      (ReopeningNAt canonicalOldVisit).lineageAt
        (contributionCapacityReopeningEmitted canonicalOldVisit 1
          CanonicalReopeningSourceEvent 3).1
  firstClaimPreserved :
    firstResidualCarry.sourceEntry.claim = firstResidualCarry.targetEntry.claim
  secondClaimPreserved :
    secondResidualCarry.sourceEntry.claim = secondResidualCarry.targetEntry.claim
  existingBearer :
    contributionCapacityU8BearerAt canonicalOldVisit
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityU8GeneratedResidual canonicalOldVisit) =
      sourceGeneratedLossAllocationMaterial.parentBearer
  exitCapacityAndCarriedResidualCoexist :
    (geometryCompilerAt 6).actionableExitCapacity = 1 ∧
      firstResidualCarry.targetEntry.progressBudget = 0
  actualExitOccurrencesInjective :
    Function.Injective (fun index =>
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityReopeningDepthAtCurrent 1 index))

def proofCarryingContributionCapacityReopeningResidualCarryCertificate :
    ProofCarryingContributionCapacityReopeningResidualCarryCertificate where
  firstRuntimeAnswer := seventhTick_is_generated_reopening_target_answer
  secondRuntimeAnswer := eighthTick_is_next_generated_reopening_target_answer
  firstSourceOccurrenceExact := first_carry_source_is_exact_root_occurrence
  secondSourceOccurrenceExact := second_carry_source_is_exact_root_occurrence
  firstCarryGenerated :=
    contributionCapacityReopenedAnswer_generates_residualCarryAt
      canonicalOldVisit 1 0
  secondCarryGenerated :=
    contributionCapacityReopenedAnswer_generates_residualCarryAt
      canonicalOldVisit 1 1
  everyCurrentCarryGenerated := fun index =>
    contributionCapacityReopenedAnswer_generates_residualCarryAt
      canonicalOldVisit 1 index
  firstCausalAuthority :=
    contributionCapacityReopenedAuthorityAt canonicalOldVisit 1 0
  secondCausalAuthority :=
    contributionCapacityReopenedAuthorityAt canonicalOldVisit 1 1
  firstSourceEntryExact := first_carry_source_entry_is_generated_residual
  secondSourceEntryExact := second_carry_source_entry_is_generated_residual
  firstTargetEntryExact := first_carry_target_entry_is_generated_residual
  secondTargetEntryExact := second_carry_target_entry_is_generated_residual
  firstCompilerDispositionExact := firstResidualCarry.compilerDisposition_exact
  secondCompilerDispositionExact := secondResidualCarry.compilerDisposition_exact
  firstFoldDestinationExact := firstResidualCarry.foldDestination_exact
  secondFoldDestinationExact := secondResidualCarry.foldDestination_exact
  firstCanonicalTerminalEmpty :=
    canonical_terminal_branch_isEmpty firstResidualCarry
  secondCanonicalTerminalEmpty :=
    canonical_terminal_branch_isEmpty secondResidualCarry
  firstActualRenewal := firstResidualCarry.actualRenewal
  secondActualRenewal := secondResidualCarry.actualRenewal
  firstSourceBudgetZero := firstResidualCarry.sourceEntry_budget_zero
  firstTargetBudgetZero := firstResidualCarry.targetEntry_budget_zero
  secondSourceBudgetZero := secondResidualCarry.sourceEntry_budget_zero
  secondTargetBudgetZero := secondResidualCarry.targetEntry_budget_zero
  firstLineagePreserved := firstResidualCarry.lineage_preserved
  secondLineagePreserved := secondResidualCarry.lineage_preserved
  firstClaimPreserved := firstResidualCarry.claim_preserved
  secondClaimPreserved := secondResidualCarry.claim_preserved
  existingBearer :=
    contributionCapacityU8_generatedBearer_is_existingParent canonicalOldVisit
  exitCapacityAndCarriedResidualCoexist :=
    ⟨actionableExitCapacity_eq_one_at 6,
      firstResidualCarry.targetEntry_budget_zero⟩
  actualExitOccurrencesInjective :=
    reopening_root_actual_exit_occurrences_injective

end
end M14ProofCarryingContributionCapacityReopeningResidualCarryRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningResidualCarryRegression.proofCarryingContributionCapacityReopeningResidualCarryCertificate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningResidualCarryRegression.one_carry_witness_cannot_wrap_next_current
