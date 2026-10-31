import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Consumer.SourceGeneratedContributionCapacitySettlementConsumer

/-!
# No free-eternal survivor debt

The two inherited survivor rows are fully accountable, but their current root
only carries them with zero budget and has no faithful-terminal fibre.  This
module proves that such a tail cannot already be a total Noetherian debt
closure law.  It reuses the exact `settlementDebtProcessAt`; no second process,
ledger, terminal, or future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementSurvivorNoFreeEternity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability
open M14SourceGeneratedContributionCapacitySettlementConsumer

abbrev contributionCapacitySettlementSurvivorDebtOriginAt
    (oldVisit : OldVisit)
    (targetEntry :
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :=
  (contributionCapacitySettlementSurvivorDebtOrigin oldVisit targetEntry).1

def contributionCapacitySettlementSurvivorDebtCurrentAt
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat)
    (targetEntry :
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    SourceNativeRootDebtCurrentAt
      (settlementDebtProcessAt oldVisit sourceIndex)
      (contributionCapacitySettlementSurvivorDebtOriginAt oldVisit
        targetEntry) where
  state := some currentIndex
  entry := targetEntry
  sameDebt :=
    (contributionCapacitySettlementSurvivorDebtOrigin oldVisit targetEntry).2

@[simp] theorem contributionCapacitySettlementSurvivorDebtCurrent_budget_zero
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat)
    (targetEntry :
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    (contributionCapacitySettlementSurvivorDebtCurrentAt oldVisit sourceIndex
      currentIndex targetEntry).budget = 0 :=
  contributionCapacitySettlementSurvivorEntry_budget_zero oldVisit
    targetEntry

theorem contributionCapacitySettlementSurvivorDebtCurrent_noLocalTerminal
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat)
    (targetEntry :
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    IsEmpty
      (SourceNativeRootDebtLocalTerminalAt
        (contributionCapacitySettlementSurvivorDebtCurrentAt oldVisit
          sourceIndex currentIndex targetEntry)) := by
  constructor
  intro terminal
  exact nomatch terminal.terminal

/-- Strong no-free-eternity mouth.  Every survivor debt, observed at any
later current of the same fixed process, refutes a purported total Noetherian
closure law. -/
theorem everySettlementSurvivorRejectsFreeEternalClosure
    (oldVisit : OldVisit) (sourceIndex currentIndex : Nat)
    (targetEntry :
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    IsEmpty
      (SourceNativeNoetherianDebtClosureLaw
        (settlementDebtProcessAt oldVisit sourceIndex)
        (contributionCapacitySettlementSurvivorDebtOriginAt oldVisit
          targetEntry)) :=
  no_noetherianDebtClosureLaw_of_budget_eq_zero_of_noLocalTerminal
    (contributionCapacitySettlementSurvivorDebtCurrentAt oldVisit sourceIndex
      currentIndex targetEntry)
    (contributionCapacitySettlementSurvivorDebtCurrent_budget_zero oldVisit
      sourceIndex currentIndex targetEntry)
    (contributionCapacitySettlementSurvivorDebtCurrent_noLocalTerminal
      oldVisit sourceIndex currentIndex targetEntry)

abbrev ProofCarryingContributionCapacitySettlementSurvivorNoFreeEternityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop :=
  ProofCarryingContributionCapacitySettlementSurvivorAccountabilityAt oldVisit
      sourceIndex ∧
    ∀ targetEntry :
        (contributionCapacitySettlementSurvivorLedger oldVisit).Entry,
      IsEmpty
        (SourceNativeNoetherianDebtClosureLaw
          (settlementDebtProcessAt oldVisit sourceIndex)
          (contributionCapacitySettlementSurvivorDebtOriginAt oldVisit
            targetEntry))

theorem generatedSettlementSurvivorNoFreeEternity
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacitySettlementSurvivorNoFreeEternityAt
      oldVisit sourceIndex :=
  ⟨generatedSettlementSurvivorWholeLedgerAccountability oldVisit sourceIndex,
    everySettlementSurvivorRejectsFreeEternalClosure oldVisit sourceIndex 0⟩

end
end M14SourceGeneratedContributionCapacitySettlementSurvivorNoFreeEternity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorNoFreeEternity.contributionCapacitySettlementSurvivorDebtCurrent_noLocalTerminal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorNoFreeEternity.everySettlementSurvivorRejectsFreeEternalClosure
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorNoFreeEternity.generatedSettlementSurvivorNoFreeEternity
