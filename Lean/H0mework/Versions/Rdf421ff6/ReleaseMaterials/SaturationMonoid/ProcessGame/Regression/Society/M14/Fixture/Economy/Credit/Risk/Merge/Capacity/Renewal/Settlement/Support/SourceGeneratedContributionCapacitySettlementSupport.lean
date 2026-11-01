import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.World.SourceGeneratedContributionCapacityReopeningWorld

/-!
# Existing two-row support for contribution-capacity settlement

The capacity-U8 coface already contains both inventories needed by the
settlement boundary.  Its generated coface support carries the two inherited
rows plus the generated residual; the old target face carries exactly the two
inherited rows.  This file only names those existing supports inside the
reopening network.  It creates no filtered ledger, lifecycle state, actor, or
receipt registry.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementSupport

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityReopeningWorld

/-- Existing three-row coface support after reopening. -/
def contributionCapacitySettlementFullSupport
    (oldVisit : OldVisit) : (ReopeningNAt oldVisit).Support :=
  contributionCapacityReopeningTargetSupport oldVisit

/-- Existing two-row old face of the capacity-U8 coface. -/
def contributionCapacitySettlementSurvivorSupport
    (oldVisit : OldVisit) : (ReopeningNAt oldVisit).Support :=
  (.inl (contributionCapacityCutTargetSupport
    (capacityActionRootedAt oldVisit)), true)

def contributionCapacitySettlementFullLedger
    (oldVisit : OldVisit) : CompleteLiveLedgerAt (ReopeningNAt oldVisit) :=
  ⟨contributionCapacitySettlementFullSupport oldVisit⟩

def contributionCapacitySettlementSurvivorLedger
    (oldVisit : OldVisit) : CompleteLiveLedgerAt (ReopeningNAt oldVisit) :=
  ⟨contributionCapacitySettlementSurvivorSupport oldVisit⟩

/-- The existing contribution row on the old face. -/
def contributionCapacitySettlementSurvivorContribution
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementSurvivorLedger oldVisit).Entry :=
  let oldEntry := contributionCapacityCutTargetContribution
    (capacityActionRootedAt oldVisit)
  ⟨.inl oldEntry.1, oldEntry.2⟩

/-- The existing obstruction-continuity row on the old face. -/
def contributionCapacitySettlementSurvivorObstruction
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementSurvivorLedger oldVisit).Entry :=
  let oldEntry := contributionCapacityCutTargetObstruction
    (capacityActionRootedAt oldVisit)
  ⟨.inl oldEntry.1, oldEntry.2⟩

def contributionCapacitySettlementSurvivorEntryAt
    (oldVisit : OldVisit) :
    Fin 2 → (contributionCapacitySettlementSurvivorLedger oldVisit).Entry :=
  Fin.cases (contributionCapacitySettlementSurvivorContribution oldVisit)
    (fun _ => contributionCapacitySettlementSurvivorObstruction oldVisit)

def contributionCapacitySettlementSurvivorEntryIndex
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementSurvivorLedger oldVisit).Entry → Fin 2
  | ⟨.inl responsibility, .inl _contribution⟩ => ⟨0, by decide⟩
  | ⟨.inl responsibility, .inr _obstruction⟩ => ⟨1, by decide⟩
  | ⟨.inr direction, impossible⟩ => PEmpty.elim impossible

theorem contributionCapacitySettlementSurvivorEntryAt_index
    (oldVisit : OldVisit)
    (entry : (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    contributionCapacitySettlementSurvivorEntryAt oldVisit
        (contributionCapacitySettlementSurvivorEntryIndex oldVisit entry) =
      entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      rcases isOpen with contribution | obstruction
      · rcases contribution.down with ⟨support_eq, responsibility_eq⟩
        cases support_eq
        cases responsibility_eq
        rfl
      · rcases obstruction.down with ⟨support_eq, responsibility_eq⟩
        cases support_eq
        cases responsibility_eq
        rfl
  | inr direction => exact PEmpty.elim isOpen

@[simp] theorem contributionCapacitySettlementSurvivorEntryIndex_at
    (oldVisit : OldVisit) (index : Fin 2) :
    contributionCapacitySettlementSurvivorEntryIndex oldVisit
        (contributionCapacitySettlementSurvivorEntryAt oldVisit index) =
      index := by
  refine Fin.cases ?_ (fun tail => ?_) index
  · rfl
  · change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    rfl

/-- Exact finite inventory presentation of the existing old face. -/
def contributionCapacitySettlementSurvivorEntryEquiv
    (oldVisit : OldVisit) :
    Fin 2 ≃ (contributionCapacitySettlementSurvivorLedger oldVisit).Entry where
  toFun := contributionCapacitySettlementSurvivorEntryAt oldVisit
  invFun := contributionCapacitySettlementSurvivorEntryIndex oldVisit
  left_inv := contributionCapacitySettlementSurvivorEntryIndex_at oldVisit
  right_inv := contributionCapacitySettlementSurvivorEntryAt_index oldVisit

theorem contributionCapacitySettlementSurvivorEntry_cases
    (oldVisit : OldVisit)
    (entry : (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    entry = contributionCapacitySettlementSurvivorContribution oldVisit ∨
      entry = contributionCapacitySettlementSurvivorObstruction oldVisit := by
  have indexed :=
    contributionCapacitySettlementSurvivorEntryAt_index oldVisit entry
  generalize index_eq :
    contributionCapacitySettlementSurvivorEntryIndex oldVisit entry = index at indexed
  revert indexed
  refine Fin.cases ?_ (fun tail => ?_) index
  · intro equality
    exact .inl equality.symm
  · change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    intro equality
    exact .inr equality.symm

theorem contributionCapacitySettlementSurvivorEntries_distinct
    (oldVisit : OldVisit) :
    contributionCapacitySettlementSurvivorContribution oldVisit ≠
      contributionCapacitySettlementSurvivorObstruction oldVisit := by
  intro equality
  have responsibility_eq := congrArg Sigma.fst equality
  exact nomatch responsibility_eq

@[simp] theorem contributionCapacitySettlementSurvivorContribution_budget_zero
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementSurvivorContribution oldVisit).progressBudget =
      0 :=
  rfl

@[simp] theorem contributionCapacitySettlementSurvivorObstruction_budget_zero
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementSurvivorObstruction oldVisit).progressBudget =
      0 :=
  rfl

theorem contributionCapacitySettlementSurvivorEntry_budget_zero
    (oldVisit : OldVisit)
    (entry : (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    entry.progressBudget = 0 := by
  rcases contributionCapacitySettlementSurvivorEntry_cases oldVisit entry with
      equality | equality <;> subst entry <;> rfl

/-- The generated residual responsibility cannot occur on the existing old
face.  This is the original coface no-new-responsibility theorem, not a new
filtered-inventory axiom. -/
theorem contributionCapacitySettlementResidual_not_open_on_survivor
    (oldVisit : OldVisit) :
    IsEmpty
      ((ReopeningNAt oldVisit).OpenAt
        (contributionCapacitySettlementSurvivorSupport oldVisit)
        (contributionCapacityReopeningResidualEntryAt oldVisit true).1) := by
  constructor
  intro impossible
  exact PEmpty.elim impossible

/-- Each target survivor is classified against the complete three-row source
ledger by an exact old-debt lineage. -/
def contributionCapacitySettlementSurvivorDebtOrigin
    (oldVisit : OldVisit)
    (targetEntry :
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    Sigma fun sourceEntry :
        (contributionCapacitySettlementFullLedger oldVisit).Entry =>
      RootDebtLineageAt (ReopeningNAt oldVisit) sourceEntry targetEntry := by
  rcases targetEntry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      exact ⟨⟨.inl oldResponsibility, isOpen⟩, ⟨rfl, rfl⟩⟩
  | inr direction => exact PEmpty.elim isOpen

/-- The addressable generated residual has no debt-lineage continuation in
the old-face target.  Its claim is the generated `.inr` coordinate, whereas
every survivor claim is inherited through `.inl`. -/
theorem contributionCapacitySettlementResidual_hasNoSameDebtAtSurvivor
    (oldVisit : OldVisit) :
    IsEmpty
      (Sigma fun targetEntry :
          (contributionCapacitySettlementSurvivorLedger oldVisit).Entry =>
        RootDebtLineageAt (ReopeningNAt oldVisit)
          (contributionCapacityReopeningResidualEntryAt oldVisit true)
          targetEntry) := by
  constructor
  rintro ⟨targetEntry, sameDebt⟩
  rcases contributionCapacitySettlementSurvivorEntry_cases oldVisit
      targetEntry with equality | equality <;> subst targetEntry
  all_goals exact nomatch sameDebt.claim_eq

/-- A terminal handoff cannot clone one old debt into the two-row target.
The two survivors carry distinct inherited claim coordinates. -/
theorem contributionCapacitySettlementSameDebtTarget_unique
    (oldVisit : OldVisit)
    (sourceEntry : (contributionCapacitySettlementFullLedger oldVisit).Entry)
    (left right :
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry)
    (leftDebt : RootDebtLineageAt (ReopeningNAt oldVisit) sourceEntry left)
    (rightDebt : RootDebtLineageAt (ReopeningNAt oldVisit) sourceEntry right) :
    left = right := by
  rcases contributionCapacitySettlementSurvivorEntry_cases oldVisit left with
      left_eq | left_eq <;>
    rcases contributionCapacitySettlementSurvivorEntry_cases oldVisit right with
      right_eq | right_eq <;> subst left <;> subst right
  · rfl
  · have impossible := leftDebt.claim_eq.symm.trans rightDebt.claim_eq
    exact nomatch impossible
  · have impossible := leftDebt.claim_eq.symm.trans rightDebt.claim_eq
    exact nomatch impossible
  · rfl

end
end M14SourceGeneratedContributionCapacitySettlementSupport
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSupport.contributionCapacitySettlementSurvivorEntryAt_index
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSupport.contributionCapacitySettlementSurvivorEntryEquiv
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSupport.contributionCapacitySettlementResidual_not_open_on_survivor
