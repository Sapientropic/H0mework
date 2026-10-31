import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.NoGo.SourceGeneratedContributionCapacityNoFreeRestoration
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicActualServiceCapacity

/-!
# Source-generated capacity reopening world

The self-U8 revised ledger remains materially exhausted.  Reopening therefore
adds only a process phase to the existing capacity-U8 world; it preserves the
same responsibilities, claims, lineage, open fibres and zero budgets.  The
positive object is the independently generated periodic UBI actionable-exit
capacity carried by the action event, never a refilled ledger row.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityReopeningWorld

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityNoFreeRestoration
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity

abbrev ReopeningOldNAt (oldVisit : OldVisit) := CapacityU8NAt oldVisit

abbrev ContributionCapacityReopeningSupportAt (oldVisit : OldVisit) :=
  (ReopeningOldNAt oldVisit).Support × Bool

def contributionCapacityReopeningInitialSupport
    (oldVisit : OldVisit) : ContributionCapacityReopeningSupportAt oldVisit :=
  ((CapacityCofaceAt oldVisit).cofaceSupport, false)

def contributionCapacityReopeningTargetSupport
    (oldVisit : OldVisit) : ContributionCapacityReopeningSupportAt oldVisit :=
  ((CapacityCofaceAt oldVisit).cofaceSupport, true)

/-- Runtime source index `1` occurs at global tick `5`; the same formula
extends the bridge without storing a schedule. -/
def contributionCapacityReopeningDepthAt (sourceIndex : Nat) : Nat :=
  sourceIndex + 4

@[simp] theorem contributionCapacityReopeningDepthAt_one :
    contributionCapacityReopeningDepthAt 1 = 5 :=
  rfl

def contributionCapacityReopeningDepthAtCurrent
    (sourceIndex current : Nat) : Nat :=
  contributionCapacityReopeningDepthAt sourceIndex + current

@[simp] theorem contributionCapacityReopeningDepthAtCurrent_one_zero :
    contributionCapacityReopeningDepthAtCurrent 1 0 = 5 :=
  rfl

@[simp] theorem contributionCapacityReopeningDepthAtCurrent_one_one :
    contributionCapacityReopeningDepthAtCurrent 1 1 = 6 :=
  rfl

def contributionCapacityReopeningPeriodicExitAt
    (sourceIndex current : Nat) :
    PeriodicActualServiceExitAt
      (contributionCapacityReopeningDepthAtCurrent sourceIndex current) :=
  periodicActualServiceExitAt
    (contributionCapacityReopeningDepthAtCurrent sourceIndex current)

/-- Pure phase lift of the existing capacity-U8 world.  No identity,
responsibility, claim, incidence, bearer or budget carrier is added. -/
def contributionCapacityReopeningWorld
    (oldVisit : OldVisit) : WorldRelationNetwork where
  Support := ContributionCapacityReopeningSupportAt oldVisit
  Anchor := (ReopeningOldNAt oldVisit).Anchor
  Incidence := (ReopeningOldNAt oldVisit).Incidence
  Lineage := (ReopeningOldNAt oldVisit).Lineage
  Responsibility := (ReopeningOldNAt oldVisit).Responsibility
  Claim := (ReopeningOldNAt oldVisit).Claim
  anchorAt := fun support => (ReopeningOldNAt oldVisit).anchorAt support.1
  incidenceAt := fun support =>
    (ReopeningOldNAt oldVisit).incidenceAt support.1
  lineageAt := fun support =>
    (ReopeningOldNAt oldVisit).lineageAt support.1
  OpenAt := fun support responsibility =>
    (ReopeningOldNAt oldVisit).OpenAt support.1 responsibility
  openClaimAt := fun isOpen =>
    (ReopeningOldNAt oldVisit).openClaimAt isOpen
  openProgressBudgetAt := fun isOpen =>
    (ReopeningOldNAt oldVisit).openProgressBudgetAt isOpen
  HoldsAt := fun support claim =>
    (ReopeningOldNAt oldVisit).HoldsAt support.1 claim
  ObstructionAt := fun support =>
    (ReopeningOldNAt oldVisit).ObstructionAt support.1
  obstructionClaim := fun obstruction =>
    (ReopeningOldNAt oldVisit).obstructionClaim obstruction
  SemanticChangeAt := fun support sourceClaim targetClaim =>
    (ReopeningOldNAt oldVisit).SemanticChangeAt support.1 sourceClaim
      targetClaim
  DispositionAt := fun support kind =>
    (ReopeningOldNAt oldVisit).DispositionAt support.1 kind

abbrev ReopeningNAt (oldVisit : OldVisit) :=
  contributionCapacityReopeningWorld oldVisit

def contributionCapacityReopeningTranslation
    (oldVisit : OldVisit) :
    TypedSemanticWorldNetworkTranslationAt
      (ReopeningOldNAt oldVisit) (ReopeningNAt oldVisit) where
  support :=
    { forward := fun support => (support, false)
      backward := Prod.fst
      backward_forward := fun _ => rfl }
  anchor :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  incidence :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  lineage :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  responsibility :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  claim :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ =>
    { forward := fun entry => ⟨entry.1, entry.2⟩
      backward := fun entry => ⟨entry.1, entry.2⟩
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ proof => proof

def contributionCapacityReopeningLedgerAt
    (oldVisit : OldVisit) (phase : Bool) :
    CompleteLiveLedgerAt (ReopeningNAt oldVisit) :=
  ⟨((CapacityCofaceAt oldVisit).cofaceSupport, phase)⟩

abbrev contributionCapacityReopeningInitialLedger
    (oldVisit : OldVisit) :=
  contributionCapacityReopeningLedgerAt oldVisit false

abbrev contributionCapacityReopeningTargetLedger
    (oldVisit : OldVisit) :=
  contributionCapacityReopeningLedgerAt oldVisit true

/-- Exact generated-residual row viewed at either reopening phase. -/
def contributionCapacityReopeningResidualEntryAt
    (oldVisit : OldVisit) (phase : Bool) :
    (contributionCapacityReopeningLedgerAt oldVisit phase).Entry :=
  let residual := contributionCapacityU8GeneratedResidual oldVisit
  ⟨residual.1, residual.2⟩

def contributionCapacityReopeningEntryAt
    (oldVisit : OldVisit) (phase : Bool) :
    Fin 3 → (contributionCapacityReopeningLedgerAt oldVisit phase).Entry :=
  fun index =>
    let oldEntry := contributionCapacityU8EntryAt oldVisit index
    ⟨oldEntry.1, oldEntry.2⟩

def contributionCapacityReopeningEntryIndex
    (oldVisit : OldVisit) (phase : Bool) :
    (contributionCapacityReopeningLedgerAt oldVisit phase).Entry → Fin 3 :=
  fun entry => contributionCapacityU8EntryIndex oldVisit
    (⟨entry.1, entry.2⟩ : (contributionCapacityU8Ledger oldVisit).Entry)

theorem contributionCapacityReopeningEntryAt_index
    (oldVisit : OldVisit) (phase : Bool)
    (entry : (contributionCapacityReopeningLedgerAt oldVisit phase).Entry) :
    contributionCapacityReopeningEntryAt oldVisit phase
        (contributionCapacityReopeningEntryIndex oldVisit phase entry) =
      entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  exact contributionCapacityU8EntryAt_index oldVisit
    ⟨responsibility, isOpen⟩

theorem contributionCapacityReopeningEntry_cases
    (oldVisit : OldVisit) (phase : Bool)
    (entry : (contributionCapacityReopeningLedgerAt oldVisit phase).Entry) :
    entry = contributionCapacityReopeningEntryAt oldVisit phase 0 ∨
      entry = contributionCapacityReopeningEntryAt oldVisit phase 1 ∨
      entry = contributionCapacityReopeningEntryAt oldVisit phase 2 := by
  have indexed := contributionCapacityReopeningEntryAt_index oldVisit phase entry
  generalize index_eq :
    contributionCapacityReopeningEntryIndex oldVisit phase entry = index at indexed
  revert indexed
  refine Fin.cases ?_ (fun tail => ?_) index
  · intro equality
    exact .inl equality.symm
  · change Fin 2 at tail
    refine Fin.cases ?_ (fun last => ?_) tail
    · intro equality
      exact .inr (.inl equality.symm)
    · change Fin 1 at last
      have last_eq : last = (0 : Fin 1) := Subsingleton.elim _ _
      subst last
      intro equality
      exact .inr (.inr equality.symm)

/-- Changing only the process phase is a retract on the exact three-row
ledger.  This supplies injectivity without assuming open fibres are
subsingletons. -/
def contributionCapacityReopeningPhaseRetract
    (oldVisit : OldVisit) (sourcePhase targetPhase : Bool) :
    ConstructiveRetract
      (contributionCapacityReopeningLedgerAt oldVisit sourcePhase).Entry
      (contributionCapacityReopeningLedgerAt oldVisit targetPhase).Entry where
  forward := fun entry => ⟨entry.1, entry.2⟩
  backward := fun entry => ⟨entry.1, entry.2⟩
  backward_forward := fun _ => rfl

theorem contributionCapacityReopeningPhaseForward_injective
    (oldVisit : OldVisit) (sourcePhase targetPhase : Bool) :
    Function.Injective
      (contributionCapacityReopeningPhaseRetract oldVisit sourcePhase
        targetPhase).forward := by
  intro left right equality
  have backwardEquality := congrArg
    (contributionCapacityReopeningPhaseRetract oldVisit sourcePhase
      targetPhase).backward equality
  simpa only
    [(contributionCapacityReopeningPhaseRetract oldVisit sourcePhase
      targetPhase).backward_forward] using backwardEquality

def contributionCapacityReopeningTransferReceipt
    (oldVisit : OldVisit) :
    (ReopeningNAt oldVisit).DispositionAt
      (contributionCapacityReopeningInitialSupport oldVisit) .transfer :=
  GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget
    (contributionCapacityU8TransferDispositionAt oldVisit
      (contributionCapacityCutTargetSupport
        (capacityActionRootedAt oldVisit)))

def contributionCapacityReopeningTransferAt
    (oldVisit : OldVisit)
    (entry : (contributionCapacityU8Ledger oldVisit).Entry) :
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit)
      (⟨entry.1, entry.2⟩ :
        (contributionCapacityReopeningInitialLedger oldVisit).Entry)
      (⟨entry.1, entry.2⟩ :
        (contributionCapacityReopeningTargetLedger oldVisit).Entry) :=
  .transferred (contributionCapacityReopeningTransferReceipt oldVisit)
    rfl rfl (Nat.le_refl _)

@[simp] theorem contributionCapacityReopeningTargetEntry_budget_zero
    (oldVisit : OldVisit)
    (entry : (contributionCapacityReopeningTargetLedger oldVisit).Entry) :
    entry.progressBudget = 0 := by
  rcases entry with ⟨responsibility, isOpen⟩
  exact contributionCapacityU8Entry_budget_zero oldVisit
    ⟨responsibility, isOpen⟩

end
end M14SourceGeneratedContributionCapacityReopeningWorld
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningWorld.contributionCapacityReopeningTranslation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningWorld.contributionCapacityReopeningTargetEntry_budget_zero
