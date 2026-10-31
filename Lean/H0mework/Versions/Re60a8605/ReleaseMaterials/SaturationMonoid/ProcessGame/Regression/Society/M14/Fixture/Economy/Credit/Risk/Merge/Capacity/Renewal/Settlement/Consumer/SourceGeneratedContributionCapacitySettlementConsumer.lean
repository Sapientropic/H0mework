import H0mework.Foundation.Responsibility.NoetherianClosure
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Handoff.Accountability.SourceGeneratedContributionCapacitySettlementSurvivorAccountability

/-!
# Direct consumer of contribution-capacity settlement

This module consumes the exact runtime boundary generated after capacity
reopening.  The three-row root faithfully terminates its complete ledger, its
source-fixed handoff enters the already existing two-row old face, and only
the generated residual debt disappears there.  The two inherited rows remain
source-accounted and continue to generate actual-service exit occurrences.

The debt process below is a fixed view of those same registered living
currents.  It creates no second occurrence, ledger, receipt registry, or
completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementConsumer

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySupportSeparation
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementRoot
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability
open M14UBIPeriodicActualServiceCapacity

abbrev canonicalSettlementOldVisit :=
  M14SourceGeneratedContributionCapacitySupportSeparation.canonicalOldVisit

abbrev CanonicalSettlementSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  CanonicalContributionCapacitySettlementSourceEventAt oldVisit sourceIndex

/-! ## The exact terminal-to-survivor living process -/

def settlementDebtStateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Option Nat → SourceNativeLivingRootCurrentAt (ReopeningNAt oldVisit)
  | none =>
      ⟨SettlementVAt oldVisit,
        CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex,
        contributionCapacitySettlementTerminalVisit oldVisit sourceIndex
          (CanonicalSettlementSourceEventAt oldVisit sourceIndex)⟩
  | some index =>
      ⟨ContributionCapacitySettlementSurvivorVAt oldVisit,
        CanonicalContributionCapacitySettlementSurvivorRootAt oldVisit
          sourceIndex,
        contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          index⟩

def settlementDebtFiniteDepth?
    {oldVisit : OldVisit}
    (current : SourceNativeLivingRootCurrentAt (ReopeningNAt oldVisit)) :
    Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

@[simp] theorem settlementSurvivorFiniteDepth_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    settlementDebtFiniteDepth?
        (settlementDebtStateAt oldVisit sourceIndex (some index)) =
      some index := by
  change
    some
        (ProductiveFiniteRootHistoryAt.causalDepth
          (contributionCapacitySettlementSurvivorRootVisitAt oldVisit
            sourceIndex index).history) =
      some index
  rw [contributionCapacitySettlementSurvivorRootVisit_depth]

theorem bool_ne_nat : Bool ≠ Nat := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  simp at card_eq

theorem settlementDebtStateAt_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective (settlementDebtStateAt oldVisit sourceIndex) := by
  intro left right equality
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right =>
          have vocabulary_eq :=
            congrArg SourceNativeLivingRootCurrentAt.V equality
          have current_eq := congrArg Vocabulary.Current vocabulary_eq
          exact False.elim (bool_ne_nat current_eq)
  | some left =>
      cases right with
      | none =>
          have vocabulary_eq :=
            congrArg SourceNativeLivingRootCurrentAt.V equality
          have current_eq := congrArg Vocabulary.Current vocabulary_eq
          exact False.elim (bool_ne_nat current_eq.symm)
      | some right =>
          have depth_eq := congrArg settlementDebtFiniteDepth? equality
          rw [settlementSurvivorFiniteDepth_exact,
            settlementSurvivorFiniteDepth_exact] at depth_eq
          cases Option.some.inj depth_eq
          rfl

def settlementDebtSuccessor : Option Nat → Option Nat
  | none => some 0
  | some index => some (index + 1)

def settlementDebtProcessAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeLivingRootProcess (ReopeningNAt oldVisit) where
  State := Option Nat
  stateAt := settlementDebtStateAt oldVisit sourceIndex
  stateAt_injective := settlementDebtStateAt_injective oldVisit sourceIndex
  initial := none
  successorAt := by
    intro state
    refine ⟨settlementDebtSuccessor state, ?_⟩
    cases state with
    | none => exact ⟨rfl, trivial⟩
    | some index => exact ⟨rfl, HEq.rfl⟩

/-! ## The generated residual really settles -/

abbrev settlementResidualOriginAt (oldVisit : OldVisit) :=
  contributionCapacityReopeningResidualEntryAt oldVisit true

def settlementResidualCurrentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRootDebtCurrentAt
      (settlementDebtProcessAt oldVisit sourceIndex)
      (settlementResidualOriginAt oldVisit) where
  state := none
  entry := settlementResidualOriginAt oldVisit
  sameDebt := ⟨rfl, rfl⟩

def generatedResidualSettlementAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRootDebtSettlementAt
      (settlementResidualCurrentAt oldVisit sourceIndex) where
  localTerminal :=
    contributionCapacitySettlementExactTerminal oldVisit sourceIndex
      (CanonicalSettlementSourceEventAt oldVisit sourceIndex)
  noSameDebtAtTarget :=
    contributionCapacitySettlementResidual_hasNoSameDebtAtSurvivor oldVisit

def generatedResidualTerminalReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    LedgerEntryTerminalAt (ReopeningNAt oldVisit)
      (settlementResidualCurrentAt oldVisit sourceIndex).entry :=
  (generatedResidualSettlementAt oldVisit sourceIndex).receipt

/-! ## The survivor face is inherited, live, and periodically actionable -/

theorem everySettlementSurvivor_has_sourceDebt
    (oldVisit : OldVisit)
    (targetEntry :
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) :
    Nonempty
      (Sigma fun sourceEntry :
          (contributionCapacitySettlementFullLedger oldVisit).Entry =>
        RootDebtLineageAt (ReopeningNAt oldVisit) sourceEntry targetEntry) :=
  ⟨contributionCapacitySettlementSurvivorDebtOrigin oldVisit targetEntry⟩

def settlementSurvivorInventoryEquivAt
    (oldVisit : OldVisit) :
    Fin 2 ≃ (contributionCapacitySettlementSurvivorLedger oldVisit).Entry :=
  contributionCapacitySettlementSurvivorEntryEquiv oldVisit

theorem settlementSurvivor_generates_actualExit
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty
      (PeriodicActualServiceExitAt
        (contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
          index)) := by
  exact contributionCapacitySettlementSurvivorRootGeneratedRenewalAt
    oldVisit sourceIndex (CanonicalSettlementSourceEventAt oldVisit sourceIndex)
    (contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex + index)

theorem distinctSettlementSurvivorVisits_have_distinctCurrent
    (oldVisit : OldVisit) (sourceIndex left right : Nat)
    (current_eq :
      (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          left).current =
        (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          right).current) :
    left = right := by
  have left_exact :
      (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          left).current =
        contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
          left :=
    contributionCapacitySettlementSurvivorVisit_current_exact oldVisit
      sourceIndex left
  have right_exact :
      (contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
          right).current =
        contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
          right :=
    contributionCapacitySettlementSurvivorVisit_current_exact oldVisit
      sourceIndex right
  have sum_eq :
      contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
          left =
        contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
          right :=
    left_exact.symm.trans (current_eq.trans right_exact)
  exact Nat.add_left_cancel sum_eq

/-! ## Named-runtime factorization and negative controls -/

@[simp] theorem canonicalRuntime_depthEight_is_settlementAction :
    (jointRuntime.stateAt 8).engine.node =
      .active (contributionCapacitySettlementActionPresentationAt
        canonicalSettlementOldVisit 1) :=
  ninthState_node_is_contributionCapacitySettlementAction

@[simp] theorem canonicalRuntime_depthNine_is_exactTerminal :
    (jointRuntime.stateAt 9).engine.node =
      .active (contributionCapacitySettlementTerminalPresentationAt
        canonicalSettlementOldVisit 1) :=
  tenthState_node_is_contributionCapacitySettlementTerminal

@[simp] theorem canonicalRuntime_depthTen_is_firstSurvivor :
    (jointRuntime.stateAt 10).engine.node =
      .active (contributionCapacitySettlementSurvivorPresentationAt
        canonicalSettlementOldVisit 1 0) :=
  eleventhState_node_is_contributionCapacitySettlementSurvivor

theorem canonicalRuntime_depthTen_has_wholeLedgerAccountability :
    (jointRuntime.stateAt 10).engine.node =
        .active (contributionCapacitySettlementSurvivorPresentationAt
          canonicalSettlementOldVisit 1 0) ∧
      ContributionCapacitySettlementSurvivorAccountabilityAtCurrent
        canonicalSettlementOldVisit 1 0 :=
  ⟨canonicalRuntime_depthTen_is_firstSurvivor,
    (generatedSettlementSurvivorWholeLedgerAccountability
      canonicalSettlementOldVisit 1).2 0⟩

theorem canonicalRuntime_depthEleven_has_wholeLedgerAccountability :
    (jointRuntime.stateAt 11).engine.node =
        .active (contributionCapacitySettlementSurvivorPresentationAt
          canonicalSettlementOldVisit 1 1) ∧
      ContributionCapacitySettlementSurvivorAccountabilityAtCurrent
        canonicalSettlementOldVisit 1 1 :=
  ⟨twelfthState_node_is_next_contributionCapacitySettlementSurvivor,
    (generatedSettlementSurvivorWholeLedgerAccountability
      canonicalSettlementOldVisit 1).2 1⟩

/-- A survivor root has no local faithful-terminal label at any current. -/
theorem survivorCannotMintLocalTerminal
    (oldVisit : OldVisit) (current : Nat) :
    IsEmpty
      ((ContributionCapacitySettlementSurvivorVAt oldVisit
        ).FaithfulTerminalAt current) := by
  change IsEmpty PEmpty
  infer_instance

/-- The generated residual is absent from the exact target open fibre. -/
theorem settledResidualCannotReappearAtHandoff
    (oldVisit : OldVisit) :
    IsEmpty
      ((ReopeningNAt oldVisit).OpenAt
        (contributionCapacitySettlementSurvivorSupport oldVisit)
        (settlementResidualOriginAt oldVisit).1) :=
  contributionCapacitySettlementResidual_not_open_on_survivor oldVisit

abbrev ProofCarryingContributionCapacitySettlementCertificateAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop :=
    Nonempty
        (SourceNativeRootDebtSettlementAt
          (settlementResidualCurrentAt oldVisit sourceIndex)) ∧
      (settlementDebtProcessAt oldVisit sourceIndex).successor none = some 0 ∧
      Nonempty
        (Fin 2 ≃
          (contributionCapacitySettlementSurvivorLedger oldVisit).Entry) ∧
      (∀ targetEntry :
          (contributionCapacitySettlementSurvivorLedger oldVisit).Entry,
        Nonempty
          (Sigma fun sourceEntry :
              (contributionCapacitySettlementFullLedger oldVisit).Entry =>
            RootDebtLineageAt (ReopeningNAt oldVisit) sourceEntry
              targetEntry)) ∧
      IsEmpty
        ((ReopeningNAt oldVisit).OpenAt
          (contributionCapacitySettlementSurvivorSupport oldVisit)
          (settlementResidualOriginAt oldVisit).1) ∧
      ∀ index : Nat,
        Nonempty
          (PeriodicActualServiceExitAt
            (contributionCapacitySettlementSurvivorInitialCurrentAt
                sourceIndex + index))

/-- Strong direct-consumer mouth: the exact terminal closes the generated
residual, hands off exactly the two inherited rows with source debt, and every
later survivor current generates actionable exit authority. -/
theorem generatedSettlement_closesResidual_preservesSurvivors_renewsExit
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacitySettlementCertificateAt oldVisit
      sourceIndex := by
  exact
    ⟨⟨generatedResidualSettlementAt oldVisit sourceIndex⟩,
      rfl,
      ⟨settlementSurvivorInventoryEquivAt oldVisit⟩,
      everySettlementSurvivor_has_sourceDebt oldVisit,
      settledResidualCannotReappearAtHandoff oldVisit,
      settlementSurvivor_generates_actualExit oldVisit sourceIndex⟩

end
end M14SourceGeneratedContributionCapacitySettlementConsumer
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.settlementDebtProcessAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.generatedResidualSettlementAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.generatedResidualTerminalReceiptAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.settlementSurvivor_generates_actualExit
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.canonicalRuntime_depthNine_is_exactTerminal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.survivorCannotMintLocalTerminal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.settledResidualCannotReappearAtHandoff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.generatedSettlement_closesResidual_preservesSurvivors_renewsExit
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.canonicalRuntime_depthTen_has_wholeLedgerAccountability
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementConsumer.canonicalRuntime_depthEleven_has_wholeLedgerAccountability
