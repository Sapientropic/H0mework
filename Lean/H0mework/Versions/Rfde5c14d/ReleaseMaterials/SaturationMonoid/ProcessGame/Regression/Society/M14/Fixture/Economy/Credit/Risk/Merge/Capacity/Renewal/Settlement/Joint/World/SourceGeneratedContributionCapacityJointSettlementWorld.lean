import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Root.SourceGeneratedContributionCapacityReopeningRoot
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Support.SourceGeneratedContributionCapacitySettlementSupport

/-!
# Action-generated joint-settlement world

The target network is the minimal support extension forced by the absence of
an empty live-ledger face in `ReopeningNAt`.  Every old support is retained
definitionally through `Sum.inl`.  The sole new support `Sum.inr ()` has no open
responsibility or obstruction row; its geometry, facts, changes and disposition
readouts remain anchored at the already generated survivor support.

This file defines only the world, its translation, and complete ingress/empty
ledger presentations.  It installs no event, receipt, root, registry, U7/U8
choice, or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementWorld

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacitySettlementSupport

abbrev JointSettlementSupportAt (oldVisit : OldVisit) :=
  (ReopeningNAt oldVisit).Support ⊕ Unit

def contributionCapacityJointSettlementWorld
    (oldVisit : OldVisit) : WorldRelationNetwork where
  Support := JointSettlementSupportAt oldVisit
  Anchor := (ReopeningNAt oldVisit).Anchor
  Incidence := (ReopeningNAt oldVisit).Incidence
  Lineage := (ReopeningNAt oldVisit).Lineage
  Responsibility := (ReopeningNAt oldVisit).Responsibility
  Claim := (ReopeningNAt oldVisit).Claim
  anchorAt
    | .inl oldSupport => (ReopeningNAt oldVisit).anchorAt oldSupport
    | .inr () => (ReopeningNAt oldVisit).anchorAt
        (contributionCapacitySettlementSurvivorSupport oldVisit)
  incidenceAt
    | .inl oldSupport => (ReopeningNAt oldVisit).incidenceAt oldSupport
    | .inr () => (ReopeningNAt oldVisit).incidenceAt
        (contributionCapacitySettlementSurvivorSupport oldVisit)
  lineageAt
    | .inl oldSupport => (ReopeningNAt oldVisit).lineageAt oldSupport
    | .inr () => (ReopeningNAt oldVisit).lineageAt
        (contributionCapacitySettlementSurvivorSupport oldVisit)
  OpenAt
    | .inl oldSupport, responsibility =>
        (ReopeningNAt oldVisit).OpenAt oldSupport responsibility
    | .inr (), _responsibility => PEmpty
  openClaimAt := by
    intro support responsibility isOpen
    cases support with
    | inl oldSupport => exact (ReopeningNAt oldVisit).openClaimAt isOpen
    | inr emptyUnit => cases emptyUnit; exact nomatch isOpen
  openProgressBudgetAt := by
    intro support responsibility isOpen
    cases support with
    | inl oldSupport =>
        exact (ReopeningNAt oldVisit).openProgressBudgetAt isOpen
    | inr emptyUnit => cases emptyUnit; exact nomatch isOpen
  HoldsAt
    | .inl oldSupport, claim =>
        (ReopeningNAt oldVisit).HoldsAt oldSupport claim
    | .inr (), claim =>
        (ReopeningNAt oldVisit).HoldsAt
          (contributionCapacitySettlementSurvivorSupport oldVisit) claim
  ObstructionAt
    | .inl oldSupport => (ReopeningNAt oldVisit).ObstructionAt oldSupport
    | .inr () => PEmpty
  obstructionClaim := by
    intro support obstruction
    cases support with
    | inl oldSupport =>
        exact (ReopeningNAt oldVisit).obstructionClaim obstruction
    | inr emptyUnit =>
        cases emptyUnit
        exact PEmpty.elim obstruction
  SemanticChangeAt
    | .inl oldSupport, sourceClaim, targetClaim =>
        (ReopeningNAt oldVisit).SemanticChangeAt oldSupport sourceClaim
          targetClaim
    | .inr (), sourceClaim, targetClaim =>
        (ReopeningNAt oldVisit).SemanticChangeAt
          (contributionCapacitySettlementSurvivorSupport oldVisit) sourceClaim
          targetClaim
  DispositionAt
    | .inl oldSupport, kind =>
        (ReopeningNAt oldVisit).DispositionAt oldSupport kind
    | .inr (), kind =>
        (ReopeningNAt oldVisit).DispositionAt
          (contributionCapacitySettlementSurvivorSupport oldVisit) kind

abbrev JointSettlementNAt (oldVisit : OldVisit) :=
  contributionCapacityJointSettlementWorld oldVisit

def contributionCapacityJointSettlementTranslation
    (oldVisit : OldVisit) :
    TypedSemanticWorldNetworkTranslationAt
      (ReopeningNAt oldVisit) (JointSettlementNAt oldVisit) where
  support :=
    { forward := Sum.inl
      backward
        | .inl oldSupport => oldSupport
        | .inr () => contributionCapacitySettlementSurvivorSupport oldVisit
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
    { forward := fun oldEntry => ⟨oldEntry.1, oldEntry.2⟩
      backward := fun newEntry => ⟨newEntry.1, newEntry.2⟩
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ receipt => receipt

def contributionCapacityJointSettlementLiveSupport
    (oldVisit : OldVisit) : (JointSettlementNAt oldVisit).Support :=
  .inl (contributionCapacitySettlementSurvivorSupport oldVisit)

def contributionCapacityJointSettlementEmptySupport
    (oldVisit : OldVisit) : (JointSettlementNAt oldVisit).Support :=
  .inr ()

def contributionCapacityJointSettlementLiveLedger
    (oldVisit : OldVisit) : CompleteLiveLedgerAt (JointSettlementNAt oldVisit) :=
  ⟨contributionCapacityJointSettlementLiveSupport oldVisit⟩

def contributionCapacityJointSettlementEmptyLedger
    (oldVisit : OldVisit) : CompleteLiveLedgerAt (JointSettlementNAt oldVisit) :=
  ⟨contributionCapacityJointSettlementEmptySupport oldVisit⟩

def contributionCapacityJointSettlementIngressPresentation
    (oldVisit : OldVisit) :
    ConstructivePresentation
      (contributionCapacitySettlementSurvivorLedger oldVisit).Entry
      (contributionCapacityJointSettlementLiveLedger oldVisit).Entry where
  forward := fun oldEntry => ⟨oldEntry.1, oldEntry.2⟩
  backward := fun newEntry => ⟨newEntry.1, newEntry.2⟩
  backward_forward := fun _ => rfl
  forward_backward := fun _ => rfl

def contributionCapacityJointSettlementLiveEntryAt
    (oldVisit : OldVisit) :
    Fin 2 → (contributionCapacityJointSettlementLiveLedger oldVisit).Entry :=
  fun index => (contributionCapacityJointSettlementIngressPresentation oldVisit)
    |>.forward (contributionCapacitySettlementSurvivorEntryAt oldVisit index)

def contributionCapacityJointSettlementLiveEntryIndex
    (oldVisit : OldVisit) :
    (contributionCapacityJointSettlementLiveLedger oldVisit).Entry → Fin 2 :=
  fun entry => contributionCapacitySettlementSurvivorEntryIndex oldVisit
    ((contributionCapacityJointSettlementIngressPresentation oldVisit).backward
      entry)

@[simp] theorem contributionCapacityJointSettlementLiveEntryAt_index
    (oldVisit : OldVisit)
    (entry : (contributionCapacityJointSettlementLiveLedger oldVisit).Entry) :
    contributionCapacityJointSettlementLiveEntryAt oldVisit
        (contributionCapacityJointSettlementLiveEntryIndex oldVisit entry) =
      entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  exact contributionCapacitySettlementSurvivorEntryAt_index oldVisit
    ⟨responsibility, isOpen⟩

@[simp] theorem contributionCapacityJointSettlementLiveEntryIndex_at
    (oldVisit : OldVisit) (index : Fin 2) :
    contributionCapacityJointSettlementLiveEntryIndex oldVisit
        (contributionCapacityJointSettlementLiveEntryAt oldVisit index) =
      index :=
  contributionCapacitySettlementSurvivorEntryIndex_at oldVisit index

def contributionCapacityJointSettlementLiveEntryEquiv
    (oldVisit : OldVisit) :
    Fin 2 ≃ (contributionCapacityJointSettlementLiveLedger oldVisit).Entry where
  toFun := contributionCapacityJointSettlementLiveEntryAt oldVisit
  invFun := contributionCapacityJointSettlementLiveEntryIndex oldVisit
  left_inv := contributionCapacityJointSettlementLiveEntryIndex_at oldVisit
  right_inv := contributionCapacityJointSettlementLiveEntryAt_index oldVisit

theorem contributionCapacityJointSettlementIngress_noFresh
    (oldVisit : OldVisit)
    (targetEntry :
      (contributionCapacityJointSettlementLiveLedger oldVisit).Entry) :
    Nonempty
      (Sigma fun oldEntry :
          (contributionCapacitySettlementSurvivorLedger oldVisit).Entry =>
        PLift
          ((contributionCapacityJointSettlementIngressPresentation oldVisit).forward
            oldEntry = targetEntry)) :=
  ⟨⟨(contributionCapacityJointSettlementIngressPresentation oldVisit)
      |>.backward targetEntry,
    PLift.up ((contributionCapacityJointSettlementIngressPresentation oldVisit)
      |>.forward_backward targetEntry)⟩⟩

theorem contributionCapacityJointSettlementEmptyLedger_isEmpty
    (oldVisit : OldVisit) :
    IsEmpty (contributionCapacityJointSettlementEmptyLedger oldVisit).Entry :=
  ⟨fun entry => nomatch entry.2⟩

theorem contributionCapacityJointSettlementEmptySupport_hasNoOldPreimage
    (oldVisit : OldVisit) :
    IsEmpty
      (Sigma fun oldSupport : (ReopeningNAt oldVisit).Support =>
        PLift
          ((contributionCapacityJointSettlementTranslation oldVisit).support.forward
              oldSupport =
            contributionCapacityJointSettlementEmptySupport oldVisit)) :=
  ⟨fun preimage => by
    rcases preimage with ⟨oldSupport, equality⟩
    cases equality.down⟩

theorem contributionCapacityJointSettlementEmptySupport_unique
    (oldVisit : OldVisit)
    (support : (JointSettlementNAt oldVisit).Support)
    (empty : IsEmpty (OpenResponsibilityAt
      (JointSettlementNAt oldVisit) support)) :
    support = contributionCapacityJointSettlementEmptySupport oldVisit := by
  cases support with
  | inl oldSupport =>
      exact False.elim (empty.false
        ((contributionCapacityJointSettlementTranslation oldVisit).oldOpenLedger
          oldSupport |>.forward
            (contributionCapacityReopeningDefaultEntryAt oldVisit oldSupport)))
  | inr emptyUnit => cases emptyUnit; rfl

end
end M14SourceGeneratedContributionCapacityJointSettlementWorld
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementWorld.contributionCapacityJointSettlementTranslation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementWorld.contributionCapacityJointSettlementLiveEntryEquiv
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementWorld.contributionCapacityJointSettlementEmptySupport_unique
