import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.SourceGeneratedLossAllocationMaterial
import H0mework.Versions.Rdf421ff6.Checks.Runtime.U8Completion

/-!
# M14 source-generated loss-allocation world

For any exact rooted failure over the fixed old network `N`, this module
retains its generated minimal coface as an initial support and adds one exact
first-write target support.  Instantiating the construction at a later joint
root therefore generates a fresh indexed world; no coface is transported
between sibling old roots.

The translated old parent and both loss children share one world
responsibility and claim.  The children are distinct only through
proof-relevant `OpenAt` witnesses carrying the existing exchange legs `a` and
`b`; no loss-share or participant registry is introduced.  Each child's
structural continuation budget is `2 -> 1`; this does not assert aggregate or
monetary conservation.  The canonical obstruction row separately continues
`0 -> 0`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedLossAllocationWorld

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open Lifecycle Universal Relations Exchange Money Clearing
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M14ClearingConsumerDeath
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopCreditStanding
open M14SourceGeneratedLossAllocationMaterial
open RootInquiryU8CompletionRegression

abbrev OldN := RootInquiryU8CompletionRegression.N

/-! ## Zero-choice economic provenance material -/

def lossAllocationChildActor (leg : Leg) : core.TargetActor :=
  exactExchangeSeed.actor exchangeCompiler leg

def lossAllocationChildBearer (leg : Leg) : Lifecycle.ActorBearer :=
  sourceGeneratedLossAllocationMaterial.childBearerAt leg

@[simp] theorem lossAllocationChildA_actor_is_creditor :
    lossAllocationChildActor .a = creditorActor :=
  rfl

@[simp] theorem lossAllocationChildB_actor_is_borrower :
    lossAllocationChildActor .b = borrowerActor :=
  rfl

theorem lossAllocationChildBearers_distinct :
    lossAllocationChildBearer .a ≠ lossAllocationChildBearer .b :=
  sourceGeneratedLossAllocationMaterial.childBearersDistinct

variable
    {OldV : ConstructiveRoot.Vocabulary}
    {oldWorld : SourceNativeAuthoritativeRootClosure OldN OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus OldN}
    {oldTheory : TheoryState OldN}
    {support : OldN.Support}
    {obstruction : OldN.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "RootedFailure" => RootedActualExpressibilityFailureAt
  oldWorld oldVisit U7 failure

def lossAllocationCoface (rooted : RootedFailure) :
    GeneratedMinimalCofaceAt rooted :=
  root_obstruction_generates_minimal_coface rooted

/-! ## Existing carriers only -/

abbrev LossAllocationSupport (rooted : RootedFailure) :=
  (lossAllocationCoface rooted).worldNetwork.Support × Bool

abbrev LossAllocationResponsibility (rooted : RootedFailure) :=
  (lossAllocationCoface rooted).worldNetwork.Responsibility

abbrev LossAllocationClaim (rooted : RootedFailure) :=
  (lossAllocationCoface rooted).worldNetwork.Claim

def lossAllocationInitialSupport (rooted : RootedFailure) :
    LossAllocationSupport rooted :=
  ((lossAllocationCoface rooted).cofaceSupport, false)

def lossAllocationTargetSupport (rooted : RootedFailure) :
    LossAllocationSupport rooted :=
  ((lossAllocationCoface rooted).cofaceSupport, true)

/-- Dependent restriction of existing `Leg`, not a new share carrier. -/
def ExistingLossChildLegAt (leg : Leg) : Prop :=
  leg = .a ∨ leg = .b

def lossAllocationOpenAt (rooted : RootedFailure) :
    LossAllocationSupport rooted ->
      LossAllocationResponsibility rooted -> Type
  | (.inl oldSupport, false), .inl oldResponsibility =>
      OldN.OpenAt oldSupport oldResponsibility
  | (.inr supportDirection, false), responsibility =>
      (lossAllocationCoface rooted).worldNetwork.OpenAt
        (.inr supportDirection) responsibility
  | (.inr _, true), .inl _ =>
      { leg : Leg // ExistingLossChildLegAt leg }
  | (.inr supportDirection, true), .inr responsibilityDirection =>
      GeneratedDirectionAlignedAt rooted supportDirection
        responsibilityDirection
  | (.inl oldSupport, true), responsibility =>
      (lossAllocationCoface rooted).worldNetwork.OpenAt
        (.inl oldSupport) responsibility
  | _, _ => PEmpty

def lossAllocationOpenClaimAt (rooted : RootedFailure) :
    {indexedSupport : LossAllocationSupport rooted} ->
    {responsibility : LossAllocationResponsibility rooted} ->
    lossAllocationOpenAt rooted indexedSupport responsibility ->
      LossAllocationClaim rooted
  | (.inl _oldSupport, false), .inl _oldResponsibility, isOpen =>
      .inl (OldN.openClaimAt isOpen)
  | (.inr _supportDirection, false), _responsibility, isOpen =>
      (lossAllocationCoface rooted).worldNetwork.openClaimAt isOpen
  | (.inr _, true), .inl _, _ => .inl ()
  | (.inr _, true), .inr responsibilityDirection, _ =>
      .inr responsibilityDirection
  | (.inl _oldSupport, true), _responsibility, isOpen =>
      (lossAllocationCoface rooted).worldNetwork.openClaimAt isOpen
  | (.inl _, false), .inr _, impossible => PEmpty.elim impossible

def lossAllocationOpenProgressBudgetAt (rooted : RootedFailure) :
    {indexedSupport : LossAllocationSupport rooted} ->
    {responsibility : LossAllocationResponsibility rooted} ->
    lossAllocationOpenAt rooted indexedSupport responsibility -> Nat
  | (.inl _oldSupport, false), .inl _oldResponsibility, isOpen =>
      OldN.openProgressBudgetAt isOpen
  | (.inr _supportDirection, false), _responsibility, isOpen =>
      (lossAllocationCoface rooted).worldNetwork.openProgressBudgetAt isOpen
  | (.inr _, true), .inl _, _ => 1
  | (.inr _, true), .inr _, _ => 0
  | (.inl _oldSupport, true), _responsibility, isOpen =>
      (lossAllocationCoface rooted).worldNetwork.openProgressBudgetAt isOpen
  | (.inl _, false), .inr _, impossible => PEmpty.elim impossible

/-- Richer whole-network representation.  The Boolean is the exact first-write
support phase, not a scheduler or completed future. -/
def lossAllocationWorld (rooted : RootedFailure) : WorldRelationNetwork where
  Support := LossAllocationSupport rooted
  Anchor := OldN.Anchor
  Incidence := (lossAllocationCoface rooted).worldNetwork.Incidence
  Lineage := OldN.Lineage
  Responsibility := LossAllocationResponsibility rooted
  Claim := LossAllocationClaim rooted
  anchorAt := fun indexedSupport => match indexedSupport.1 with
    | .inl oldSupport => OldN.anchorAt oldSupport
    | .inr _ => OldN.anchorAt
        (oldWorld.toRoot.supportAt rooted.oldSuccessor.next)
  incidenceAt := fun indexedSupport => match indexedSupport.1 with
    | .inl oldSupport => .inl (OldN.incidenceAt oldSupport)
    | .inr direction => .inr direction
  lineageAt := fun indexedSupport => match indexedSupport.1 with
    | .inl oldSupport => OldN.lineageAt oldSupport
    | .inr _ => OldN.lineageAt
        (oldWorld.toRoot.supportAt rooted.oldSuccessor.next)
  OpenAt := lossAllocationOpenAt rooted
  openClaimAt := lossAllocationOpenClaimAt rooted
  openProgressBudgetAt := lossAllocationOpenProgressBudgetAt rooted
  HoldsAt := fun indexedSupport claim =>
    (lossAllocationCoface rooted).worldNetwork.HoldsAt indexedSupport.1 claim
  ObstructionAt := fun indexedSupport =>
    (lossAllocationCoface rooted).worldNetwork.ObstructionAt indexedSupport.1
  obstructionClaim := fun obstruction =>
    (lossAllocationCoface rooted).worldNetwork.obstructionClaim obstruction
  SemanticChangeAt := fun indexedSupport sourceClaim targetClaim =>
    (lossAllocationCoface rooted).worldNetwork.SemanticChangeAt
      indexedSupport.1 sourceClaim targetClaim
  DispositionAt := fun indexedSupport kind =>
    (lossAllocationCoface rooted).worldNetwork.DispositionAt
      indexedSupport.1 kind

abbrev LossN (rooted : RootedFailure) := lossAllocationWorld rooted

/-! ## Old-world translation and exact initial coface ledger -/

def lossAllocationTranslation (rooted : RootedFailure) :
    TypedSemanticWorldNetworkTranslationAt OldN (LossN rooted) where
  support :=
    { forward := fun oldSupport => (.inl oldSupport, false)
      backward := fun indexedSupport => match indexedSupport.1 with
        | .inl oldSupport => oldSupport
        | .inr _ => oldWorld.toRoot.supportAt rooted.oldSuccessor.next
      backward_forward := fun _ => rfl }
  anchor :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  incidence :=
    { forward := Sum.inl
      backward := fun incidence => match incidence with
        | .inl oldIncidence => oldIncidence
        | .inr _ => OldN.incidenceAt
            (oldWorld.toRoot.supportAt rooted.oldSuccessor.next)
      backward_forward := fun _ => rfl }
  lineage :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  responsibility :=
    { forward := Sum.inl
      backward := fun responsibility => match responsibility with
        | .inl oldResponsibility => oldResponsibility
        | .inr _ => rooted.oldTargetEntry.1
      backward_forward := fun _ => rfl }
  claim :=
    { forward := Sum.inl
      backward := fun claim => match claim with
        | .inl oldClaim => oldClaim
        | .inr _ => OldN.obstructionClaim obstruction
      backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _oldSupport =>
    { forward := fun oldEntry => ⟨.inl oldEntry.1, oldEntry.2⟩
      backward := fun newEntry => match newEntry with
        | ⟨.inl oldResponsibility, isOpen⟩ =>
            ⟨oldResponsibility, isOpen⟩
        | ⟨.inr _, impossible⟩ => PEmpty.elim impossible
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ _ => ()
  oldDispositionSurvives := fun _ _ _ => ()

def lossAllocationOldTargetOpenLedger (rooted : RootedFailure) :
    ConstructiveRetract
      (OpenResponsibilityAt OldN
        (oldWorld.toRoot.supportAt rooted.oldSuccessor.next))
      (OpenResponsibilityAt (LossN rooted)
        (lossAllocationInitialSupport rooted)) where
  forward := fun oldEntry => ⟨.inl oldEntry.1, oldEntry.2⟩
  backward := fun newEntry => match newEntry with
    | ⟨.inl oldResponsibility, isOpen⟩ =>
        ⟨oldResponsibility, isOpen⟩
    | ⟨.inr _, _⟩ => rooted.oldTargetEntry
  backward_forward := fun _ => rfl

def lossAllocationInitialParent (rooted : RootedFailure) :
    OpenResponsibilityAt (LossN rooted)
      (lossAllocationInitialSupport rooted) :=
  (lossAllocationOldTargetOpenLedger rooted).forward rooted.oldTargetEntry

def lossAllocationInitialObstruction (rooted : RootedFailure) :
    OpenResponsibilityAt (LossN rooted)
      (lossAllocationInitialSupport rooted) :=
  ⟨.inr .completion, .same .completion⟩

def lossAllocationTargetChildA (rooted : RootedFailure) :
    OpenResponsibilityAt (LossN rooted)
      (lossAllocationTargetSupport rooted) :=
  ⟨(lossAllocationInitialParent rooted).1, ⟨.a, .inl rfl⟩⟩

def lossAllocationTargetChildB (rooted : RootedFailure) :
    OpenResponsibilityAt (LossN rooted)
      (lossAllocationTargetSupport rooted) :=
  ⟨(lossAllocationInitialParent rooted).1, ⟨.b, .inr rfl⟩⟩

def lossAllocationTargetObstruction (rooted : RootedFailure) :
    OpenResponsibilityAt (LossN rooted)
      (lossAllocationTargetSupport rooted) :=
  ⟨.inr .completion, .same .completion⟩

def lossAllocationInitialLedger (rooted : RootedFailure) :
    CompleteLiveLedgerAt (LossN rooted) :=
  ⟨lossAllocationInitialSupport rooted⟩

def lossAllocationTargetLedger (rooted : RootedFailure) :
    CompleteLiveLedgerAt (LossN rooted) :=
  ⟨lossAllocationTargetSupport rooted⟩

/-! ## Existing-leg and budget readouts -/

def lossTargetLeg? (rooted : RootedFailure) :
    (lossAllocationTargetLedger rooted).Entry -> Option Leg
  | ⟨.inl _, leg⟩ => some leg.1
  | ⟨.inr _, _⟩ => none

@[simp] theorem lossTargetLeg?_childA (rooted : RootedFailure) :
    lossTargetLeg? rooted (lossAllocationTargetChildA rooted) = some .a :=
  rfl

@[simp] theorem lossTargetLeg?_childB (rooted : RootedFailure) :
    lossTargetLeg? rooted (lossAllocationTargetChildB rooted) = some .b :=
  rfl

theorem lossAllocationChildren_distinct (rooted : RootedFailure) :
    lossAllocationTargetChildA rooted ≠
      lossAllocationTargetChildB rooted := by
  intro equality
  have legEquality := congrArg (lossTargetLeg? rooted) equality
  exact Leg.noConfusion (Option.some.inj legEquality)

@[simp] theorem lossAllocationInitialParent_budget
    (rooted : RootedFailure) :
    (lossAllocationInitialParent rooted).progressBudget = 2 :=
  rfl

@[simp] theorem lossAllocationInitialObstruction_budget
    (rooted : RootedFailure) :
    (lossAllocationInitialObstruction rooted).progressBudget = 0 :=
  rfl

@[simp] theorem lossAllocationTargetChildA_budget
    (rooted : RootedFailure) :
    (lossAllocationTargetChildA rooted).progressBudget = 1 :=
  rfl

@[simp] theorem lossAllocationTargetChildB_budget
    (rooted : RootedFailure) :
    (lossAllocationTargetChildB rooted).progressBudget = 1 :=
  rfl

@[simp] theorem lossAllocationTargetObstruction_budget
    (rooted : RootedFailure) :
    (lossAllocationTargetObstruction rooted).progressBudget = 0 :=
  rfl

theorem lossAllocation_parent_children_same_responsibility_and_claim
    (rooted : RootedFailure) :
    (lossAllocationInitialParent rooted).1 =
        (lossAllocationTargetChildA rooted).1 ∧
      (lossAllocationInitialParent rooted).1 =
        (lossAllocationTargetChildB rooted).1 ∧
      (lossAllocationInitialParent rooted).claim =
        (lossAllocationTargetChildA rooted).claim ∧
      (lossAllocationInitialParent rooted).claim =
        (lossAllocationTargetChildB rooted).claim :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem lossAllocation_support_geometry_exact (rooted : RootedFailure) :
    (LossN rooted).anchorAt (lossAllocationInitialSupport rooted) =
        (LossN rooted).anchorAt (lossAllocationTargetSupport rooted) ∧
      (LossN rooted).incidenceAt (lossAllocationInitialSupport rooted) =
        (LossN rooted).incidenceAt (lossAllocationTargetSupport rooted) ∧
      (LossN rooted).lineageAt (lossAllocationInitialSupport rooted) =
        (LossN rooted).lineageAt (lossAllocationTargetSupport rooted) :=
  ⟨rfl, rfl, rfl⟩

end
end M14SourceGeneratedLossAllocationWorld
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationWorld.lossAllocationTranslation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationWorld.lossAllocationChildren_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationWorld.lossAllocationChildBearers_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationWorld.lossAllocation_parent_children_same_responsibility_and_claim
