import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Runtime.SourceGeneratedContributionMergeSupportSeparation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Action.SourceGeneratedContributionCapacityU8TargetState

/-!
# Capacity and self-U8 support separation

At the canonical M9 source visit, the original, revised, merge, capacity and
self-U8 networks have support cardinalities `2, 6, 12, 24, 25`.  Hence one
meta-process cannot hide two different root laws behind the same erased
current.  This file constructs no process, state or runtime.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySupportSeparation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeSupportSeparation
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityFailure
open M14SourceGeneratedContributionCapacityU8Lifecycle

abbrev CanonicalOldVisit :=
  RootVisit jointRoot.toAuthoritativeRoot.toRoot

def canonicalOldVisit : CanonicalOldVisit :=
  jointRoot.toAuthoritativeRoot.toRoot.initialVisit

abbrev CapacityN := CutN M9ProofCarryingRenewalU8Failure.rooted

abbrev CapacityU8N := CapacityU8NAt canonicalOldVisit

local instance originalDirectionUnique :
    Unique (GeneratedDirectionAt M9ProofCarryingRenewalU8Failure.rooted) where
  default := .completion
  uniq := GeneratedDirectionAt.eq_completion

local instance capacityDirectionUnique :
    Unique (GeneratedDirectionAt
      (capacityRootedFailureAt canonicalOldVisit)) where
  default := .completion
  uniq := GeneratedDirectionAt.eq_completion

local instance originalDirectionFinite :
    Finite (GeneratedDirectionAt M9ProofCarryingRenewalU8Failure.rooted) :=
  Finite.of_injective
    (fun _ : GeneratedDirectionAt M9ProofCarryingRenewalU8Failure.rooted =>
      PUnit.unit)
    (by
      intro left right _
      cases left
      cases right
      rfl)

local instance capacityDirectionFinite :
    Finite (GeneratedDirectionAt
      (capacityRootedFailureAt canonicalOldVisit)) :=
  Finite.of_injective
    (fun _ : GeneratedDirectionAt
      (capacityRootedFailureAt canonicalOldVisit) => PUnit.unit)
    (by
      intro left right _
      cases left
      cases right
      rfl)

local instance revisedSupportFinite : Finite RevisedN.Support := by
  change Finite
    ((Bool ⊕ GeneratedDirectionAt
      M9ProofCarryingRenewalU8Failure.rooted) × Bool)
  infer_instance

local instance mergeSupportFinite : Finite MergeN.Support := by
  change Finite (RevisedN.Support × Bool)
  infer_instance

local instance capacitySupportFinite : Finite CapacityN.Support := by
  change Finite (MergeN.Support × Bool)
  infer_instance

local instance capacityU8SupportFinite : Finite CapacityU8N.Support := by
  change Finite
    (CapacityN.Support ⊕ GeneratedDirectionAt
      (capacityRootedFailureAt canonicalOldVisit))
  infer_instance

theorem originalSupport_card : Nat.card OriginalN.Support = 2 := by
  change Nat.card Bool = 2
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_bool

theorem revisedSupport_card : Nat.card RevisedN.Support = 6 := by
  have direction_card :
      Nat.card (GeneratedDirectionAt
        M9ProofCarryingRenewalU8Failure.rooted) = 1 :=
    Nat.card_unique
  change Nat.card
    ((Bool ⊕ GeneratedDirectionAt
      M9ProofCarryingRenewalU8Failure.rooted) × Bool) = 6
  rw [Nat.card_prod, Nat.card_sum, direction_card]
  rw [Nat.card_eq_fintype_card]
  simp

theorem mergeSupport_card : Nat.card MergeN.Support = 12 := by
  change Nat.card (RevisedN.Support × Bool) = 12
  rw [Nat.card_prod, revisedSupport_card]
  rw [Nat.card_eq_fintype_card]
  simp

theorem capacitySupport_card : Nat.card CapacityN.Support = 24 := by
  change Nat.card (MergeN.Support × Bool) = 24
  rw [Nat.card_prod, mergeSupport_card]
  rw [Nat.card_eq_fintype_card]
  simp

theorem capacityU8Support_card : Nat.card CapacityU8N.Support = 25 := by
  have direction_card :
      Nat.card (GeneratedDirectionAt
        (capacityRootedFailureAt canonicalOldVisit)) = 1 :=
    Nat.card_unique
  change Nat.card
    (CapacityN.Support ⊕ GeneratedDirectionAt
      (capacityRootedFailureAt canonicalOldVisit)) = 25
  rw [Nat.card_sum, capacitySupport_card, direction_card]

theorem originalSupport_ne_capacitySupport :
    OriginalN.Support ≠ CapacityN.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [originalSupport_card, capacitySupport_card] at card_eq
  omega

theorem revisedSupport_ne_capacitySupport :
    RevisedN.Support ≠ CapacityN.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [revisedSupport_card, capacitySupport_card] at card_eq
  omega

theorem mergeSupport_ne_capacitySupport :
    MergeN.Support ≠ CapacityN.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [mergeSupport_card, capacitySupport_card] at card_eq
  omega

theorem originalSupport_ne_capacityU8Support :
    OriginalN.Support ≠ CapacityU8N.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [originalSupport_card, capacityU8Support_card] at card_eq
  omega

theorem revisedSupport_ne_capacityU8Support :
    RevisedN.Support ≠ CapacityU8N.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [revisedSupport_card, capacityU8Support_card] at card_eq
  omega

theorem mergeSupport_ne_capacityU8Support :
    MergeN.Support ≠ CapacityU8N.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [mergeSupport_card, capacityU8Support_card] at card_eq
  omega

theorem capacitySupport_ne_capacityU8Support :
    CapacityN.Support ≠ CapacityU8N.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [capacitySupport_card, capacityU8Support_card] at card_eq
  omega

end
end M14SourceGeneratedContributionCapacitySupportSeparation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySupportSeparation.capacitySupport_card
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySupportSeparation.capacityU8Support_card
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySupportSeparation.capacitySupport_ne_capacityU8Support
