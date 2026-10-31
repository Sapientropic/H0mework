import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.SourceGeneratedContributionCapacitySupportSeparation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Action.SourceGeneratedContributionCapacityReopeningState

/-!
# Capacity reopening support separation

The reopening phase lift has support cardinality `50`, distinct from every
earlier canonical runtime network (`2, 6, 12, 24, 25`).
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityReopeningSupportSeparation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M14SourceGeneratedContributionCapacitySupportSeparation
open M14SourceGeneratedContributionMergeSupportSeparation
open M14SourceGeneratedContributionCapacityReopeningWorld
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionCapacityFailure

abbrev ReopeningN := ReopeningNAt canonicalOldVisit

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

local instance reopeningSupportFinite : Finite ReopeningN.Support := by
  change Finite (CapacityU8N.Support × Bool)
  infer_instance

theorem reopeningSupport_card : Nat.card ReopeningN.Support = 50 := by
  change Nat.card (CapacityU8N.Support × Bool) = 50
  rw [Nat.card_prod, capacityU8Support_card]
  rw [Nat.card_eq_fintype_card]
  simp

theorem originalSupport_ne_reopeningSupport :
    OriginalN.Support ≠ ReopeningN.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [originalSupport_card, reopeningSupport_card] at card_eq
  omega

theorem revisedSupport_ne_reopeningSupport :
    RevisedN.Support ≠ ReopeningN.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [revisedSupport_card, reopeningSupport_card] at card_eq
  omega

theorem mergeSupport_ne_reopeningSupport :
    MergeN.Support ≠ ReopeningN.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [mergeSupport_card, reopeningSupport_card] at card_eq
  omega

theorem capacitySupport_ne_reopeningSupport :
    CapacityN.Support ≠ ReopeningN.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [capacitySupport_card, reopeningSupport_card] at card_eq
  omega

theorem capacityU8Support_ne_reopeningSupport :
    CapacityU8N.Support ≠ ReopeningN.Support := by
  intro equality
  have card_eq := congrArg (fun carrier : Type => Nat.card carrier) equality
  rw [capacityU8Support_card, reopeningSupport_card] at card_eq
  omega

end
end M14SourceGeneratedContributionCapacityReopeningSupportSeparation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningSupportSeparation.reopeningSupport_card
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningSupportSeparation.capacityU8Support_ne_reopeningSupport
