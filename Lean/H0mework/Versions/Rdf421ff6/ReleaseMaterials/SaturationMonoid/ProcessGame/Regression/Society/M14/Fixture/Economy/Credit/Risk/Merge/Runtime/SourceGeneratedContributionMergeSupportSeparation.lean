import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Root.SourceGeneratedContributionMergeRoot
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedWorld

/-!
# M14 contribution-merge support separation

At the initial M9 old-root visit, the original, revised split and
contribution-merge networks have pairwise distinct support carriers.  This is
pure type-level separation: no process, state, root, program, action or
runtime is constructed.

The first two separations use the existing three-point pigeonhole argument.
The revised/merge separation uses the exact identity
`MergeSupport = RevisedSupport × Bool`: the revised carrier is finite and
nonempty, so it cannot be equipotent to two disjoint copies of itself.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeSupportSeparation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8RevisedWorld
open M14SourceGeneratedContributionMergeWorld

abbrev OriginalN := M9ProofCarryingRenewalU8Failure.N
abbrev RevisedN := M9ProofCarryingRenewalU8RevisedWorld.NewN
abbrev MergeN := TargetN M9ProofCarryingRenewalU8Failure.rooted

/-! ## Original versus revised -/

/-- Reproved locally to avoid importing the canonical runtime and creating a
dependency cycle. -/
theorem originalSupport_ne_revisedSupport :
    OriginalN.Support ≠ RevisedN.Support := by
  intro equality
  let restrict : RevisedN.Support → Bool := Eq.mp equality.symm
  have restrict_injective : Function.Injective restrict :=
    RootInquiryU8CompletionRegression.eqMp_injective equality.symm
  rcases RootInquiryU8CompletionRegression.three_bools_collide
      (restrict (.inl false, false))
      (restrict (.inl true, false))
      (restrict (.inr .completion, false)) with
      collision | collision | collision
  · cases restrict_injective collision
  · cases restrict_injective collision
  · cases restrict_injective collision

/-! ## Original versus merge -/

theorem originalSupport_ne_mergeSupport :
    OriginalN.Support ≠ MergeN.Support := by
  intro equality
  let restrict : MergeN.Support → Bool := Eq.mp equality.symm
  have restrict_injective : Function.Injective restrict :=
    RootInquiryU8CompletionRegression.eqMp_injective equality.symm
  rcases RootInquiryU8CompletionRegression.three_bools_collide
      (restrict ((.inl false, false), false))
      (restrict ((.inl true, false), false))
      (restrict ((.inr .completion, false), false)) with
      collision | collision | collision
  · cases restrict_injective collision
  · cases restrict_injective collision
  · cases restrict_injective collision

/-! ## Revised versus merge -/

set_option linter.style.haveILetI false in
theorem revisedSupport_ne_mergeSupport :
    RevisedN.Support ≠ MergeN.Support := by
  intro equality
  letI : Finite
      (GeneratedDirectionAt M9ProofCarryingRenewalU8Failure.rooted) :=
    Finite.of_injective
      (fun _ : GeneratedDirectionAt M9ProofCarryingRenewalU8Failure.rooted =>
        PUnit.unit)
      (by
        intro left right _
        cases left
        cases right
        rfl)
  letI : Finite RevisedN.Support := by
    change Finite
      ((Bool ⊕ GeneratedDirectionAt
        M9ProofCarryingRenewalU8Failure.rooted) × Bool)
    infer_instance
  letI : Nonempty RevisedN.Support := ⟨(.inl false, false)⟩
  let carrierEquiv : RevisedN.Support ≃ MergeN.Support :=
    Equiv.cast equality
  have card_eq := Nat.card_congr carrierEquiv
  change Nat.card RevisedN.Support =
    Nat.card (RevisedN.Support × Bool) at card_eq
  rw [Nat.card_prod] at card_eq
  have bool_card : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_bool
  rw [bool_card] at card_eq
  have card_positive : 0 < Nat.card RevisedN.Support :=
    Nat.card_pos
  omega

/-! ## Whole-network consequences -/

theorem originalNetwork_ne_revisedNetwork : OriginalN ≠ RevisedN := by
  intro network_eq
  exact originalSupport_ne_revisedSupport
    (congrArg WorldRelationNetwork.Support network_eq)

theorem originalNetwork_ne_mergeNetwork : OriginalN ≠ MergeN := by
  intro network_eq
  exact originalSupport_ne_mergeSupport
    (congrArg WorldRelationNetwork.Support network_eq)

theorem revisedNetwork_ne_mergeNetwork : RevisedN ≠ MergeN := by
  intro network_eq
  exact revisedSupport_ne_mergeSupport
    (congrArg WorldRelationNetwork.Support network_eq)

end
end M14SourceGeneratedContributionMergeSupportSeparation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeSupportSeparation.originalSupport_ne_revisedSupport
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeSupportSeparation.originalSupport_ne_mergeSupport
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeSupportSeparation.revisedSupport_ne_mergeSupport
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeSupportSeparation.revisedNetwork_ne_mergeNetwork
