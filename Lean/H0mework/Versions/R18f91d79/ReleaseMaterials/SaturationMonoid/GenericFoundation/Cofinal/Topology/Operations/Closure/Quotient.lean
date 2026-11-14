import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations CofinalHistorySettlement

variable {S Root : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before after : Expr V X s}

local notation "history" "[" root "," paid "]" => prefixHistory root (exposure paid)

private theorem paid_completion_kernel (root : RootedAccountedUnfolding Root) (paid : Trace old before after)
    (word : history[root, paid].generatorClosure) :
    word ∈ history[root, paid].relationInGeneratorClosure ↔ coefficientSum word.val = 0 := by
  refine (Submodule.Quotient.mk_eq_zero history[root, paid].relationInGeneratorClosure).symm.trans ?_
  change history[root, paid].completionProjection word = 0 ↔ _
  constructor
  · intro vanished
    exact (paid_completion_source root paid word).symm.trans
      ((congrArg (paidCompletionEquiv root paid) vanished).trans (map_zero _))
  · intro vanished
    apply (paidCompletionEquiv root paid).injective
    exact (paid_completion_source root paid word).trans (vanished.trans (map_zero _).symm)

private def quotientMap (root : RootedAccountedUnfolding Root) (p : Nat.Primes) (paid : Trace old before after) :
    history[root, paid].CompletionCarrier →ₗ[ℤ] history[root, trace p paid].CompletionCarrier :=
  history[root, paid].relationInGeneratorClosure.mapQ history[root, trace p paid].relationInGeneratorClosure
    (generatorEquiv root p paid).toLinearMap (by
      intro word member
      change generatorEquiv root p paid word ∈ history[root, trace p paid].relationInGeneratorClosure
      apply (paid_completion_kernel root (trace p paid) _).mpr
      rw [generator_equiv_value, word_map_coefficientSum]
      exact (paid_completion_kernel root paid word).mp member)

private theorem quotient_map_coordinate (root : RootedAccountedUnfolding Root) (p : Nat.Primes)
    (paid : Trace old before after) (value : history[root, paid].CompletionCarrier) :
    paidCompletionEquiv root (trace p paid) (quotientMap root p paid value) = paidCompletionEquiv root paid value := by
  obtain ⟨word, rfl⟩ := history[root, paid].relationInGeneratorClosure.mkQ_surjective value
  change paidCompletionEquiv root (trace p paid)
    (history[root, trace p paid].completionProjection (generatorEquiv root p paid word)) =
    paidCompletionEquiv root paid (history[root, paid].completionProjection word)
  rw [paid_completion_source, paid_completion_source, generator_equiv_value, word_map_coefficientSum]

/-- The actual word map is an equivalence on the original paid presentation quotients. -/
def completionEquiv (root : RootedAccountedUnfolding Root) (p : Nat.Primes) (paid : Trace old before after) :
    history[root, paid].CompletionCarrier ≃ₗ[ℤ] history[root, trace p paid].CompletionCarrier :=
  LinearEquiv.ofBijective (quotientMap root p paid) ⟨by
    intro left right same
    apply (paidCompletionEquiv root paid).injective
    exact (quotient_map_coordinate root p paid left).symm.trans
      ((congrArg (paidCompletionEquiv root (trace p paid)) same).trans
        (quotient_map_coordinate root p paid right)), by
    intro target
    obtain ⟨word, rfl⟩ := history[root, trace p paid].relationInGeneratorClosure.mkQ_surjective target
    refine ⟨history[root, paid].completionProjection ((generatorEquiv root p paid).symm word), ?_⟩
    change history[root, trace p paid].completionProjection
      (generatorEquiv root p paid ((generatorEquiv root p paid).symm word)) =
      history[root, trace p paid].completionProjection word
    rw [LinearEquiv.apply_symm_apply]⟩

theorem completion_equiv_projection (root : RootedAccountedUnfolding Root) (p : Nat.Primes)
    (paid : Trace old before after) (word : history[root, paid].generatorClosure) :
    completionEquiv root p paid (history[root, paid].completionProjection word) =
      history[root, trace p paid].completionProjection (generatorEquiv root p paid word) := rfl

theorem completion_equiv_coordinate (root : RootedAccountedUnfolding Root) (p : Nat.Primes)
    (paid : Trace old before after) (value : history[root, paid].CompletionCarrier) :
    paidCompletionEquiv root (trace p paid) (completionEquiv root p paid value) = paidCompletionEquiv root paid value :=
  quotient_map_coordinate root p paid value

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
