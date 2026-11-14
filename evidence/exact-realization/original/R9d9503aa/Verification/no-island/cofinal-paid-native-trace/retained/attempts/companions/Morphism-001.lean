import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Trace

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open SourceOperationEffects SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
open SourceGeneratedPrimePowerCompletion

variable {S : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]

/-- The original formal word and complete old/effect pair induce the existing residual morphism. -/
def inventoryMorphism {s : S} (p : Nat.Primes) (old increment : Env V X) :
    Morphism (updateInventory (R := ℤ) (s := s) old increment)
      (updateInventory (R := ℤ) (s := s) (environment p old) (environment p increment)) where
  sourceMap := wordMap p s
  targetMap := (canonicalLinearMap (L := V s) p).prodMap (canonicalLinearMap (L := V s) p)
  commutes := by
    apply Finsupp.lhom_ext
    intro term coefficient
    simp only [LinearMap.comp_apply, word_map_single, updateInventory, LinearMap.prod_apply,
      LinearMap.prodMap_apply, evaluation, effectEvaluator, Finsupp.linearCombination_single,
      expression_eval, expression_effect, map_smul]

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
