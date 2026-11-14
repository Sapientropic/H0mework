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

local instance completedInventoryModule (p : Nat.Primes) (s : S) :
    Module ℤ (Value V p s × Value V p s) :=
  Prod.instModule

/-- The original formal word and complete old/effect pair induce the existing residual morphism. -/
def inventoryMorphism {s : S} (p : Nat.Primes) (old increment : Env V X) :
    Morphism (updateInventory (R := ℤ) (s := s) old increment)
      (updateInventory (R := ℤ) (s := s) (environment p old) (environment p increment)) where
  sourceMap := wordMap p s
  targetMap := (canonicalLinearMap (L := V s) p).prodMap (canonicalLinearMap (L := V s) p)
  commutes := by
    apply Finsupp.lhom_ext
    intro term coefficient
    let read : V s →ₗ[ℤ] Value V p s := canonicalLinearMap p
    change (read (evaluation (R := ℤ) old (Finsupp.single term coefficient)),
        read (effectEvaluator (R := ℤ) old increment (Finsupp.single term coefficient))) =
      (evaluation (R := ℤ) (environment p old) (wordMap p s (Finsupp.single term coefficient)),
        effectEvaluator (R := ℤ) (environment p old) (environment p increment)
          (wordMap p s (Finsupp.single term coefficient)))
    rw [word_map_single]
    simp only [evaluation, effectEvaluator, Finsupp.linearCombination_single, expression_eval, expression_effect]
    exact Prod.ext (map_smul read coefficient _) (map_smul read coefficient _)

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
