import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Trace

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
    have preserves (value : V s) : read (coefficient • value) =
        (Completion (L := V s) p).isModule.smul coefficient (read value) :=
      (map_zsmul read.toAddMonoidHom coefficient value).trans
        (int_smul_eq_zsmul (Completion (L := V s) p).isModule coefficient (read value)).symm
    exact Prod.ext (preserves _) (preserves _)

theorem inventory_read {s : S} (p : Nat.Primes) (old increment : Env V X) (word : Formal ℤ V X s) :
    updateInventory (R := ℤ) (environment p old) (environment p increment) (wordMap p s word) =
      (canonicalLinearMap p (evaluation (R := ℤ) old word),
        canonicalLinearMap p (effectEvaluator (R := ℤ) old increment word)) :=
  (LinearMap.congr_fun (inventoryMorphism (s := s) p old increment).commutes word).symm

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
