import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Admission

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.AdmissionReceipt

open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}

/-- The full old/effect word action is the sum of its actual signed items. -/
theorem update_inventory_formal_items (old increment : Env V X) (items : List (Expr V X s × ℤ)) :
    (∑ index : Fin items.length,
      let item := items.get index
      item.2 • (liftExpr item.1).eval (pairEnvironment old increment)) =
      updateInventory (R := ℤ) old increment (formalItems items) := by
  let evaluate := fun item : Expr V X s × ℤ =>
    item.2 • (liftExpr item.1).eval (pairEnvironment old increment)
  change (∑ index : Fin items.length, evaluate (items.get index)) = _
  rw [← List.sum_ofFn]
  change (List.ofFn (evaluate ∘ items.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]
  calc
    _ = ((evaluation (R := ℤ) (pairEnvironment old increment)).comp (liftMap (R := ℤ))) (formalItems items) := by
      rw [formalItems, map_list_sum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro item _
      simp only [Function.comp_apply, LinearMap.comp_apply, liftMap, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single, evaluation, Finsupp.linearCombination_single, evaluate]
    _ = _ := LinearMap.congr_fun (evaluation_liftMap (R := ℤ) old increment) _

end SourceInventoryExecutionFeed.AdmissionReceipt
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
