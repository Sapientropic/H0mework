import H0mework.Realization.ObservationActions.WordsModel
import H0mework.Realization.ScalarCofinal.FiniteLift

/-! The already generated whole action-word inventory makes one source witness control the entire old completion. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords

open SourceGeneratedActionObservationHistory CategoryTheory CategoryTheory.Limits

noncomputable section
universe r u
variable {R : Type r} [CommRing R]
variable {I C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (actions : I → C →ₗ[R] C) (read : C →ₗ[R] B) (primary : I)

theorem inventory_controls_completion (left right : C) (same : inventory actions read left = inventory actions read right) :
    sourceMap (actions primary) (inventory actions read) left = sourceMap (actions primary) (inventory actions read) right := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply LinearMap.mem_ker.mp
  rw [original_kernel]
  rw [LinearMap.mem_ker, map_sub, same, sub_self]

theorem full_source_surjective : Function.Surjective (sourceMap (actions primary) (inventory actions read)) := by
  intro value
  let tower := data (actions primary) (inventory actions read)
  let laws := compatible (actions primary) (inventory actions read)
  obtain ⟨source, first⟩ := tower.finite_lift laws value 0
  refine ⟨source, ?_⟩
  apply Limits.Concrete.limit_ext (tower.quotientTower laws)
  intro stage
  apply tower.stageRealization_injective stage.unop
  change stageRead (actions primary) (inventory actions read) stage.unop
    (sourceMap (actions primary) (inventory actions read) source) =
    stageRead (actions primary) (inventory actions read) stage.unop value
  obtain ⟨later, agrees⟩ := tower.finite_lift laws value stage.unop
  have sameZero := (first 0 le_rfl).trans (agrees 0 (Nat.zero_le _)).symm
  have sameInventory := congrFun (congrArg (tower.stageRealization 0) sameZero) (0 : Fin 1)
  change inventory actions read source = inventory actions read later at sameInventory
  rw [inventory_controls_completion actions read primary source later sameInventory, source_reads_prefix]
  exact congrArg (tower.stageRealization stage.unop) (agrees stage.unop le_rfl)

end
end SourceGeneratedActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
