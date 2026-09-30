import H0mework.Probability.Source.Field
import H0mework.Realization.Operations.ObservationModel

/-! Paired raw observations share the old autonomous coimage of their one native source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.JointModel

open SourceGeneratedActionObservationHistory

noncomputable section

universe u

variable {State Left Right : Type u} [AddCommGroup Left] [AddCommGroup Right]
variable (step : State → State) (leftRead : State → Left) (rightRead : State → Right)

def pairRead (state : State) : Left × Right := (leftRead state, rightRead state)

theorem observation_pair : observation (pairRead leftRead rightRead) =
    (observation leftRead).prod (observation rightRead) := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  change observation (pairRead leftRead rightRead) (sourcePoint state) =
    (observation leftRead).prod (observation rightRead) (sourcePoint state)
  simp only [observation_point, LinearMap.prod_apply, Function.prod, pairRead]

theorem kernel_pair :
    LinearMap.ker (sourceMap (sourceAction step) (observation (pairRead leftRead rightRead))) =
      LinearMap.ker (sourceMap (sourceAction step) (observation leftRead)) ⊓
        LinearMap.ker (sourceMap (sourceAction step) (observation rightRead)) := by
  ext word
  simp only [Submodule.mem_inf, mem_kernel_iff, observation_pair, LinearMap.prod_apply,
    Function.prod, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, forall_and]

def leftMap : Model (sourceAction step) (observation (pairRead leftRead rightRead)) →ₗ[ℤ]
    Model (sourceAction step) (observation leftRead) :=
  Submodule.factor ((kernel_pair step leftRead rightRead).le.trans inf_le_left)

def rightMap : Model (sourceAction step) (observation (pairRead leftRead rightRead)) →ₗ[ℤ]
    Model (sourceAction step) (observation rightRead) :=
  Submodule.factor ((kernel_pair step leftRead rightRead).le.trans inf_le_right)

theorem leftMap_projection (word : Carrier State) :
    leftMap step leftRead rightRead (projection (sourceAction step) (observation (pairRead leftRead rightRead)) word) =
      projection (sourceAction step) (observation leftRead) word := rfl

theorem rightMap_projection (word : Carrier State) :
    rightMap step leftRead rightRead (projection (sourceAction step) (observation (pairRead leftRead rightRead)) word) =
      projection (sourceAction step) (observation rightRead) word := rfl

theorem leftMap_surjective : Function.Surjective (leftMap step leftRead rightRead) := by
  have source := (actionRow (sourceAction step) (observation leftRead)).restriction_surjective
  change Function.Surjective (projection (sourceAction step) (observation leftRead)) at source
  apply Function.Surjective.of_comp
    (g := projection (sourceAction step) (observation (pairRead leftRead rightRead)))
  simpa only [Function.comp_def, leftMap_projection] using source

theorem rightMap_surjective : Function.Surjective (rightMap step leftRead rightRead) := by
  have source := (actionRow (sourceAction step) (observation rightRead)).restriction_surjective
  change Function.Surjective (projection (sourceAction step) (observation rightRead)) at source
  apply Function.Surjective.of_comp
    (g := projection (sourceAction step) (observation (pairRead leftRead rightRead)))
  simpa only [Function.comp_def, rightMap_projection] using source

theorem pair_fibre_iff (left right : Carrier State) :
    projection (sourceAction step) (observation (pairRead leftRead rightRead)) left =
        projection (sourceAction step) (observation (pairRead leftRead rightRead)) right ↔
      projection (sourceAction step) (observation leftRead) left =
          projection (sourceAction step) (observation leftRead) right ∧
        projection (sourceAction step) (observation rightRead) left =
          projection (sourceAction step) (observation rightRead) right := by
  rw [model_fibre_iff, model_fibre_iff, model_fibre_iff]
  simp only [observation_pair, LinearMap.prod_apply, Function.prod, Prod.ext_iff, forall_and]

theorem sameRead_maps : leftMap step leftRead leftRead = rightMap step leftRead leftRead := rfl

end
end SourceOwnedObservationHistory.JointModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
