import H0mework.Fock.HistoryConditional.ActualImageInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def distribution (runtime : LivingRuntimeState process) : PMF (Image runtime) :=
  (historyPMF (inventoryBound runtime)).map (SourceConditionalNext.Image.actual (nextRead runtime))

private theorem map_at_injective {A B : Type*} (source : PMF A) (map : A → B)
    (injective : Function.Injective map) (point : A) : source.map map (map point) = source point := by
  rw [PMF.map_apply, tsum_eq_single point]
  · exact if_pos rfl
  · intro other different
    exact if_neg (fun same => different (injective same).symm)

theorem distribution_mass (runtime : LivingRuntimeState process) (value : Image runtime) :
    distribution runtime value = ((inventoryBound runtime + 1 : Nat) : ENNReal)⁻¹ := by
  obtain ⟨index, same⟩ := value.property
  have actual : value = SourceConditionalNext.Image.actual (nextRead runtime) index := Subtype.ext same.symm
  rw [actual, distribution, map_at_injective]
  · exact historyPMF_apply _ _
  · intro left right same
    exact nextRead_injective runtime (congrArg Subtype.val same)

theorem distribution_unit (runtime : LivingRuntimeState process) (value : Image runtime) :
    ((inventoryBound runtime + 1 : Nat) : ENNReal) * distribution runtime value = 1 := by
  rw [distribution_mass]
  exact ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)

theorem next_distribution_retain (runtime : LivingRuntimeState process) (value : Image runtime.tick.next) :
    ((inventoryBound runtime + 2 : Nat) : ENNReal) * distribution runtime.tick.next value =
      ((inventoryBound runtime + 1 : Nat) : ENNReal) * ((distribution runtime).map (retain runtime) value) + PMF.pure (birth runtime) value := by
  have nextUnit := distribution_unit runtime.tick.next value
  rw [next_bound] at nextUnit
  change ((inventoryBound runtime + 2 : Nat) : ENNReal) * distribution runtime.tick.next value = 1 at nextUnit
  rw [nextUnit]
  rcases retain_complete runtime value with ⟨previous, rfl⟩ | rfl
  · rw [map_at_injective _ _ (retain_injective runtime), distribution_unit, PMF.pure_apply,
      if_neg (retain_ne_birth runtime previous), add_zero]
  · have absent : (distribution runtime).map (retain runtime) (birth runtime) = 0 := by
      rw [PMF.map_apply]
      trans (∑' _ : Image runtime, (0 : ENNReal))
      · apply tsum_congr
        intro previous
        exact if_neg (Ne.symm (retain_ne_birth runtime previous))
      · exact tsum_zero
    rw [absent, mul_zero, PMF.pure_apply, if_pos rfl, zero_add]

theorem next_distribution_step (runtime : LivingRuntimeState process) (value : Image runtime.tick.next) :
    ((inventoryBound runtime + 2 : Nat) : ENNReal) * distribution runtime.tick.next value =
      ((inventoryBound runtime + 1 : Nat) : ENNReal) * ((distribution runtime).map (step runtime) value) + PMF.pure (first runtime) value := by
  have nextUnit := distribution_unit runtime.tick.next value
  rw [next_bound] at nextUnit
  change ((inventoryBound runtime + 2 : Nat) : ENNReal) * distribution runtime.tick.next value = 1 at nextUnit
  rw [nextUnit]
  rcases step_complete runtime value with ⟨previous, rfl⟩ | rfl
  · rw [map_at_injective _ _ (step_injective runtime), distribution_unit, PMF.pure_apply,
      if_neg (step_ne_first runtime previous), add_zero]
  · have absent : (distribution runtime).map (step runtime) (first runtime) = 0 := by
      rw [PMF.map_apply]
      trans (∑' _ : Image runtime, (0 : ENNReal))
      · apply tsum_congr
        intro previous
        exact if_neg (Ne.symm (step_ne_first runtime previous))
      · exact tsum_zero
    rw [absent, mul_zero, PMF.pure_apply, if_pos rfl, zero_add]

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
