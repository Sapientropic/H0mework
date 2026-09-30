import H0mework.Versions.X.Fock.HistoryConditional.NativeBirthMerge

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem previous_birth_coordinate (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) :
    SourceGInformationCost.coordinateRead (inventoryBound runtime + 2)
      (SourceConditionalNativePosterior.decoder runtime read value) = 0 := by
  rw [SourceConditionalNativePosterior.decoder, SourceConditionalNativePosterior.model]
  simp only [map_sum, map_smul, ← SourceConditionalInventory.values_original]
  apply Finset.sum_eq_zero
  intro actor _
  have old := SourceGInformationCost.coordinate_actual (inventoryBound runtime + 1)
    (Fin.last (inventoryBound runtime + 1)) actor.castSucc
  rw [if_neg (Fin.castSucc_ne_last actor), SourceConditionalInventory.values_retained] at old
  change SourceGInformationCost.coordinateRead (inventoryBound runtime + 2)
    (SourceConditionalInventory.values (inventoryBound runtime) actor) = 0 at old
  rw [old, smul_zero]

theorem birth_coordinate (runtime : LivingRuntimeState process) :
    SourceGInformationCost.coordinateRead (inventoryBound runtime + 2)
      (SourceConditionalInventory.born (inventoryBound runtime)) = 1 := by
  have paid := SourceGInformationCost.coordinate_actual (inventoryBound runtime + 1)
    (Fin.last (inventoryBound runtime + 1)) (Fin.last (inventoryBound runtime + 1))
  simpa only [SourceConditionalInventory.born, Fin.val_last, ite_true] using paid

theorem stalePenalty_positive (runtime : LivingRuntimeState process) (read : Nat → Key) :
    0 < stalePenalty runtime read := by
  have different : SourceConditionalInventory.born (inventoryBound runtime) ≠
      SourceConditionalNativePosterior.decoder runtime read (read (inventoryBound runtime + 1)) := by
    intro same
    have coordinate := congrArg (SourceGInformationCost.coordinateRead (inventoryBound runtime + 2)) same
    rw [birth_coordinate, previous_birth_coordinate] at coordinate
    exact one_ne_zero coordinate
  rw [stalePenalty]
  exact div_pos (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr different)) 2) (by positivity)

theorem stale_strict (runtime : LivingRuntimeState process) (read : Nat → Key) :
    total runtime.tick.next read <
      ∑ actor : Actors runtime.tick.next,
        ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
          SourceConditionalNativePosterior.decoder runtime read (read actor.val)‖ ^ 2 := by
  rw [stale_loss]
  exact lt_add_of_pos_right _ (stalePenalty_positive runtime read)

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
