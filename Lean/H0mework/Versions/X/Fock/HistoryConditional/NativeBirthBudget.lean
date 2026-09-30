import H0mework.Versions.X.Fock.HistoryConditional.NativeBirthFeedback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
variable {Key : Type*} [DecidableEq Key]

theorem total_information_cost [MeasurableSpace Key] [MeasurableSingletonClass Key]
    (runtime : LivingRuntimeState process) (read : Nat → Key) :
    SourceConditionalInventory.cost (inventoryBound runtime) (fun actor : Actors runtime => read actor.val) +
      ((inventoryBound runtime + 1 : Nat) : ℝ) *
        (Real.exp (2 * SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
          (fun actor : Actors runtime => read actor.val) (SourceConditionalNext.Image.actual (nextRead runtime))
          (positive runtime)) - 1) / 12 ≤ total runtime read := by
  have lower := SourceGInformationCost.decoder_information_lower (inventoryBound runtime)
    (fun actor : Actors runtime => read actor.val) (SourceConditionalNativePosterior.decoder runtime read)
  rw [← SourceInformationReadback.model_information runtime (fun actor : Actors runtime => read actor.val)] at lower
  have paid := mul_le_mul_of_nonneg_left lower (Nat.cast_nonneg (inventoryBound runtime + 1) : (0 : ℝ) ≤ _)
  simp only [mul_add, SourceConditionalInventory.sum_count] at paid
  have nonzero : (inventoryBound runtime : ℝ) + 1 ≠ 0 := by positivity
  dsimp only [total]
  convert paid using 1
  · rfl
  · push_cast
    field_simp

variable {Coarse : Type*} [DecidableEq Coarse] [MeasurableSpace Coarse] [MeasurableSingletonClass Coarse]

theorem next_budget (runtime : LivingRuntimeState process) (read : Nat → Key) (forget : Key → Coarse) :
    SourceConditionalInventory.cost (inventoryBound runtime.tick.next)
      (fun actor : Actors runtime.tick.next => forget (read actor.val)) +
    ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) *
      (Real.exp (2 *
        ((((inventoryBound runtime + 1 : Nat) : ℝ) *
          (SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
            (fun actor : Actors runtime => read actor.val) (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) +
              SourceConditionalInformationLoss.amount runtime read forget) +
          informationIncrement (SourceConditionalNativeMerge.count read forget (inventoryBound runtime)
            (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (forget (read (inventoryBound runtime + 1))))) /
          ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ))) - 1) / 12 ≤
      total runtime read + ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalMergeLoss.gap runtime read forget +
        innovation runtime (forget ∘ read) := by
  rw [SourceConditionalNativeMerge.count_generated]
  have generated := information_next runtime (forget ∘ read)
  simp only [Function.comp_apply] at generated
  rw [← SourceConditionalInformationLoss.information_balance runtime read forget] at generated
  have nonzero : ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) ≠ 0 := by positivity
  have resolved := (eq_div_iff nonzero).mpr ((mul_comm _ _).trans generated)
  have lower := total_information_cost runtime.tick.next (forget ∘ read)
  simp only [Function.comp_apply] at lower
  rw [resolved, minimum_update, total_gap runtime read forget] at lower
  exact lower

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
