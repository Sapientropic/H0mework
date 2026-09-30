import H0mework.Versions.X.Fock.HistoryConditional.MergeLossLoss

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalMergeLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

def gap (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) : ℝ :=
  ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
    ‖SourceConditionalNativePosterior.decoder runtime read (read actor.val) - decoder runtime read forget (forget (read actor.val))‖ ^ 2

theorem gap_zero_iff (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    gap runtime read forget = 0 ↔ ∀ actor : Actors runtime,
      SourceConditionalNativePosterior.decoder runtime read (read actor.val) = decoder runtime read forget (forget (read actor.val)) := by
  rw [gap, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))]
  constructor
  · intro all actor
    have term := all actor (Finset.mem_univ actor)
    have weight : (historyPMF (inventoryBound runtime) actor).toReal ≠ 0 := by
      rw [SourceUniformFibreVariance.source_weight]
      positivity
    have zero := (mul_eq_zero.mp term).resolve_left weight
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp zero))
  · intro all actor _
    rw [all actor, sub_self, norm_zero]
    simp

theorem fine_readback (runtime : LivingRuntimeState process) (read : Nat → Fine) (left right : Actors runtime)
    (same : SourceConditionalNativePosterior.decoder runtime read (read left.val) =
      SourceConditionalNativePosterior.decoder runtime read (read right.val)) : read left.val = read right.val := by
  let query : Actors runtime → Fine := fun actor => read actor.val
  have leftSupported := SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) query left (positive runtime left)
  have rightSupported := SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) query right (positive runtime right)
  rw [SourceConditionalNativePosterior.decoder, SourceConditionalNativePosterior.decoder] at same
  have models := SourceActualImageStep.realize_injective runtime same
  rw [SourceConditionalNativePosterior.model_original _ _ _ leftSupported,
    SourceConditionalNativePosterior.model_original _ _ _ rightSupported] at models
  have retained := (SourcePosteriorReadback.recovered_support runtime query (query left) leftSupported left).mpr rfl
  rw [models] at retained
  exact (SourcePosteriorReadback.recovered_support runtime query (query right) rightSupported left).mp retained

theorem decoder_of_kernel (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse)
    (faithful : ∀ left right : Actors runtime, forget (read left.val) = forget (read right.val) → read left.val = read right.val)
    (actor : Actors runtime) :
    SourceConditionalNativePosterior.decoder runtime read (read actor.val) = decoder runtime read forget (forget (read actor.val)) := by
  let query : Actors runtime → Fine := fun index => read index.val
  let coarse : Actors runtime → Coarse := fun index => forget (read index.val)
  have fineSupported := SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) query actor (positive runtime actor)
  have coarseSupported := SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) coarse actor (positive runtime actor)
  have weights := SourceConditionalHistory.conditional_eq_of_fibre (historyPMF (inventoryBound runtime)) query coarse
    (query actor) (coarse actor) fineSupported coarseSupported
    (fun index => ⟨congrArg forget, faithful index actor⟩)
  have models := (SourcePosteriorReadback.estimates_equal_iff runtime query coarse (query actor) (coarse actor)
    fineSupported coarseSupported).mpr weights
  rw [decoder_original, SourceConditionalNativePosterior.decoder, SourceConditionalNativePosterior.decoder,
    SourceConditionalNativePosterior.model_original _ _ _ fineSupported,
    SourceConditionalNativePosterior.model_original _ _ _ coarseSupported]
  exact congrArg (SourceConditionalVector.realizeModel runtime) models

theorem lossless_iff (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    gap runtime read forget = 0 ↔
      ∀ left right : Actors runtime, forget (read left.val) = forget (read right.val) → read left.val = read right.val := by
  rw [gap_zero_iff]
  constructor
  · intro same left right merged
    apply fine_readback runtime read left right
    exact (same left).trans ((congrArg (decoder runtime read forget) merged).trans (same right).symm)
  · exact fun faithful actor => decoder_of_kernel runtime read forget faithful actor


theorem gap_nonnegative (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    0 ≤ gap runtime read forget :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

theorem gap_positive_of_collision (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse)
    (left right : Actors runtime) (merged : forget (read left.val) = forget (read right.val))
    (different : read left.val ≠ read right.val) : 0 < gap runtime read forget := by
  have nonzero : gap runtime read forget ≠ 0 := fun zero => different ((lossless_iff runtime read forget).mp zero left right merged)
  exact lt_of_le_of_ne (gap_nonnegative runtime read forget) (Ne.symm nonzero)

attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

theorem information_of_lossless (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse)
    (preserved : gap runtime read forget = 0) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => read actor.val)
      (SourceConditionalNext.Image.actual (SourceConditionalModel.nextRead runtime)) (positive runtime) =
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => forget (read actor.val))
      (SourceConditionalNext.Image.actual (SourceConditionalModel.nextRead runtime)) (positive runtime) := by
  apply SourceConditionalNext.conditionalEntropy_eq_of_kernel
  intro left right
  exact ⟨congrArg forget, (lossless_iff runtime read forget).mp preserved left right⟩

end
end SourceConditionalMergeLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
