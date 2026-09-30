import H0mework.Versions.X.Fock.InverseDistribution.LossWord
import H0mework.Versions.X.Fock.InverseDistribution.ActionGenerated

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionLoss

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceCopyTimeModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem residual_formula (bound depth : Nat) (word : List (Fock.Letter depth)) (weights : Fin (bound + 1) → ℚ) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let remainder := SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
      (SourceNativeInverseDistribution.residual bound program weights))
    SourceGWordInverse.residual depth word
      (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound weights))) =
      remainder - SourceCopyGraph.axes (mass remainder) (SourceJointClockGraph.clock remainder) := by
  dsimp only
  have split := SourceNativeInverseDistribution.g_reconstruction bound depth word weights
  have inverse := congrArg (SourceGWordInverse.recover depth word) split
  rw [map_add, SourceGWordInverse.recover_effect, SourceNativeInverseDistribution.residual_recovery] at inverse
  change SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound weights)) -
    SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word
      (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound weights)))) = _
  rw [← inverse, map_add, SourceGWordInverse.effect_axes]
  have nonzero : ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (SourceCompiledWordOperator.slope_positive _).ne'
  rw [mul_inv_cancel_left₀ nonzero, sub_add_cancel, ← split]
  abel

theorem residual_norm (bound depth : Nat) (word : List (Fock.Letter depth)) (weights : Fin (bound + 1) → ℚ) :
    ‖SourceGWordInverse.residual depth word
      (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound weights)))‖ ^ 2 =
      ∑ actor : Fin (bound + 1), ‖((SourceNativeInverseDistribution.split bound
        (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) weights actor).2 : ℂ)‖ ^ 2 := by
  rw [residual_formula, norm_sub_axes]
  exact word_hilbert_norm bound _

theorem generated_residual_norm {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    ‖SourceGWordInverse.residual depth word (SourceConditionalNativePosterior.decoder runtime read key)‖ ^ 2 =
      ∑ actor : SourceConditionalModel.Actors runtime,
        ‖(((SourceInverseDistributionAction.generate read (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) key).2 actor).2 : ℂ)‖ ^ 2 := by
  rw [SourceConditionalNativeBirth.decoder_word, residual_norm,
    SourceInverseDistributionAction.generated_source, SourceInverseDistributionStream.generated_source]

end
end SourceInverseDistributionLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
