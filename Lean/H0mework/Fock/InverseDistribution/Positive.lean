import H0mework.Fock.InverseDistribution.LossConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionLoss

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem double_shift_loss_positive {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) :
    0 < ∑ actor : Fin (bound + 1),
      ‖(((SourceInverseDistributionAction.generate read [none, none] bound (read 0)).2 actor).2 : ℂ)‖ ^ 2 := by
  rw [SourceInverseDistributionAction.generated_source, SourceInverseDistributionStream.generated_source]
  apply Finset.sum_pos'
  · intro actor _
    exact sq_nonneg _
  · refine ⟨(0 : Fin (bound + 1)), Finset.mem_univ _, ?_⟩
    change 0 < ‖((SourceNativeInverseDistribution.splitEntry
      (SourceCopyWordAffine.compile [none, none]) 1
      ((SourceConditionalNativeObservers.generate read bound (read 0)).2 0)).2 : ℂ)‖ ^ 2
    have entry (weight : ℚ) :
        (SourceNativeInverseDistribution.splitEntry (SourceCopyWordAffine.compile [none, none]) 1 weight).2 = weight := rfl
    rw [entry, SourceConditionalNativePosterior.weight_fibre]
    simp only [Fin.val_zero, ite_true]
    have positive := SourceConditionalNativePosterior.count_positive read bound (read 0) (0 : Fin (bound + 1)) rfl
    exact pow_pos (norm_pos_iff.mpr (Rat.cast_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr positive.ne')))) _

theorem double_shift_not_restored {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (read : Nat → Key) :
    SourceCompiledGWord.effect depth [.inl ⟨⟩, .inl ⟨⟩]
      (SourceGWordInverse.recover depth [.inl ⟨⟩, .inl ⟨⟩] (SourceConditionalNativePosterior.decoder runtime read (read 0))) ≠
      SourceConditionalNativePosterior.decoder runtime read (read 0) := by
  have positive : 0 < ‖SourceGWordInverse.residual depth [.inl ⟨⟩, .inl ⟨⟩]
      (SourceConditionalNativePosterior.decoder runtime read (read 0))‖ ^ 2 := by
    rw [generated_residual_norm]
    exact double_shift_loss_positive read (inventoryBound runtime)
  intro same
  change 0 < ‖SourceConditionalNativePosterior.decoder runtime read (read 0) -
    SourceCompiledGWord.effect depth [.inl ⟨⟩, .inl ⟨⟩]
      (SourceGWordInverse.recover depth [.inl ⟨⟩, .inl ⟨⟩] (SourceConditionalNativePosterior.decoder runtime read (read 0)))‖ ^ 2 at positive
  rw [same, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at positive
  exact (lt_irrefl 0) positive

end
end SourceInverseDistributionLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
