import H0mework.Fock.InverseOptimal.Field
import H0mework.Fock.InverseDistribution.Positive

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimal

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem no_double_shift_recovery {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (read : Nat → Key) (candidate : SourceJointClockGraph.Carrier) :
    SourceCompiledGWord.effect depth [.inl ⟨⟩, .inl ⟨⟩] candidate ≠
      SourceConditionalNativePosterior.decoder runtime read (read 0) := by
  have positive : 0 < ‖SourceGWordInverse.residual depth [.inl ⟨⟩, .inl ⟨⟩]
      (SourceConditionalNativePosterior.decoder runtime read (read 0))‖ ^ 2 := by
    rw [SourceInverseDistributionLoss.generated_residual_norm]
    exact SourceInverseDistributionLoss.double_shift_loss_positive read (inventoryBound runtime)
  have lower := optimal depth [.inl ⟨⟩, .inl ⟨⟩] (SourceConditionalNativePosterior.decoder runtime read (read 0)) candidate
  change ‖SourceGWordInverse.residual depth [.inl ⟨⟩, .inl ⟨⟩]
    (SourceConditionalNativePosterior.decoder runtime read (read 0))‖ ^ 2 ≤ _ at lower
  intro same
  rw [same, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at lower
  exact (not_lt_of_ge lower) positive

end
end SourceInverseDistributionOptimal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
