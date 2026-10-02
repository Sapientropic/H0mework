import H0mework.Versions.R2.Probability.Empirical.Decoder

/-! Every raw decoder's source error splits into retained information and its distance from the generated transfer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability
open scoped InnerProductSpace

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

def sourceError (value : Space read runtime bound) (decoder : Field read → ℂ) : ℝ :=
  ∑ index : Fin (bound + 1), (historyPMF bound index).toReal *
    ‖value (fieldSample read runtime bound index) - decoder (nextAtom read runtime bound index)‖ ^ 2

def decoderError (value : Space read runtime.tick.next bound) (decoder : Field read → ℂ) : ℝ :=
  ∑ index : Fin (bound + 1), (historyPMF bound index).toReal *
    ‖value (nextAtom read runtime bound index) - decoder (nextAtom read runtime bound index)‖ ^ 2

theorem sourceError_eq_norm (value : Space read runtime bound) (decoder : Field read → ℂ) :
    sourceError read runtime bound value decoder =
      ‖value - pullback read runtime bound (decoderValue read runtime bound decoder)‖ ^ 2 := by
  rw [sourceError, sample_norm_sq]
  apply Finset.sum_congr rfl
  intro index _
  have evaluated := (sampleRead read runtime bound index).map_sub value
    (pullback read runtime bound (decoderValue read runtime bound decoder))
  simp only [sampleRead_apply] at evaluated
  rw [evaluated, pullback_at_sample, decoderValue_at_next]

theorem decoderError_eq_norm (value : Space read runtime.tick.next bound) (decoder : Field read → ℂ) :
    decoderError read runtime bound value decoder = ‖value - decoderValue read runtime bound decoder‖ ^ 2 := by
  rw [decoderError, sample_norm_sq]
  apply Finset.sum_congr rfl
  intro index _
  have evaluated := (sampleRead read runtime.tick.next bound index).map_sub value (decoderValue read runtime bound decoder)
  simp only [sampleRead_apply] at evaluated
  rw [evaluated, ← nextAtom_eq_next_sample, decoderValue_at_next]

theorem error_decomposition (value : Space read runtime bound) (decoder : Field read → ℂ) :
    sourceError read runtime bound value decoder = ‖residual read runtime bound value‖ ^ 2 +
      decoderError read runtime bound (transfer read runtime bound value) decoder := by
  rw [sourceError_eq_norm, decoderError_eq_norm]
  have reconstructed :
      pullback read runtime bound (transfer read runtime bound value - decoderValue read runtime bound decoder) +
          residual read runtime bound value = value - pullback read runtime bound (decoderValue read runtime bound decoder) := by
    rw [map_sub]
    calc
      _ = (pullback read runtime bound (transfer read runtime bound value) + residual read runtime bound value) -
          pullback read runtime bound (decoderValue read runtime bound decoder) := by abel
      _ = _ := congrArg (fun current => current - pullback read runtime bound (decoderValue read runtime bound decoder))
        (pullback_transfer_add_residual read runtime bound value)
  have energy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (pullback read runtime bound (transfer read runtime bound value - decoderValue read runtime bound decoder))
    (residual read runtime bound value) (residual_decoder_orthogonal read runtime bound value decoder)
  rw [reconstructed, pullback_norm] at energy
  simpa only [sq] using energy.trans (add_comm _ _)

theorem residual_lower_bound (value : Space read runtime bound) (decoder : Field read → ℂ) :
    ‖residual read runtime bound value‖ ^ 2 ≤ sourceError read runtime bound value decoder := by
  rw [error_decomposition, decoderError_eq_norm]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem transfer_attains (value : Space read runtime bound) :
    sourceError read runtime bound value (fun atom => transfer read runtime bound value atom) =
      ‖residual read runtime bound value‖ ^ 2 := by
  rw [error_decomposition]
  simp [decoderError]

end
end SourceConditionalRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
