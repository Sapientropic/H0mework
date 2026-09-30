import H0mework.Versions.X.Fock.CopyGraph.DecoderComparison
import H0mework.Versions.X.Fock.CopyGraph.DecoderClock

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceGeneratedJointClock
open SourceCopyObservation SourceConditionalGraph
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open scoped InnerProductSpace
noncomputable section
local instance effectParentMeasurable : MeasurableSpace ParentCarrier := ⊤

local notation "clockValue" => taskValue (historyPMF 3) (signal 3)

theorem old_conditional_not_decoder :
    transfer (historyPMF 3) (before 3 3) clockValue ≠
      decode 3 3 twoMaterial (before 3 3) (copyRead 3 3 twoMaterial clockValue) := by
  intro same
  have rebuilt := reconstruction 3 3 twoMaterial (before 3 3) (copyRead 3 3 twoMaterial clockValue)
  rw [← same, action_source] at rebuilt
  have original := congrArg (copyRead 3 3 twoMaterial)
    (IsometricRetainedTransfer.pullback_transfer_add_residual (pullback (historyPMF 3) (before 3 3)) clockValue)
  rw [map_add] at original
  have retained : residual 3 3 twoMaterial (before 3 3) (copyRead 3 3 twoMaterial clockValue) =
      copyRead 3 3 twoMaterial (SourceWeightedRecovery.residual (historyPMF 3) (before 3 3) clockValue) :=
    add_left_cancel (rebuilt.trans original.symm)
  have normal := source_orthogonal 3 3 twoMaterial (before 3 3) (copyRead 3 3 twoMaterial clockValue)
    (transfer (historyPMF 3) (before 3 3) clockValue)
  rw [retained, conditional_inner] at normal
  have conjugate : starRingEnd ℂ (SourceClockComplex.clock (SourceHistoryWord.word 3
      (pullback (historyPMF 3) (before 3 3) (transfer (historyPMF 3) (before 3 3) clockValue)))) ≠ 0 := by
    simpa only [starRingEnd_apply, star_ne_zero] using before_prediction_clock_ne_zero
  exact (mul_ne_zero (pow_ne_zero 2 (SourceCopyGraph.scale_nonzero 3 twoMaterial))
    (mul_ne_zero conjugate SourceConditionalGraph.before_residual_clock_ne_zero)) normal

theorem strict_clock_improvement :
    ‖residual 3 3 twoMaterial (before 3 3) (copyRead 3 3 twoMaterial clockValue)‖ ^ 2 <
      ‖copyRead 3 3 twoMaterial (SourceWeightedRecovery.residual (historyPMF 3) (before 3 3) clockValue)‖ ^ 2 := by
  have generated := conditional_gain 3 3 twoMaterial (before 3 3) clockValue
  have different : decode 3 3 twoMaterial (before 3 3) (copyRead 3 3 twoMaterial clockValue) -
      transfer (historyPMF 3) (before 3 3) clockValue ≠ 0 :=
    fun zero => old_conditional_not_decoder (sub_eq_zero.mp zero).symm
  have nonzero : action 3 3 twoMaterial (before 3 3)
      (decode 3 3 twoMaterial (before 3 3) (copyRead 3 3 twoMaterial clockValue) -
        transfer (historyPMF 3) (before 3 3) clockValue) ≠ 0 := by
    intro zero
    exact different (source_injective 3 3 twoMaterial (before 3 3) (zero.trans (map_zero _).symm))
  have paid := sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  linarith only [generated, paid]

theorem before_minimum_positive :
    0 < ‖residual 3 3 twoMaterial (before 3 3) (copyRead 3 3 twoMaterial clockValue)‖ ^ 2 := by
  have lower := retained_lower 3 3 twoMaterial (before 3 3) clockValue
  exact (sq_pos_of_pos (norm_pos_iff.mpr SourceConditionalGraph.before_clock_residual_ne_zero)).trans_le lower

theorem after_minimum_zero (value : Space (historyPMF 3)) :
    residual 3 3 twoMaterial (after 3 3 twoMaterial) (copyRead 3 3 twoMaterial value) = 0 :=
  (recovery_zero_iff 3 3 twoMaterial (after 3 3 twoMaterial) value).mpr (after_residual_zero value)

theorem after_decode_original (value : Space (historyPMF 3)) :
    decode 3 3 twoMaterial (after 3 3 twoMaterial) (copyRead 3 3 twoMaterial value) =
      transfer (historyPMF 3) (after 3 3 twoMaterial) value := by
  apply Eq.symm
  apply (minimum_fibre 3 3 twoMaterial (after 3 3 twoMaterial) (copyRead 3 3 twoMaterial value)
    (transfer (historyPMF 3) (after 3 3 twoMaterial) value)).mp
  rw [after_minimum_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), action_source]
  exact SourceConditionalGraph.after_graph_error_zero value

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
