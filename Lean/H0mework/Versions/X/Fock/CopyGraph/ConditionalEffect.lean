import H0mework.Versions.X.Fock.CopyGraph.ConditionalGeometry
import H0mework.Versions.X.Fock.HistoryCopy.ObservationRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceGeneratedJointClock SourceCopyObservation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open scoped InnerProductSpace
noncomputable section

local instance effectParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem before_clock_residual_ne_zero :
    residual (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3)) ≠ 0 := by
  intro vanished
  have reconstructed := IsometricRetainedTransfer.pullback_transfer_add_residual
    (pullback (historyPMF 3) (before 3 3)) (taskValue (historyPMF 3) (signal 3))
  rw [vanished, add_zero] at reconstructed
  have decoded (actor : Fin 4) :
      signal 3 actor = transfer (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3)) (before 3 3 actor) := by
    have sample := congrArg (fun value : Space (historyPMF 3) => value actor) reconstructed.symm
    rw [taskValue_at _ _ actor (source_positive 3 actor), pullback_at _ _ _ actor (source_positive 3 actor)] at sample
    exact sample
  have same := (decoded 2).trans ((congrArg
    (transfer (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3))) original_snapshot_collision).trans (decoded 3).symm)
  rw [signal_value, signal_value] at same
  norm_num at same

theorem before_residual_clock_ne_zero :
    SourceClockComplex.clock (SourceHistoryWord.word 3
      (residual (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3)))) ≠ 0 := by
  intro vanished
  have paid := residual_clock 3 (before 3 3) (taskValue (historyPMF 3) (signal 3))
  have realPart := congrArg Complex.re paid
  rw [vanished, Complex.zero_re, Complex.smul_re] at realPart
  have self : (inner ℂ
      (residual (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3)))
      (residual (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3)))).re =
        ‖residual (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3))‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [self] at realPart
  have size := norm_pos_iff.mpr before_clock_residual_ne_zero
  have positive : 0 < Real.sqrt (3 + 1 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have impossible := mul_pos positive (sq_pos_of_pos size)
  change 0 = Real.sqrt (3 + 1 : ℝ) * _ at realPart
  linarith

theorem before_graph_cost_strict :
    ‖residual (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3))‖ ^ 2 <
      ‖copyRead 3 3 twoMaterial (residual (historyPMF 3) (before 3 3)
        (taskValue (historyPMF 3) (signal 3)))‖ ^ 2 := by
  rw [residual_graph_energy]
  have scalePositive : (0 : ℝ) < SourceCopyProgram.scale 3 twoMaterial := by
    exact_mod_cast SourceCopyProgram.scale_pos 3 twoMaterial
  exact lt_add_of_pos_right _ (mul_pos (sq_pos_of_pos scalePositive)
    (sq_pos_of_pos (norm_pos_iff.mpr before_residual_clock_ne_zero)))

theorem after_graph_recovery (value : Space (historyPMF 3)) :
    copyRead 3 3 twoMaterial (pullback (historyPMF 3) (after 3 3 twoMaterial)
      (transfer (historyPMF 3) (after 3 3 twoMaterial) value)) = copyRead 3 3 twoMaterial value := by
  have original := IsometricRetainedTransfer.pullback_transfer_add_residual
    (pullback (historyPMF 3) (after 3 3 twoMaterial)) value
  rw [after_residual_zero, add_zero] at original
  exact congrArg (copyRead 3 3 twoMaterial) original

theorem after_graph_error_zero (value : Space (historyPMF 3)) :
    ‖copyRead 3 3 twoMaterial value - copyRead 3 3 twoMaterial
      (pullback (historyPMF 3) (after 3 3 twoMaterial) (transfer (historyPMF 3) (after 3 3 twoMaterial) value))‖ ^ 2 = 0 := by
  rw [after_graph_recovery, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]

end
end SourceConditionalGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
