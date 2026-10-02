import H0mework.Versions.R2.Physics.MotherProgrammesFormationDiscrete.History
import H0mework.Physics.MotherSource.Contact

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceMaterialEffects

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StandardModelConstraint
open scoped Matrix.Norms.Elementwise

noncomputable section

def axis (direction : LorentzianIndex) (time : ℝ) : BasePoint :=
  time • EuclideanSpace.single direction 1

theorem axis_zero (direction : LorentzianIndex) : axis direction 0 = 0 := by
  simp [axis]

theorem axis_continuous (direction : LorentzianIndex) : Continuous (axis direction) := by
  unfold axis
  fun_prop

theorem coframe_axis (source : SmoothUnifiedSource) (direction row column : LorentzianIndex)
    (time : ℝ) :
    source.legacy.coframeAt (axis direction time) row column =
      (1 : LorentzianCoframe) row column +
        source.stageEight.coframeLinearCoefficient direction row column * time := by
  simp [ProofFreeRicherAnholonomicSource.Source.coframeAt, axis, PiLp.single_apply,
    SmoothUnifiedSource.legacy, SmoothUnifiedSource.forget, StageEightProofFreeSource.Source.toPhysicalSource, mul_ite]

theorem coframe_derivative (source : SmoothUnifiedSource) (direction row column : LorentzianIndex)
    (time : ℝ) :
    HasDerivAt (fun t => source.legacy.coframeAt (axis direction t) row column)
      (source.stageEight.coframeLinearCoefficient direction row column) time := by
  simp_rw [coframe_axis]
  simpa using ((hasDerivAt_id time).const_mul
    (source.stageEight.coframeLinearCoefficient direction row column)).const_add
      ((1 : LorentzianCoframe) row column)

theorem derivative_readback (source : SmoothUnifiedSource) (direction row column : LorentzianIndex)
    (time : ℝ) :
    deriv (fun t => source.legacy.coframeAt (axis direction t) row column) time =
      source.stageEight.coframeLinearCoefficient direction row column :=
  (coframe_derivative source direction row column time).deriv

theorem coframe_nondegenerate_near_origin (source : SmoothUnifiedSource)
    (direction : LorentzianIndex) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ time : ℝ, |time| < radius →
      Matrix.det (source.legacy.coframeAt (axis direction time)) ≠ 0 := by
  have continuous : Continuous (fun time =>
      Matrix.det (source.legacy.coframeAt (axis direction time))) :=
    (source.legacy.coframeAt_contDiff.continuous.comp (axis_continuous direction)).matrix_det
  have nonzero : Matrix.det (source.legacy.coframeAt (axis direction 0)) ≠ 0 := by
    rw [axis_zero, source.legacy.coframeAt_zero]
    simp
  have nearby := continuous.continuousAt.eventually_ne nonzero
  obtain ⟨radius, positive, within⟩ := Metric.eventually_nhds_iff.mp nearby
  exact ⟨radius, positive, fun time close => within (by simpa [Real.dist_eq] using close)⟩

theorem different_coframe_has_legal_effect (first last : SmoothUnifiedSource)
    (direction row column : LorentzianIndex)
    (different : first.stageEight.coframeLinearCoefficient direction row column ≠
      last.stageEight.coframeLinearCoefficient direction row column) :
    ∃ point : BasePoint,
      Matrix.det (first.legacy.coframeAt point) ≠ 0 ∧
      Matrix.det (last.legacy.coframeAt point) ≠ 0 ∧
      first.legacy.coframeAt point row column ≠ last.legacy.coframeAt point row column := by
  obtain ⟨a, apos, firstWithin⟩ := coframe_nondegenerate_near_origin first direction
  obtain ⟨b, bpos, lastWithin⟩ := coframe_nondegenerate_near_origin last direction
  let time := min a b / 2
  have positive : 0 < time := by dsimp [time]; positivity
  have lessA : |time| < a := by rw [abs_of_pos positive]; dsimp [time]; have := min_le_left a b; linarith
  have lessB : |time| < b := by rw [abs_of_pos positive]; dsimp [time]; have := min_le_right a b; linarith
  refine ⟨axis direction time, firstWithin time lessA, lastWithin time lessB, ?_⟩
  rw [coframe_axis, coframe_axis]
  intro same
  exact different (mul_right_cancel₀ (ne_of_gt positive) (add_left_cancel same))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceMaterialEffects
