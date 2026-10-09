import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.Transport

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
open SourceGaussianModel GlobalSource GlobalSource.Differential Set MeasureTheory
open _root_.LAlanineTrueFlowDifferential
noncomputable section

def travelRadius : ℝ := spatialStep*(GlobalSource.sourceSpeedBound : ℝ)/2

theorem short_displacement (x : Point) (t : Time) : dist (flow x (spatialStep*(t : ℝ))) x ≤ travelRadius := by
  have bound := flow_displacement x (spatialStep*(t : ℝ))
  rw [abs_mul,abs_of_pos spatialStep_positive] at bound
  calc
    _ ≤ (GlobalSource.sourceSpeedBound : ℝ)*(spatialStep*|(t : ℝ)|) := bound
    _ ≤ (GlobalSource.sourceSpeedBound : ℝ)*(spatialStep*(1/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_le.mpr t.property) spatialStep_positive.le) (by positivity)
    _ = _ := by unfold travelRadius; ring

theorem short_outside (R : ℝ) (x : Point) (t : Time) (outside : R+travelRadius < ‖x‖) :
    R < ‖flow x (spatialStep*(t : ℝ))‖ := by
  have triangle : ‖x‖ ≤ ‖flow x (spatialStep*(t : ℝ))‖+dist (flow x (spatialStep*(t : ℝ))) x := by
    have bound := norm_le_norm_add_norm_sub (flow x (spatialStep*(t : ℝ))) x
    simpa only [dist_eq_norm,norm_sub_rev] using bound
  linarith [short_displacement x t]

def dominating (R A B : ℝ) : Point → ℝ :=
  (Metric.closedBall (0 : Point) (R+travelRadius)).indicator
    (fun _ => 144*A+48*B*(spatialStep*(GlobalSource.sourceSpeedBound : ℝ)))

theorem dominating_integrable (R A B : ℝ) : Integrable (dominating R A B) :=
  (integrableOn_const (isCompact_closedBall (0 : Point) (R+travelRadius)).measure_ne_top).integrable_indicator Metric.isClosed_closedBall.measurableSet

theorem original_domination (test : Test) (R A B : ℝ) (apos : 0 ≤ A) (bpos : 0 ≤ B)
    (value : ∀ x, ‖test.value x‖ ≤ A) (derivative : ∀ x, ‖test.derivative x‖ ≤ B)
    (outside : ∀ x, R < ‖x‖ → test.value x = 0 ∧ test.derivative x = 0)
    (x : Point) (t : Time) : ‖pullDerivative test t x‖ ≤ dominating R A B x := by
  by_cases member : x ∈ Metric.closedBall (0 : Point) (R+travelRadius)
  · rw [dominating,indicator_of_mem member]
    exact pullDerivative_bound test A B apos bpos value derivative x t
  · have hx : R+travelRadius < ‖x‖ := by
      simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using member
    have zero := outside _ (short_outside R x t hx)
    simp only [pullDerivative,zero.1,zero.2,_root_.zero_apply,mul_zero,add_zero,norm_zero,
      dominating,indicator_of_notMem member,le_refl]

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
