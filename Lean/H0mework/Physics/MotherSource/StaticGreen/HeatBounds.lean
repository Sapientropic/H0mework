import H0mework.Physics.MotherSource.StaticGreen.SpatialHeat

/-! Weighted integrability for the actual Gaussian derivatives, generated from Schwartz decay. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Filter
open scoped SchwartzMap LineDeriv
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
noncomputable section

theorem spatialHeat_le_one (parameter : ℝ) (point : Point) : spatialHeat parameter point ≤ 1 := by
  rw [spatialHeat, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg parameter)) (sq_nonneg _)

theorem weighted_mul_integrable (coefficient : Point → ℝ) (continuous : Continuous coefficient)
    (constant quadratic : ℝ) (bound : ∀ point, ‖coefficient point‖ ≤ constant+quadratic*‖point‖^2)
    (test : 𝓢(Point, ℝ)) : Integrable (fun point => coefficient point*test point) := by
  have majorant := (test.integrable.norm.const_mul constant).add
    ((test.integrable_pow_mul volume 2).const_mul quadratic)
  apply majorant.mono' (continuous.mul test.continuous).aestronglyMeasurable
  filter_upwards [] with point
  calc
    ‖coefficient point*test point‖ = ‖coefficient point‖*‖test point‖ := norm_mul _ _
    _ ≤ (constant+quadratic*‖point‖^2)*‖test point‖ :=
      mul_le_mul_of_nonneg_right (bound point) (norm_nonneg _)
    _ = constant*‖test point‖+quadratic*(‖point‖^2*‖test point‖) := by ring

theorem heatFirst_bound (parameter : ℝ) (point : Point) (index : Fin 3) :
    ‖heatFirst parameter index point‖ ≤ parameter^2+parameter^2*‖point‖^2 := by
  have product := mul_le_mul (norm_le_pi_norm point index) (spatialHeat_le_one parameter point)
    (spatialHeat_positive parameter point).le (norm_nonneg point)
  have multiplied := mul_le_mul_of_nonneg_left product (show 0 ≤ 2*parameter^2 by positivity)
  calc
    ‖heatFirst parameter index point‖ = 2*parameter^2*(‖point index‖*spatialHeat parameter point) := by
      simp [heatFirst, norm_mul, Real.norm_eq_abs, abs_of_pos (spatialHeat_positive parameter point)]
      ring
    _ ≤ 2*parameter^2*‖point‖ := by simpa only [mul_one] using multiplied
    _ ≤ parameter^2+parameter^2*‖point‖^2 := by
      nlinarith [mul_nonneg (sq_nonneg parameter) (sq_nonneg (‖point‖-1))]

theorem heatSecond_bound (parameter : ℝ) (point : Point) (index : Fin 3) :
    ‖heatSecond parameter index point‖ ≤ 2*parameter^2+4*parameter^4*‖point‖^2 := by
  have triangle : ‖4*parameter^4*(point index)^2-2*parameter^2‖ ≤
      4*parameter^4*(point index)^2+2*parameter^2 := by
    change |4*parameter^4*(point index)^2-2*parameter^2| ≤ _
    have h := abs_sub (4*parameter^4*(point index)^2) (2*parameter^2)
    rw [abs_of_nonneg (show 0 ≤ 4*parameter^4*(point index)^2 by positivity),
      abs_of_nonneg (show 0 ≤ 2*parameter^2 by positivity)] at h
    exact h
  have coordinate : (point index)^2 ≤ ‖point‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (point index)) (norm_nonneg point)).mpr (norm_le_pi_norm point index)
  calc
    ‖heatSecond parameter index point‖ =
        ‖4*parameter^4*(point index)^2-2*parameter^2‖*spatialHeat parameter point := by
      rw [heatSecond, norm_mul, Real.norm_eq_abs (spatialHeat parameter point),
        abs_of_pos (spatialHeat_positive parameter point)]
    _ ≤ (4*parameter^4*(point index)^2+2*parameter^2)*1 :=
      mul_le_mul triangle (spatialHeat_le_one parameter point)
        (spatialHeat_positive parameter point).le (by positivity)
    _ ≤ 2*parameter^2+4*parameter^4*‖point‖^2 := by
      nlinarith [mul_le_mul_of_nonneg_left coordinate (show 0 ≤ 4*parameter^4 by positivity)]

theorem spatialHeat_mul_integrable (parameter : ℝ) (test : 𝓢(Point, ℝ)) :
    Integrable (fun point => spatialHeat parameter point*test point) := by
  apply weighted_mul_integrable _ (spatialHeat_continuous parameter) 1 0 _ test
  intro point
  simpa only [zero_mul, add_zero, Real.norm_eq_abs,
    abs_of_pos (spatialHeat_positive parameter point)] using spatialHeat_le_one parameter point

theorem heatFirst_mul_integrable (parameter : ℝ) (index : Fin 3) (test : 𝓢(Point, ℝ)) :
    Integrable (fun point => heatFirst parameter index point*test point) := by
  have continuous : Continuous (heatFirst parameter index) := by
    unfold heatFirst
    exact (continuous_const.mul (continuous_apply index)).mul (spatialHeat_continuous parameter)
  exact weighted_mul_integrable _ continuous (parameter^2) (parameter^2)
    (fun point => heatFirst_bound parameter point index) test

theorem heatSecond_mul_integrable (parameter : ℝ) (index : Fin 3) (test : 𝓢(Point, ℝ)) :
    Integrable (fun point => heatSecond parameter index point*test point) := by
  have continuous : Continuous (heatSecond parameter index) := by
    unfold heatSecond
    exact ((continuous_const.mul ((continuous_apply index).pow 2)).sub continuous_const).mul
      (spatialHeat_continuous parameter)
  exact weighted_mul_integrable _ continuous (2*parameter^2) (4*parameter^4)
    (fun point => heatSecond_bound parameter point index) test

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
