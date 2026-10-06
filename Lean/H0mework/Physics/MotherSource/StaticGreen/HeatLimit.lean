import H0mework.Physics.MotherSource.StaticGreen.HeatMass
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! The scaled source Gaussian converges to point evaluation by an explicit change of variables and dominated convergence. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology SchwartzMap
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
noncomputable section

theorem spatialHeat_continuous (parameter : ℝ) : Continuous (spatialHeat parameter) := by
  unfold spatialHeat
  exact (continuous_const.mul (distance_continuous.pow 2)).rexp

theorem spatialHeat_positive (parameter : ℝ) (point : Point) : 0 < spatialHeat parameter point :=
  Real.exp_pos _

theorem spatialHeat_integrable (parameter : ℝ) (positive : 0 < parameter) :
    Integrable (spatialHeat parameter) := by
  apply Integrable.of_integral_ne_zero
  rw [spatialHeat_integral]
  exact ne_of_gt (by positivity)

theorem spatialHeat_scale (parameter : ℝ) (point : Point) :
    spatialHeat parameter point = spatialHeat 1 (parameter • point) := by
  rw [spatialHeat_product, spatialHeat_product]
  apply Finset.prod_congr rfl
  intro axis _
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem scaled_heat_pairing_change (parameter : ℝ) (positive : 0 < parameter) (test : Point → ℝ) :
    (∫ point : Point, parameter^3*spatialHeat parameter point*test point) =
      ∫ point : Point, spatialHeat 1 point*test (parameter⁻¹ • point) := by
  have changeVariables := integral_comp_inv_smul_of_nonneg (volume : Measure Point)
    (fun point => spatialHeat parameter point*test point) positive.le
  have read (point : Point) : spatialHeat parameter (parameter⁻¹ • point) = spatialHeat 1 point := by
    rw [spatialHeat_scale, smul_smul, mul_inv_cancel₀ positive.ne', one_smul]
  have dimension : Module.finrank ℝ Point = 3 := by simp [Point]
  rw [dimension, smul_eq_mul] at changeVariables
  simp only [read] at changeVariables
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  exact changeVariables.symm

theorem scaled_heat_pairing_tendsto_of_bounded (test : Point → ℝ) (continuous : Continuous test)
    (bound : ℝ) (bounded : ∀ point, ‖test point‖ ≤ bound) :
    Tendsto (fun parameter : ℝ => ∫ point : Point, parameter^3*spatialHeat parameter point*test point)
      atTop (𝓝 ((Real.sqrt Real.pi)^3*test 0)) := by
  have measurable (parameter : ℝ) : AEStronglyMeasurable
      (fun point : Point => spatialHeat 1 point*test (parameter⁻¹ • point)) volume := by
    have dilation : Continuous (fun point : Point => (parameter⁻¹ : ℝ) • point) :=
      continuous_const_smul _
    exact ((spatialHeat_continuous 1).mul
      (continuous.comp dilation)).aestronglyMeasurable
  have dominated (parameter : ℝ) (point : Point) :
      ‖spatialHeat 1 point*test (parameter⁻¹ • point)‖ ≤ spatialHeat 1 point*bound := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (spatialHeat_positive 1 point)]
    exact mul_le_mul_of_nonneg_left (bounded _) (spatialHeat_positive 1 point).le
  have converges (point : Point) : Tendsto
      (fun parameter : ℝ => spatialHeat 1 point*test (parameter⁻¹ • point))
      atTop (𝓝 (spatialHeat 1 point*test 0)) := by
    have argument : Tendsto (fun parameter : ℝ => parameter⁻¹ • point) atTop (𝓝 (0 : Point)) := by
      simpa only [zero_smul] using
        ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 (0 : ℝ))).smul_const point)
    exact tendsto_const_nhds.mul (continuous.continuousAt.tendsto.comp argument)
  have dominatedLimit := tendsto_integral_filter_of_dominated_convergence
    (fun point : Point => spatialHeat 1 point*bound)
    (Eventually.of_forall measurable)
    (Eventually.of_forall (fun parameter => Filter.Eventually.of_forall (dominated parameter)))
    ((spatialHeat_integrable 1 zero_lt_one).mul_const bound)
    (Filter.Eventually.of_forall converges)
  rw [integral_mul_const, spatialHeat_integral] at dominatedLimit
  simp only [one_pow, div_one] at dominatedLimit
  apply dominatedLimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with parameter positive
  exact (scaled_heat_pairing_change parameter positive test).symm

theorem scaled_heat_pairing_tendsto (test : 𝓢(Point, ℝ)) :
    Tendsto (fun parameter : ℝ => ∫ point : Point, parameter^3*spatialHeat parameter point*test point)
      atTop (𝓝 ((Real.sqrt Real.pi)^3*test 0)) :=
  scaled_heat_pairing_tendsto_of_bounded test test.continuous
    (SchwartzMap.seminorm ℝ 0 0 test) (SchwartzMap.norm_le_seminorm ℝ test)

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
