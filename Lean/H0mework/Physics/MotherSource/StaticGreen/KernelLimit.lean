import H0mework.Physics.MotherSource.StaticGreen.HeatPairing
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Kernel

/-! The Gaussian parameter primitive and its locally integrable representative, with the singular point handled almost everywhere. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Filter Set Metric
open scoped Topology SchwartzMap
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
open UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
noncomputable section

def heatPrimitive (point : Point) : ℝ := ∫ parameter in Ioi (0 : ℝ), spatialHeat parameter point

def truncatedHeat (upper : ℝ) (point : Point) : ℝ :=
  ∫ parameter in 0..upper, spatialHeat parameter point

theorem parameter_form (point : Point) :
    (fun t => spatialHeat t point) = fun t => Real.exp (-(distance point)^2*t^2) := by
  funext t
  unfold spatialHeat
  congr 1
  ring

theorem heatPrimitive_kernel (point : Point) : heatPrimitive point = Real.sqrt Real.pi/2*kernel point := by
  have original := kernel_laplace point
  have squareRoot : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  unfold heatPrimitive
  rw [parameter_form]
  rw [original]
  field_simp

theorem parameter_integrable (point : Point) (nonzero : point ≠ 0) :
    IntegrableOn (fun t => spatialHeat t point) (Ioi (0 : ℝ)) := by
  rw [parameter_form]
  have positive : 0 < distance point := (norm_pos_iff.mpr nonzero).trans_le (pi_norm_le_distance point)
  exact (integrable_exp_neg_mul_sq (sq_pos_of_pos positive)).integrableOn

theorem kernel_mul_integrable (test : 𝓢(Point, ℝ)) :
    Integrable (fun point => kernel point*test point) := by
  have localIntegral : Integrable ((ball (0 : Point) 1).indicator kernel) :=
    (integrable_indicator_iff measurableSet_ball).mpr (kernel_ball_integrable 1)
  have majorant := (localIntegral.const_mul (SchwartzMap.seminorm ℝ 0 0 test)).add test.integrable.norm
  apply majorant.mono' (kernel_measurable.aestronglyMeasurable.mul test.continuous.aestronglyMeasurable)
  filter_upwards [] with point
  change ‖kernel point*test point‖ ≤
    SchwartzMap.seminorm ℝ 0 0 test*(ball (0 : Point) 1).indicator kernel point+‖test point‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonnegative point)]
  by_cases inside : point ∈ ball (0 : Point) 1
  · rw [indicator_of_mem inside]
    have bound := mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ test point)
      (kernel_nonnegative point)
    nlinarith [norm_nonneg (test point)]
  · rw [indicator_of_notMem inside]
    simp only [mul_zero, zero_add]
    exact mul_le_of_le_one_left (norm_nonneg _) (kernel_le_one_outside point inside)

theorem truncatedHeat_nonnegative (upper : ℝ) (nonnegative : 0 ≤ upper) (point : Point) :
    0 ≤ truncatedHeat upper point :=
  intervalIntegral.integral_nonneg_of_forall nonnegative
    (fun t => (spatialHeat_positive t point).le)

theorem truncatedHeat_le (upper : ℝ) (nonnegative : 0 ≤ upper)
    (point : Point) (nonzero : point ≠ 0) : truncatedHeat upper point ≤ heatPrimitive point := by
  rw [truncatedHeat, intervalIntegral.integral_of_le nonnegative, heatPrimitive]
  apply setIntegral_mono_set (parameter_integrable point nonzero)
    (Eventually.of_forall (fun t => (spatialHeat_positive t point).le))
  exact Eventually.of_forall (fun _ membership => membership.1)

theorem truncatedHeat_tendsto (point : Point) (nonzero : point ≠ 0) :
    Tendsto (fun upper => truncatedHeat upper point) atTop (𝓝 (heatPrimitive point)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (parameter_integrable point nonzero) tendsto_id

theorem truncatedHeat_measurable (upper : ℝ) (nonnegative : 0 ≤ upper) :
    StronglyMeasurable (truncatedHeat upper) := by
  have joint : Continuous (fun pair : Point × ℝ => spatialHeat pair.2 pair.1) := by
    unfold spatialHeat
    exact ((continuous_snd.pow 2).neg.mul ((distance_continuous.comp continuous_fst).pow 2)).rexp
  have result := joint.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) upper))
  unfold truncatedHeat
  simpa only [intervalIntegral.integral_of_le nonnegative] using result

theorem heatPrimitive_norm_test_integrable (test : 𝓢(Point, ℝ)) :
    Integrable (fun point => heatPrimitive point*‖test point‖) := by
  have result := (kernel_mul_integrable test).norm.const_mul (Real.sqrt Real.pi/2)
  convert result using 1
  funext point
  rw [heatPrimitive_kernel]
  simp only [norm_mul, Real.norm_eq_abs (kernel point), abs_of_nonneg (kernel_nonnegative point)]
  ring

theorem truncated_pairing_tendsto (test : 𝓢(Point, ℝ)) :
    Tendsto (fun upper => ∫ point : Point, truncatedHeat upper point*test point) atTop
      (𝓝 (∫ point : Point, heatPrimitive point*test point)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun point => heatPrimitive point*‖test point‖)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with upper nonnegative
    exact ((truncatedHeat_measurable upper nonnegative).mul test.continuous.stronglyMeasurable).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with upper nonnegative
    filter_upwards [(volume : Measure Point).ae_ne 0] with point nonzero
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (truncatedHeat_nonnegative upper nonnegative point)]
    exact mul_le_mul_of_nonneg_right (truncatedHeat_le upper nonnegative point nonzero) (norm_nonneg _)
  · exact heatPrimitive_norm_test_integrable test
  · filter_upwards [(volume : Measure Point).ae_ne 0] with point nonzero
    exact (truncatedHeat_tendsto point nonzero).mul_const (test point)

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
