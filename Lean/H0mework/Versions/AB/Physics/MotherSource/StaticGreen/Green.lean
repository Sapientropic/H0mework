import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Poisson
import H0mework.Physics.MotherSource.StaticGreen.Cutoff

/-! The original Gauss coefficient and Gaussian mass generate a Green kernel; its fundamental equation precedes the Coulomb readout. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Filter
open scoped Topology SchwartzMap
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
open Stage9C.Material.SpinPair
noncomputable section

theorem heatPrimitive_fundamental (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, heatPrimitive point*(-testLaplacian test point)) =
      2*(Real.sqrt Real.pi)^3*test 0 := by
  have left := truncated_pairing_tendsto (-testLaplacian test)
  have right := (scaled_heat_pairing_tendsto test).const_mul 2
  have same : (fun upper => 2*(∫ point : Point, upper^3*spatialHeat upper point*test point)) =ᶠ[atTop]
      fun upper => ∫ point : Point, truncatedHeat upper point*(-testLaplacian test point) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with upper nonnegative
    exact (cutoff_pairing upper nonnegative test).symm
  have unique := tendsto_nhds_unique left (right.congr' same)
  simpa only [neg_apply, mul_assoc] using unique

/-- Integral of the source-coordinate Gaussian, normalized by its generated mass and original Gauss coefficient. -/
def green (point : Point) : ℝ :=
  (4*lapse*(Real.sqrt Real.pi)^3)⁻¹*heatPrimitive point

theorem green_fundamental (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, green point*(-(2*lapse)*testLaplacian test point)) = test 0 := by
  have integrand (point : Point) : green point*(-(2*lapse)*testLaplacian test point) =
      ((4*lapse*(Real.sqrt Real.pi)^3)⁻¹*(2*lapse)) *
        (heatPrimitive point*(-testLaplacian test point)) := by
    unfold green
    ring
  simp_rw [integrand]
  rw [integral_const_mul, heatPrimitive_fundamental]
  have positive : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp [lapse_pos.ne', positive.ne']
  ring

theorem green_kernel (point : Point) : green point = kernel point/(8*Real.pi*lapse) := by
  rw [green, heatPrimitive_kernel]
  have positive : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have square : (Real.sqrt Real.pi)^2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  field_simp [lapse_pos.ne', positive.ne', Real.pi_pos.ne']
  rw [square]
  ring

theorem green_nonnegative (point : Point) : 0 ≤ green point := by
  rw [green_kernel]
  exact div_nonneg (kernel_nonnegative point)
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) lapse_pos.le)

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
