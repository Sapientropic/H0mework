import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Kernel
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The Gaussian mass on the original molecular Cartesian carrier. -/

set_option autoImplicit false
set_option maxHeartbeats 50000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
noncomputable section

def spatialHeat (parameter : ℝ) (point : Point) : ℝ :=
  Real.exp (-parameter^2 * (distance point)^2)

theorem spatialHeat_product (parameter : ℝ) (point : Point) :
    spatialHeat parameter point = ∏ axis : Fin 3, Real.exp (-parameter^2 * (point axis)^2) := by
  unfold spatialHeat distance
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (point i))),
    Finset.mul_sum, Real.exp_sum]

theorem spatialHeat_integral (parameter : ℝ) :
    (∫ point : Point, spatialHeat parameter point) = (Real.sqrt (Real.pi / parameter^2))^3 := by
  simp_rw [spatialHeat_product]
  have split : (∫ point : Point, ∏ axis : Fin 3, Real.exp (-parameter^2 * (point axis)^2)) =
      ∏ axis : Fin 3, ∫ x : ℝ, Real.exp (-parameter^2*x^2) := by
    simpa only using! integral_fin_nat_prod_volume_eq_prod
      (fun _ : Fin 3 => fun x : ℝ => Real.exp (-parameter^2*x^2))
  rw [split]
  simp only [integral_gaussian, Fin.prod_univ_three]
  ring

theorem scaled_heat_mass (parameter : ℝ) (positive : 0 < parameter) :
    (∫ point : Point, parameter^3 * spatialHeat parameter point) = (Real.sqrt Real.pi)^3 := by
  rw [integral_const_mul, spatialHeat_integral,
    Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq_eq_abs, abs_of_pos positive]
  field_simp

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
