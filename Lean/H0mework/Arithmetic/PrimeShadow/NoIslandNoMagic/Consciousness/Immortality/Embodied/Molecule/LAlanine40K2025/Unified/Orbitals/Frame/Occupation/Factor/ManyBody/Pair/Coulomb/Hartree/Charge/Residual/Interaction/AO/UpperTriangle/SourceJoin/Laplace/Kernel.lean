import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Kernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceCoulomb MeasureTheory Set
noncomputable section

private theorem laplace_inverse_radius (r : ℝ) (hr : 0 ≤ r) :
    r⁻¹ = (2 / Real.sqrt Real.pi) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(r^2) * t^2) := by
  rw [integral_gaussian_Ioi]
  by_cases hz : r = 0
  · subst r
    simp
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hpi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hrp]
    field_simp

theorem kernel_laplace (x : Point) :
    kernel x = (2 / Real.sqrt Real.pi) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(distance x)^2 * t^2) := by
  exact laplace_inverse_radius (distance x) (distance_nonnegative x)

theorem volume_point_singleton (x : Point) :
    (volume : Measure Point) ({x} : Set Point) = 0 := by simp

theorem product_diagonal_null :
    (volume : Measure (Point × Point)) (diagonal Point) = 0 := by
  have h : (volume : Measure Point).prod (volume : Measure Point) (diagonal Point) = 0 := by
    rw [Measure.measure_prod_null measurableSet_diagonal]
    filter_upwards [] with x
    simp [Set.diagonal]
  simpa only [Measure.volume_eq_prod] using h

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
