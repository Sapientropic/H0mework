import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalIntegral
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousChart

open SourceGaussianModel Set

/-- The existing convex mean-value theorem rules out folds after source preconditioning. -/
theorem injOn_of_derivative_near_identity (f : Point → Point) (derivative : Point → Point →L[ℝ] Point)
    (domain : Set Point) (convex : Convex ℝ domain) (constant : ℝ) (small : constant < 1)
    (differentiates : ∀ x ∈ domain, HasFDerivAt f (derivative x) x)
    (bound : ∀ x ∈ domain, ‖derivative x - ContinuousLinearMap.id ℝ Point‖ ≤ constant) :
    InjOn f domain := by
  intro x hx y hy same
  have estimate := convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx => (differentiates x hx).hasFDerivWithinAt) bound hx hy
  have distance : ‖y - x‖ ≤ constant * ‖y - x‖ := by
    simpa only [same, sub_self, ContinuousLinearMap.id_apply, zero_sub, norm_neg] using estimate
  have : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousChart
