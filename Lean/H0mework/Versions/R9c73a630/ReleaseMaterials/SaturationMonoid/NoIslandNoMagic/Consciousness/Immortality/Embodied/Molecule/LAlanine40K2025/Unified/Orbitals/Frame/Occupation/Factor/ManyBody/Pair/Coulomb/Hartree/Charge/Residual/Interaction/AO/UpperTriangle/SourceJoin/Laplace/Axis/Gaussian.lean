import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Prod
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Algebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open MeasureTheory
noncomputable section

theorem shifted_gaussian_integral (b c : ℝ) :
    (∫ x : ℝ, Real.exp (-b * (x-c)^2)) =
      Real.sqrt (Real.pi / b) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) (-c)).integral_comp
    (MeasurableEquiv.addRight (-c)).measurableEmbedding
    (fun x : ℝ => Real.exp (-b * x^2))
  simpa only [sub_eq_add_neg] using h.trans (integral_gaussian b)

theorem two_gaussian_integral (alpha beta left right : ℝ)
    (ha : 0 < alpha) (hb : 0 < beta) :
    (∫ x : ℝ, Real.exp (-alpha * (x-left)^2) *
      Real.exp (-beta * (x-right)^2)) =
        Real.exp (-(alpha * beta / (alpha+beta) * (left-right)^2)) *
          Real.sqrt (Real.pi / (alpha+beta)) := by
  have hsum : alpha + beta ≠ 0 := ne_of_gt (add_pos ha hb)
  simp_rw [exponential_product alpha beta left right _ hsum]
  rw [integral_const_mul,shifted_gaussian_integral]

theorem shifted_gaussian_integrable (b c : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-b*(x-c)^2)) := by
  have h := ((measurePreserving_add_right (volume : Measure ℝ) (-c)).integrable_comp_emb
    (MeasurableEquiv.addRight (-c)).measurableEmbedding).mpr
      (integrable_exp_neg_mul_sq hb)
  simpa only [Function.comp_def,sub_eq_add_neg] using h


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
