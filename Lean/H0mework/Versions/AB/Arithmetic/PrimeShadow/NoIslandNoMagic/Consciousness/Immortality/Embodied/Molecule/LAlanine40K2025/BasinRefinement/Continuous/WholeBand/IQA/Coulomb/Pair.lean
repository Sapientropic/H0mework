import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Source
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.SourceCoulomb
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource MeasureTheory Set Metric
noncomputable section

def nearKernel : Point → ℝ := (ball (0 : Point) 1).indicator kernel
def farKernel : Point → ℝ := (ball (0 : Point) 1)ᶜ.indicator kernel

theorem near_integrable : Integrable nearKernel :=
  (kernel_ball_integrable 1).integrable_indicator measurableSet_ball

theorem near_measurable : Measurable nearKernel := kernel_measurable.indicator measurableSet_ball
theorem far_measurable : Measurable farKernel := kernel_measurable.indicator measurableSet_ball.compl

theorem far_bound (x : Point) : ‖farKernel x‖ ≤ 1 := by
  by_cases hx : x ∈ ball (0 : Point) 1
  · simp [farKernel,hx]
  · simpa only [farKernel,indicator_of_mem (show x ∈ (ball (0 : Point) 1)ᶜ from hx),Real.norm_eq_abs,abs_of_nonneg (kernel_nonnegative x)]
      using kernel_le_one_outside x hx

theorem kernel_parts (x : Point) : nearKernel x + farKernel x = kernel x := by
  by_cases h : x ∈ ball (0 : Point) 1 <;> simp [nearKernel,farKernel,h]

/-- The six-dimensional diagonal singularity is paid by a measure-preserving difference coordinate. -/
theorem pair_integrable (f g : Point → ℝ) (hf : Integrable f) (hg : Integrable g)
    (M : ℝ) (bounded : ∀ y, ‖g y‖ ≤ M) :
    Integrable (fun z : Point × Point => f z.1 * g z.2 * kernel (z.2-z.1)) := by
  have nearBase : Integrable (fun z : Point × Point => f z.1 * nearKernel (z.2-z.1)) :=
    (measurePreserving_prod_sub (volume : Measure Point) (volume : Measure Point)).integrable_comp_of_integrable
      (hf.mul_prod near_integrable)
  have near : Integrable (fun z : Point × Point => f z.1 * g z.2 * nearKernel (z.2-z.1)) := by
    convert nearBase.mul_bdd hg.aestronglyMeasurable.comp_snd (Filter.Eventually.of_forall (fun z => bounded z.2)) using 1
    funext z
    ring
  have far : Integrable (fun z : Point × Point => f z.1 * g z.2 * farKernel (z.2-z.1)) :=
    (hf.mul_prod hg).mul_bdd
      (far_measurable.comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => far_bound (z.2-z.1)))
  convert! near.add far using 1
  funext z
  simp only [Pi.add_apply]
  rw [← mul_add,kernel_parts]

theorem source_bilinear_pair_coulomb_integrable (l r l' r' : MultiIndex) :
    Integrable (fun z : Point × Point =>
      bilinear sourceTerms densityMatrix l r z.1 * bilinear sourceTerms densityMatrix l' r' z.2 *
        kernel (z.2-z.1)) :=
  pair_integrable _ _ (source_bilinear_integrable l r) (source_bilinear_integrable l' r')
    (GlobalSource.sourceBilinearBound l' r') (source_bilinear_uniform_bound l' r')

theorem source_hartree_integrable :
    Integrable (fun z : Point × Point => sourceDensity z.1 * sourceDensity z.2 * kernel (z.2-z.1)) :=
  source_bilinear_pair_coulomb_integrable zeroJet zeroJet zeroJet zeroJet

end
end LAlanine40K2025.BasinRefinement.SourceCoulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
