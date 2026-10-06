import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Kernel
import H0mework.Versions.AB.Chemistry.LAlanineBandGlobalSource.Integrability

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.SourceCoulomb
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource MeasureTheory Set Metric
noncomputable section

/-- Local Coulomb integrability and the original L1 tail pay different parts of the same space. -/
theorem integrable_mul_kernel (f : Point → ℝ) (integrable : Integrable f)
    (M : ℝ) (bounded : ∀ x, ‖f x‖ ≤ M) : Integrable (fun x => f x * kernel x) := by
  have near : IntegrableOn (fun x => f x * kernel x) (ball (0 : Point) 1) :=
    (kernel_ball_integrable 1).bdd_mul integrable.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall bounded)
  have far : IntegrableOn (fun x => f x * kernel x) (ball (0 : Point) 1)ᶜ := by
    apply integrable.integrableOn.mul_bdd kernel_measurable.aestronglyMeasurable.restrict (c := 1)
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (kernel_nonnegative x)] using kernel_le_one_outside x hx
  simpa only [union_compl_self,integrableOn_univ] using near.union far

theorem integrable_mul_shifted_kernel (f : Point → ℝ) (integrable : Integrable f)
    (M : ℝ) (bounded : ∀ x, ‖f x‖ ≤ M) (centre : Point) :
    Integrable (fun x => f x * kernel (x-centre)) := by
  have shifted := integrable_mul_kernel (fun x => f (x+centre)) (integrable.comp_add_right centre)
    M (fun x => bounded (x+centre))
  simpa only [sub_add_cancel] using shifted.comp_sub_right centre

theorem source_bilinear_coulomb_integrable (left right : MultiIndex) (centre : Point) :
    Integrable (fun x => bilinear sourceTerms densityMatrix left right x * kernel (x-centre)) :=
  integrable_mul_shifted_kernel _ (source_bilinear_integrable left right)
    (GlobalSource.sourceBilinearBound left right) (source_bilinear_uniform_bound left right) centre

theorem source_density_coulomb_integrable (centre : Point) :
    Integrable (fun x => sourceDensity x * kernel (x-centre)) :=
  source_bilinear_coulomb_integrable zeroJet zeroJet centre

/-- Every nuclear charge multiplies the same original density, with the singularity already paid. -/
theorem source_electron_nuclear_integrable (centre : Point) (charge : ℝ) :
    Integrable (fun x => -charge * (sourceDensity x * kernel (x-centre))) :=
  (source_density_coulomb_integrable centre).const_mul (-charge)

end
end LAlanine40K2025.BasinRefinement.SourceCoulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
