import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.Domination

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource GlobalSource.Differential Set MeasureTheory Filter
open _root_.LAlanineTrueFlowDifferential
open scoped Topology
noncomputable section

theorem original_pull_integral_derivative (test : Test) :
    IntegrableOn (pullDerivative test 0) basin ∧
    HasDerivAt (fun t : ℝ => ∫ x in basin, pull test t x) (∫ x in basin, pullDerivative test 0 x) 0 := by
  obtain ⟨R,_,A,apos,B,bpos,value,derivative,outside⟩ := test.bounds
  let window := Ioo (-(1/2) : ℝ) (1/2)
  have near : window ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have measurable : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (pull test t) (volume.restrict basin) := by
    filter_upwards [near] with t inside
    exact (pull_integrable test ⟨t,inside.1.le,inside.2.le⟩).aestronglyMeasurable
  have initial : Integrable (pull test 0) (volume.restrict basin) := by
    have equality : pull test 0 = test.value := funext (pull_zero test)
    rw [equality]
    exact test.integrable.integrableOn
  have differential : Continuous (pullDerivative test 0) := by
    have equality : pullDerivative test 0 = fun x => spatialStep *
        (laplacian sourceTerms densityMatrix x*test.value x+test.derivative x (sourceGradient x)) :=
      funext (pullDerivative_zero test)
    rw [equality]
    exact continuous_const.mul (((laplacian_contDiff sourceTerms densityMatrix 0).continuous.mul test.smooth.continuous).add
      (test.derivative_continuous.clm_apply (sourceGradient_contDiff 0).continuous))
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le near measurable initial differential.aestronglyMeasurable
    (Eventually.of_forall (fun x t inside => original_domination test R A B apos bpos value derivative outside x
      ⟨t,inside.1.le,inside.2.le⟩)) (dominating_integrable R A B).integrableOn
    (Eventually.of_forall (fun x t inside => pull_derivative test x ⟨t,inside.1.le,inside.2.le⟩))

theorem original_weak_divergence (test : Test) :
    (∫ x in basin, laplacian sourceTerms densityMatrix x*test.value x+
      test.derivative x (sourceGradient x)) = 0 := by
  have actual := (original_pull_integral_derivative test).2
  have constant : (fun t : ℝ => ∫ x in basin, pull test t x) =ᶠ[𝓝 (0 : ℝ)]
      (fun _ => ∫ x in basin, test.value x) := by
    filter_upwards [Ioo_mem_nhds (show (-(1/2) : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1/2 by norm_num)] with t inside
    exact pull_integral test ⟨t,inside.1.le,inside.2.le⟩
  have zero := actual.congr_of_eventuallyEq constant.symm |>.unique
    (hasDerivAt_const 0 (∫ x in basin, test.value x))
  simp_rw [pullDerivative_zero] at zero
  rw [integral_const_mul] at zero
  exact (mul_eq_zero.mp zero).resolve_left spatialStep_positive.ne'

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
