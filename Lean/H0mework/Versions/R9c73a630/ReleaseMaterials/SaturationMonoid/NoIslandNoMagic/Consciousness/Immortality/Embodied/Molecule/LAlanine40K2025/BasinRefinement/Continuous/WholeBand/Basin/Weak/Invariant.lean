import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.ZeroFlux

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak.Invariant
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource GlobalSource.Differential Set MeasureTheory Filter
open _root_.LAlanineTrueFlowDifferential
open scoped Topology
noncomputable section

theorem flow_image (S : Set Point)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S) (t : ℝ) :
    flowHomeomorph t '' S = S := by
  ext x
  constructor
  · rintro ⟨y,inside,rfl⟩
    exact (invariant y t).mpr inside
  · intro inside
    exact ⟨flow x (-t),(invariant x (-t)).mpr inside,
      by
        change flow (flow x (-t)) t = x
        simpa only [neg_neg] using flow_inverse x (-t)⟩

theorem change_variables (S : Set Point) (measurable : MeasurableSet S)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S) (t : Time) (observable : Point → ℝ) :
    (∫ x in S, observable x) =
      ∫ x in S, (responseMatrix x t).det * observable (flow x (spatialStep*(t : ℝ))) := by
  have formula := integral_image_eq_integral_abs_det_fderiv_smul volume measurable
    (fun x _ => (original_flow_strictDerivative x t).hasFDerivAt.hasFDerivWithinAt)
    (flowHomeomorph (spatialStep*(t : ℝ))).injective.injOn observable
  change (∫ x in (flowHomeomorph (spatialStep*(t : ℝ))) '' S, observable x) = _ at formula
  rw [flow_image S invariant] at formula
  rw [formula]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [abs_of_pos (actual_determinant_positive x t)]
  change (flowDerivative x t).det * observable (flow x (spatialStep*(t : ℝ))) = _
  rw [responseMatrix_actual,LinearMap.det_toMatrix']

theorem pullback_integrable (S : Set Point) (measurable : MeasurableSet S)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S)
    (t : Time) (observable : Point → ℝ) (paid : IntegrableOn observable S) :
    IntegrableOn (fun x => (responseMatrix x t).det * observable (flow x (spatialStep*(t : ℝ)))) S := by
  have formula := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurable
    (fun x _ => (original_flow_strictDerivative x t).hasFDerivAt.hasFDerivWithinAt)
    (flowHomeomorph (spatialStep*(t : ℝ))).injective.injOn observable
  change IntegrableOn observable ((flowHomeomorph (spatialStep*(t : ℝ))) '' S) ↔ _ at formula
  rw [flow_image S invariant] at formula
  have received := formula.mp paid
  convert! received using 1
  funext x
  rw [abs_of_pos (actual_determinant_positive x t)]
  rw [responseMatrix_actual,LinearMap.det_toMatrix']
  rfl

theorem pull_integrable (S : Set Point) (measurable : MeasurableSet S)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S)
    (test : Test) (t : Time) : IntegrableOn (pull test t) S :=
  pullback_integrable S measurable invariant t test.value test.integrable.integrableOn

theorem pull_integral (S : Set Point) (measurable : MeasurableSet S)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S)
    (test : Test) (t : Time) :
    (∫ x in S, pull test t x) = ∫ x in S, test.value x :=
  (change_variables S measurable invariant t test.value).symm

theorem pull_integral_derivative (S : Set Point) (measurable : MeasurableSet S)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S) (test : Test) :
    IntegrableOn (pullDerivative test 0) S ∧
    HasDerivAt (fun t : ℝ => ∫ x in S, pull test t x) (∫ x in S, pullDerivative test 0 x) 0 := by
  obtain ⟨R,_,A,apos,B,bpos,value,derivative,outside⟩ := test.bounds
  let window := Ioo (-(1/2) : ℝ) (1/2)
  have near : window ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have ae_measurable : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (pull test t) (volume.restrict S) := by
    filter_upwards [near] with t inside
    exact (pull_integrable S measurable invariant test ⟨t,inside.1.le,inside.2.le⟩).aestronglyMeasurable
  have initial : Integrable (pull test 0) (volume.restrict S) := by
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
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le near ae_measurable initial differential.aestronglyMeasurable
    (Eventually.of_forall (fun x t inside => original_domination test R A B apos bpos value derivative outside x
      ⟨t,inside.1.le,inside.2.le⟩)) (dominating_integrable R A B).integrableOn
    (Eventually.of_forall (fun x t inside => pull_derivative test x ⟨t,inside.1.le,inside.2.le⟩))

theorem weak_divergence (S : Set Point) (measurable : MeasurableSet S)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S) (test : Test) :
    (∫ x in S, laplacian sourceTerms densityMatrix x*test.value x+
      test.derivative x (sourceGradient x)) = 0 := by
  have actual := (pull_integral_derivative S measurable invariant test).2
  have constant : (fun t : ℝ => ∫ x in S, pull test t x) =ᶠ[𝓝 (0 : ℝ)]
      (fun _ => ∫ x in S, test.value x) := by
    filter_upwards [Ioo_mem_nhds (show (-(1/2) : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1/2 by norm_num)] with t inside
    exact pull_integral S measurable invariant test ⟨t,inside.1.le,inside.2.le⟩
  have zero := actual.congr_of_eventuallyEq constant.symm |>.unique
    (hasDerivAt_const 0 (∫ x in S, test.value x))
  simp_rw [pullDerivative_zero] at zero
  rw [integral_const_mul] at zero
  exact (mul_eq_zero.mp zero).resolve_left spatialStep_positive.ne'

theorem cutoff_divergence_integral (S : Set Point) (measurable : MeasurableSet S)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S) (n : ℕ) :
    (∫ x in S, cutoffDivergence n x) = 0 :=
  weak_divergence S measurable invariant (cutoff n)

/-- Any measurable flow-invariant set pays the same integrated zero-flux law. -/
theorem zero_flux (S : Set Point) (measurable : MeasurableSet S)
    (invariant : ∀ (x : Point) (t : ℝ), flow x t ∈ S ↔ x ∈ S) :
    (∫ x in S, laplacian sourceTerms densityMatrix x) = 0 := by
  obtain ⟨C,nonnegative,bound⟩ := cutoff_derivative_bounds
  have converges : Tendsto (fun n => ∫ x in S, cutoffDivergence n x) atTop
      (𝓝 (∫ x in S, laplacian sourceTerms densityMatrix x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖laplacian sourceTerms densityMatrix x‖+C*‖sourceGradient x‖)
      (fun n => (cutoffDivergence_continuous n).aestronglyMeasurable)
      (sourceLaplacian_integrable.norm.add (sourceGradient_integrable.norm.const_mul C)).integrableOn
      (fun n => Eventually.of_forall (cutoffDivergence_bound C nonnegative bound n))
    apply Eventually.of_forall
    intro x
    have first : Tendsto (fun _ : ℕ => laplacian sourceTerms densityMatrix x) atTop
        (𝓝 (laplacian sourceTerms densityMatrix x)) := tendsto_const_nhds
    have limit := (first.mul (cutoff_tends_one x)).add (cutoff_gradient_limit C bound x)
    simpa only [cutoffDivergence,mul_one,add_zero] using limit
  simp_rw [cutoff_divergence_integral S measurable invariant] at converges
  exact tendsto_nhds_unique converges tendsto_const_nhds

theorem whole_space_zero_flux : (∫ x, laplacian sourceTerms densityMatrix x) = 0 := by
  have h := zero_flux univ MeasurableSet.univ (fun x t => by simp)
  rwa [setIntegral_univ] at h

theorem atom7_specialization : type_of% actual_basin_zero_flux :=
  zero_flux basin basin_measurable flow_membership

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak.Invariant
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
