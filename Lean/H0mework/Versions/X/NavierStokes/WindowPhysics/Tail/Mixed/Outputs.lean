import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Mixed.Physical

set_option autoImplicit false
open scoped Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeMixedHeatOutputs
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowSpacetimeFourier NativeMixedHeatSource NativeMixedHeatReadout NativeMixedHeatPhysical
noncomputable section
variable {nu : Viscosity}

theorem velocity_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (NativeWindowSpacetimeVelocity.jointField seed lag) (domain seed H) := by
  by_cases zero : lag=0
  · subst lag
    exact (NativeWindowTailPhysical.velocity_smooth seed).mono (domain_subset seed H)
  · exact (NativeWindowSpacetimeVelocity.jointField_smooth seed lag
      (lt_of_le_of_ne zero_le (Ne.symm zero))).contDiffOn

theorem stress_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (NativeWindowSpacetimeStress.jointField seed lag) (domain seed H) := by
  by_cases zero : lag=0
  · subst lag
    exact (NativeWindowTailPhysical.stress_smooth seed).mono (domain_subset seed H)
  · exact (NativeWindowSpacetimeStress.jointField_smooth seed lag
      (lt_of_le_of_ne zero_le (Ne.symm zero))).contDiffOn

theorem residual_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (NativeWindowSpacetimeResidual.jointField seed lag) (domain seed H) := by
  by_cases zero : lag=0
  · subst lag
    exact (NativeWindowTailPhysical.residual_smooth seed).mono (domain_subset seed H)
  · exact (NativeWindowSpacetimeResidual.jointField_smooth seed lag
      (lt_of_le_of_ne zero_le (Ne.symm zero))).contDiffOn

def vorticity (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (x : Spacetime) : PhysicalSpace :=
  NativeViewPhysicalCurl.jointCurlRead (fderiv ℝ (NativeWindowSpacetimeVelocity.jointField seed lag) x)

def rate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (x : Spacetime) : PhysicalSpace :=
  fderiv ℝ (NativeWindowSpacetimeVelocity.jointField seed lag) x (1,0)

theorem derivative_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (fderiv ℝ (NativeWindowSpacetimeVelocity.jointField seed lag)) (domain seed H) :=
  (contDiffOn_infty_iff_fderiv_of_isOpen (domain_open seed H)).mp (velocity_smooth seed H lag) |>.2

theorem vorticity_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (vorticity seed lag) (domain seed H) :=
  NativeViewPhysicalCurl.jointCurlRead.contDiff.comp_contDiffOn (derivative_smooth seed H lag)

theorem rate_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (rate seed lag) (domain seed H) :=
  (ContinuousLinearMap.apply ℝ PhysicalSpace ((1,0) : Spacetime)).contDiff.comp_contDiffOn (derivative_smooth seed H lag)

theorem vorticity_actual (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (x : Spacetime)
    (inside : x∈NativeWindowTailPhysical.support seed) :
    vorticity seed lag x=NativeTimeChartVorticityReadout.spatialCurl
      (fun space => NativeWindowSpacetimeVelocity.jointField seed lag (x.1,space)) x.2 := by
  have member : x∈domain seed (x.1+1) := ⟨⟨inside.1,by linarith⟩,trivial⟩
  have differentiable := (velocity_smooth seed (x.1+1) lag).contDiffAt
    ((domain_open seed (x.1+1)).mem_nhds member) |>.differentiableAt (by simp)
  have curve : HasFDerivAt (fun space : PhysicalSpace => (x.1,space))
      ((0 : PhysicalSpace →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ PhysicalSpace)) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have written := (differentiable.hasFDerivAt.comp x.2 curve).fderiv
  rw [vorticity,NativeTimeChartVorticityReadout.spatialCurl]
  simp only [Function.comp_def] at written
  rw [written,NativeViewPhysicalCurl.jointCurlRead_apply]
  rfl

theorem rate_momentum (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (x : Spacetime)
    (inside : x∈NativeWindowTailPhysical.support seed) :
    rate seed lag x=NativeViewPhysicalEquation.momentumField seed lag x := by
  have member : x∈domain seed (x.1+1) := ⟨⟨inside.1,by linarith⟩,trivial⟩
  have differentiable := (velocity_smooth seed (x.1+1) lag).contDiffAt
    ((domain_open seed (x.1+1)).mem_nhds member) |>.differentiableAt (by simp)
  have actual : HasDerivAt (fun t => NativeWindowSpacetimeVelocity.jointField seed lag (t,x.2))
      (rate seed lag x) x.1 := by
    simpa only [rate,Function.comp_def,id_eq] using!
      differentiable.hasFDerivAt.comp_hasDerivAt x.1
        ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  apply actual.unique
  by_cases zero : lag=0
  · subst lag
    exact NativeTailTimeAction.physical_hasDerivAt seed x.1 inside.1 x.2
  · exact NativeViewPhysicalEquation.physical_hasDerivAt seed lag
      (lt_of_le_of_ne zero_le (Ne.symm zero)) x.1
      (by
        have lower : NativeAbsoluteEventualControl.startTime seed-1 < x.1 := inside.1
        linarith [NativeAbsoluteEventualControl.startTime_nonnegative seed]) x.2

theorem vorticity_jets (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (vorticity seed lag))
      (iteratedFDeriv ℝ n (vorticity seed 0)) (𝓝 0) (domain seed H) :=
  clm_jets_uniform NativeViewPhysicalCurl.jointCurlRead _ _ (domain_open seed H)
    (derivative_smooth seed H) (derivative_smooth seed H 0) n
      (fderiv_jets_uniform _ _ n (velocity_jets seed H (n+1)))

theorem rate_jets (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (rate seed lag))
      (iteratedFDeriv ℝ n (rate seed 0)) (𝓝 0) (domain seed H) :=
  clm_jets_uniform (ContinuousLinearMap.apply ℝ PhysicalSpace ((1,0) : Spacetime)) _ _ (domain_open seed H)
    (derivative_smooth seed H) (derivative_smooth seed H 0) n
      (fderiv_jets_uniform _ _ n (velocity_jets seed H (n+1)))

def outputs (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (x : Spacetime) :=
  ((NativeWindowSpacetimeVelocity.jointField seed lag x,NativeWindowSpacetimeStress.jointField seed lag x,
    NativeWindowSpacetimeResidual.jointField seed lag x),vorticity seed lag x,rate seed lag x)

theorem outputs_smooth (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (lag : ℝ≥0) :
    ContDiffOn ℝ ∞ (outputs seed lag) (domain seed H) :=
  ((velocity_smooth seed H lag).prodMk ((stress_smooth seed H lag).prodMk (residual_smooth seed H lag))).prodMk
    ((vorticity_smooth seed H lag).prodMk (rate_smooth seed H lag))

theorem outputs_jets (seed : GeneratedWholeRestartCurrent nu) (H : ℝ) (n : ℕ) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (outputs seed lag))
      (iteratedFDeriv ℝ n (outputs seed 0)) (𝓝 0) (domain seed H) := by
  have tensor := prod_jets_uniform _ _ _ _ (domain_open seed H)
    (stress_smooth seed H) (residual_smooth seed H) (stress_smooth seed H 0) (residual_smooth seed H 0) n
    (stress_jets seed H n) (residual_jets seed H n)
  have fields := prod_jets_uniform _ _ _ _ (domain_open seed H)
    (velocity_smooth seed H) (fun lag => (stress_smooth seed H lag).prodMk (residual_smooth seed H lag))
    (velocity_smooth seed H 0) ((stress_smooth seed H 0).prodMk (residual_smooth seed H 0)) n
    (velocity_jets seed H n) tensor
  have rates := prod_jets_uniform _ _ _ _ (domain_open seed H)
    (vorticity_smooth seed H) (rate_smooth seed H) (vorticity_smooth seed H 0) (rate_smooth seed H 0) n
    (vorticity_jets seed H n) (rate_jets seed H n)
  exact prod_jets_uniform _ _ _ _ (domain_open seed H)
    (fun lag => (velocity_smooth seed H lag).prodMk ((stress_smooth seed H lag).prodMk (residual_smooth seed H lag)))
    (fun lag => (vorticity_smooth seed H lag).prodMk (rate_smooth seed H lag))
    ((velocity_smooth seed H 0).prodMk ((stress_smooth seed H 0).prodMk (residual_smooth seed H 0)))
    ((vorticity_smooth seed H 0).prodMk (rate_smooth seed H 0)) n fields rates

theorem compact_outputs_jets (seed : GeneratedWholeRestartCurrent nu) (n : ℕ)
    {K : Set Spacetime} (compact : IsCompact K) (contained : K⊆NativeWindowTailPhysical.support seed) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => iteratedFDeriv ℝ n (outputs seed lag))
      (iteratedFDeriv ℝ n (outputs seed 0)) (𝓝 0) K := by
  obtain ⟨H,bounded⟩ := (compact.image continuous_fst).bddAbove
  apply (outputs_jets seed (H+1) n).mono
  intro x inside
  refine ⟨⟨(contained inside).1,?_⟩,trivial⟩
  have upper := bounded ⟨x,inside,rfl⟩
  linarith

theorem compact_outputs_common_bound (seed : GeneratedWholeRestartCurrent nu) (n : ℕ)
    {K : Set Spacetime} (compact : IsCompact K) (contained : K⊆NativeWindowTailPhysical.support seed) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ lag : ℝ≥0 in 𝓝 0, ∀ x∈K,
      ‖iteratedFDeriv ℝ n (outputs seed lag) x‖ ≤ B := by
  obtain ⟨H,bounded⟩ := (compact.image continuous_fst).bddAbove
  have subset : K⊆domain seed (H+1) := by
    intro x inside
    refine ⟨⟨(contained inside).1,?_⟩,trivial⟩
    have upper := bounded ⟨x,inside,rfl⟩
    linarith
  have continuous : ContinuousOn (iteratedFDeriv ℝ n (outputs seed 0)) K :=
    (ContinuousOn.continuousOn_iteratedFDeriv (outputs_smooth seed (H+1) 0) (domain_open seed (H+1))
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).mono subset
  obtain ⟨C,cap⟩ := compact.exists_bound_of_continuousOn continuous
  refine ⟨max C 0+1,by positivity,?_⟩
  have close := (Metric.tendstoUniformlyOn_iff.mp (compact_outputs_jets seed n compact contained)) 1 zero_lt_one
  filter_upwards [close] with lag near
  intro x inside
  have triangle := norm_le_norm_add_norm_sub
    (iteratedFDeriv ℝ n (outputs seed 0) x) (iteratedFDeriv ℝ n (outputs seed lag) x)
  rw [norm_sub_rev (iteratedFDeriv ℝ n (outputs seed 0) x)] at triangle
  have error : ‖iteratedFDeriv ℝ n (outputs seed lag) x-iteratedFDeriv ℝ n (outputs seed 0) x‖ < 1 := by
    simpa only [dist_eq_norm,norm_sub_rev] using near x inside
  exact triangle.trans (by linarith [cap x inside,le_max_left C 0])

end
end SaturationMonoid.NavierStokes.NativeMixedHeatOutputs
