import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Tensor

set_option autoImplicit false
open scoped Topology BigOperators

namespace SaturationMonoid.NavierStokes.NativeResponseTensorPayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint
noncomputable section
variable {nu : Viscosity}

private theorem bilinear_derivative
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {u : ℝ → E} {v : ℝ → F}
    {u' : E} {v' : F} {time : ℝ} (du : HasDerivAt u u' time)
    (dv : HasDerivAt v v' time) :
    HasDerivAt (fun t => B (u t) (v t)) (B u' (v time)+B (u time) v') time := by
  exact (B.hasFDerivAt.comp_hasDerivAt time du).clm_apply dv

theorem pairTensor_hasDerivAt (M : ℕ) {u z : ℝ → physicalSpace (modes M)}
    {u' z' : physicalSpace (modes M)} {time : ℝ}
    (du : HasDerivAt u u' time) (dz : HasDerivAt z z' time) :
    HasDerivAt (fun t => pairTensor M (u t) (z t))
      (pairTensor M u' (z time)+pairTensor M (u time) z') time := by
  have actual := bilinear_derivative (pairTensorCLM M) du dz
  simpa only [pairTensorCLM_apply,Function.comp_def] using actual

def liftedRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (w g : physicalSpace (modes M)) : physicalSpace (modes M) :=
  NativeWindowTraceDualEvolution.inverse seed M F radius time
    (-NativeWindowTraceAdjoint.dual seed M time w-g-
      deriv (NativeWindowTraceDualEvolution.mass seed M F radius) time
        (NativeWindowTraceDualEvolution.lifted seed M F radius time w))

theorem lifted_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (horizon time : ℝ)
    (inside : time ∈ Ioo 0 horizon)
    (generated : ∀ t ∈ Icc 0 horizon,
      (NativeWindowTraceDualEvolution.mass seed M F radius t).IsInvertible)
    {p : ℝ → physicalSpace (modes M)} {g : physicalSpace (modes M)}
    (actual : HasDerivAt p (-NativeWindowTraceAdjoint.dual seed M time (p time)-g) time) :
    HasDerivAt (fun t => NativeWindowTraceDualEvolution.lifted seed M F radius t (p t))
      (liftedRate seed M F radius time (p time) g) time := by
  let z := fun t => NativeWindowTraceDualEvolution.lifted seed M F radius t (p t)
  let T := NativeWindowTraceDualEvolution.mass seed M F radius
  have inverted := generated time (Ioo_subset_Icc_self inside)
  have zd : DifferentiableAt ℝ z time :=
    (NativeWindowTraceDualEvolution.inverse_differentiableAt seed M F radius time inverted).clm_apply
      actual.differentiableAt
  have td := ((NativeWindowTraceDualEvolution.mass_contDiff seed M F radius).differentiable
    (by norm_num) time).hasDerivAt
  have same : (fun t => T t (z t)) =ᶠ[𝓝 time] p := by
    filter_upwards [Icc_mem_nhds inside.1 inside.2] with t ht
    exact (generated t ht).self_apply_inverse (p t)
  have equation := ((td.clm_apply zd.hasDerivAt).congr_of_eventuallyEq same.symm).unique actual
  have write : T time (deriv z time) =
      -NativeWindowTraceAdjoint.dual seed M time (p time)-g-deriv T time (z time) := by
    change deriv T time (z time)+T time (deriv z time) = _ at equation
    exact eq_sub_of_add_eq' equation
  have back := congrArg (T time).inverse write
  rw [inverted.inverse_apply_self] at back
  exact zd.hasDerivAt.congr_deriv back

theorem source_tensor_rate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∀ radius ≥ low, ∀ outerRadius M observation
      (test : physicalSpace (modes M)) a b (ab : a ≤ b),
      ∀ᵐ time : ℝ, time ∈ Ioo a b → time ∈ Ioo 0 horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test a b ab
      let u := NativeWindowTraceAdjoint.value seed M time
      let z := NativeWindowTraceDualEvolution.lifted seed M F radius time (p time)
      HasDerivAt (fun t => mixedTensor seed M F radius t (p t))
        (pairTensor M (NativeWindowTraceAdjoint.forward seed M time u+
            NativeWindowStageNineSource.forcing seed M time) z+
          pairTensor M u (liftedRate seed M F radius time (p time)
            (load (nu := nu) observation M test time))) time := by
  obtain ⟨low,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M observation test a b ab => ?_⟩
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,
    NativeWindowTraceAdjoint.source_action_ae seed M] with time actual source physical clock
  let F := integerWaveFrequencyCube outerRadius
  let p := response seed M observation test a b ab
  have du := (NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual
  change HasDerivAt (NativeWindowTraceAdjoint.value seed M) _ time at du
  rw [source clock.1.le] at du
  have dp := (response_derivative seed M observation test a b ab time
    (Ioo_subset_Icc_self physical)).hasDerivAt (Icc_mem_nhds physical.1 physical.2)
  have dz := lifted_hasDerivAt seed M F radius horizon time clock
    (inverted radius above M F (NativeWindowFiniteGramFourier.cube_closed outerRadius)) dp
  exact pairTensor_hasDerivAt M du dz

end
end SaturationMonoid.NavierStokes.NativeResponseTensorPayment
