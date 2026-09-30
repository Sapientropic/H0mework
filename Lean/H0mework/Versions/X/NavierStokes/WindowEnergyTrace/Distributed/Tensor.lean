import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Weighted
import H0mework.Versions.X.NavierStokes.StressAction.StressDynamicsBilinear
import H0mework.Versions.X.NavierStokes.UnheatedWriterSobolev.Product

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

private theorem rescaled_quadratic (n c a b : ℝ) (n0 : 0 ≤ n) (c0 : 0 ≤ c)
    (a0 : 0 ≤ a) (b0 : 0 ≤ b)
    (bounded : ∀ r : ℝ, |r| * n ≤ c*(r^2*a+b)) :
    n^2 ≤ 4*c^2*a*b := by
  by_cases hz : n = 0
  · rw [hz,zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  have np : 0 < n := lt_of_le_of_ne n0 (Ne.symm hz)
  by_cases hc : c = 0
  · have h := bounded 1
    simp only [abs_one,one_mul,hc,zero_mul] at h
    exact False.elim (not_le_of_gt np h)
  have cp : 0 < c := lt_of_le_of_ne c0 (Ne.symm hc)
  by_cases ha : a = 0
  · let r := (c*b+1)/n
    have rp : 0 < r := by dsimp only [r]; positivity
    have h := bounded r
    rw [abs_of_pos rp,ha,mul_zero,zero_add] at h
    have eqn : r*n = c*b+1 := by dsimp only [r]; exact div_mul_cancel₀ _ hz
    linarith only [h,eqn]
  have ap : 0 < a := lt_of_le_of_ne a0 (Ne.symm ha)
  let r := n/(2*c*a)
  have rp : 0 < r := by dsimp only [r]; positivity
  have h := bounded r
  rw [abs_of_pos rp] at h
  have scaled := mul_le_mul_of_nonneg_left h (show 0 ≤ 4*c*a by positivity)
  have left : (4*c*a)*(r*n) = 2*n^2 := by dsimp only [r]; field_simp; ring
  have right : (4*c*a)*(c*(r^2*a+b)) = n^2+4*c^2*a*b := by
    dsimp only [r]
    field_simp
    ring
  rw [left,right] at scaled
  linarith only [scaled]

private theorem gradient_density_smul (r : ℝ) (u : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    NativeUnheatedStressProduct.density (r • u) wave =
      r^2*NativeUnheatedStressProduct.density u wave := by
  unfold NativeUnheatedStressProduct.density NativeUnheatedStressProduct.amplitude
  simp only [lp.coeFn_smul,Pi.smul_apply]
  change integerWaveNormSq wave * ‖r • euclideanCoordinateRow (u wave)‖^2 = _
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  ring

private theorem gradient_mass_smul (r : ℝ) (u : ComplexVorticityHilbertState) :
    NativeUnheatedStressProduct.gradientMass (r • u) =
      r^2*NativeUnheatedStressProduct.gradientMass u := by
  simp only [NativeUnheatedStressProduct.gradientMass,gradient_density_smul,tsum_mul_left]

private theorem h1_smul (r : ℝ) (u : ComplexVorticityHilbertState)
    (regular : NativeUnheatedStressProduct.H1 u) :
    NativeUnheatedStressProduct.H1 (r • u) := by
  exact (regular.mul_left (r^2)).congr fun wave => (gradient_density_smul r u wave).symm

private theorem tensor_smul (r : ℝ) (u v : ComplexVorticityHilbertState)
    (u0 : u 0 = 0) (v0 : v 0 = 0)
    (hu : NativeUnheatedStressProduct.H1 u) (hv : NativeUnheatedStressProduct.H1 v) :
    NativeWindowSobolevProduct.state (r • u) v
      (by simp only [lp.coeFn_smul,Pi.smul_apply,u0,smul_zero]) v0 (h1_smul r u hu) hv =
      r • NativeWindowSobolevProduct.state u v u0 v0 hu hv := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro pair
  change NativeWindowSobolevStress.quarter wave •
    NativeHigherTimeJets.mixedFlux (r • u) v wave pair.1 pair.2 =
      r • (NativeWindowSobolevStress.quarter wave •
        NativeHigherTimeJets.mixedFlux u v wave pair.1 pair.2)
  rw [NativeHigherTimeJets.mixedFlux_smul_left,smul_comm]

theorem mixed_half_square_bound (u v : ComplexVorticityHilbertState)
    (u0 : u 0 = 0) (v0 : v 0 = 0)
    (hu : NativeUnheatedStressProduct.H1 u) (hv : NativeUnheatedStressProduct.H1 v) :
    ‖NativeWindowSobolevProduct.state u v u0 v0 hu hv‖^2 ≤
      144*NativeUnheatedRieszKernel.constant*
        NativeUnheatedStressProduct.gradientMass u*
          NativeUnheatedStressProduct.gradientMass v := by
  have scaled (r : ℝ) : |r| * ‖NativeWindowSobolevProduct.state u v u0 v0 hu hv‖ ≤
      (6*Real.sqrt NativeUnheatedRieszKernel.constant)*
        (r^2*NativeUnheatedStressProduct.gradientMass u+NativeUnheatedStressProduct.gradientMass v) := by
    have paid := NativeWindowSobolevProduct.state_bound (r • u) v
      (by simp only [lp.coeFn_smul,Pi.smul_apply,u0,smul_zero]) v0 (h1_smul r u hu) hv
    rw [tensor_smul,norm_smul,Real.norm_eq_abs,gradient_mass_smul] at paid
    exact paid
  have paid := rescaled_quadratic
    ‖NativeWindowSobolevProduct.state u v u0 v0 hu hv‖
    (6*Real.sqrt NativeUnheatedRieszKernel.constant)
    (NativeUnheatedStressProduct.gradientMass u) (NativeUnheatedStressProduct.gradientMass v)
    (norm_nonneg _) (by positivity)
    (tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative u))
    (tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative v)) scaled
  convert paid using 1
  rw [mul_pow,Real.sq_sqrt NativeUnheatedRieszKernel.constant_nonnegative]
  ring

private theorem physical_H1 (M : ℕ) (v : physicalSpace (modes M)) :
    NativeUnheatedStressProduct.H1 v.1 := by
  apply summable_of_ne_finset_zero (s := modes M)
  intro wave outside
  simp [NativeUnheatedStressProduct.density,NativeUnheatedStressProduct.amplitude,
    physical_supported v wave outside,euclideanCoordinateRow]

private theorem physical_projection (M : ℕ) (v : physicalSpace (modes M)) :
    complexSharpSupportProjection (modes M) v.1 = v.1 := by
  apply lp.ext
  funext wave
  by_cases inside : wave ∈ modes M
  · simp only [complexSharpSupportProjection_apply,if_pos inside]
  · simp only [complexSharpSupportProjection_apply,if_neg inside,
      physical_supported v wave inside]

def mixedTensor (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (w : physicalSpace (modes M)) : NativeCompleteStressCarrier.Space :=
  let u := NativeWindowTraceAdjoint.value seed M time
  let z := NativeWindowTraceDualEvolution.lifted seed M F radius time w
  NativeWindowSobolevProduct.state u.1 z.1
    (physical_supported u 0 (modes_zero M)) (physical_supported z 0 (modes_zero M))
    (physical_H1 M u) (physical_H1 M z)

theorem mixedTensor_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (w : physicalSpace (modes M)) (wave : IntegerWavevector) (i j : Coordinate) :
    mixedTensor seed M F radius time w wave (i,j) =
      NativeWindowSobolevStress.quarter wave • NativeHigherTimeJets.mixedFlux
        (NativeWindowTraceAdjoint.value seed M time).1
        (NativeWindowTraceDualEvolution.lifted seed M F radius time w).1 wave i j := rfl

private theorem value_gradient_bound (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ M,
      NativeUnheatedStressProduct.gradientMass (NativeWindowTraceAdjoint.value seed M time).1 ≤
        NativeUnheatedSourceGradient.mass seed time := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular positive M
  have paid := NativeWholeH1Approximation.project_mass_le M
    (NativeUnheatedSourceGradient.physical seed time positive) (regular positive)
  rw [NativeUnheatedSourceGradient.physical_mass] at paid
  unfold NativeWholeH1Mixed.gradientMass NativeWholeH1Mixed.gradientDensity at paid
  rw [NativeWholeH1Approximation.project_whole] at paid
  rw [NativeWindowTraceAdjoint.value,NativeWindowStageNineSource.lift_load seed time positive M]
  simp only [NativeWindowStressOseenSource.load,NativeUnheatedSourceQuadraticApprox.physicalSource,
    dif_pos positive]
  exact paid

theorem source_mixed_tensor_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∀ radius ≥ low, ∀ outerRadius M,
      ∀ᵐ time : ℝ, time ∈ Icc 0 horizon → ∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      ‖mixedTensor seed M F radius time w‖^2 ≤
        (288*NativeUnheatedRieszKernel.constant/(nu.coeff*(2*Real.pi)^2))*
          NativeUnheatedSourceGradient.mass seed time*
            NativeWindowTraceDualEvolution.energy seed M F radius time w := by
  obtain ⟨low,C,C0,control⟩ := NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M => ?_⟩
  filter_upwards [value_gradient_bound seed] with time source inside w
  let F := integerWaveFrequencyCube outerRadius
  let u := NativeWindowTraceAdjoint.value seed M time
  let z := NativeWindowTraceDualEvolution.lifted seed M F radius time w
  let E := NativeWindowTraceDualEvolution.energy seed M F radius time w
  have paid := (control radius above outerRadius M time inside).2 w
  have coercive : pairing (modes M) z z +
      (nu.coeff/2)*NativeCommonAdvectorAction.curlPair (modes M) z.1 z.1 ≤ E := paid.2.1
  have mass0 : 0 ≤ pairing (modes M) z z := by
    change 0 ≤ inner ℝ (coefficients (modes M) z) (coefficients (modes M) z)
    exact real_inner_self_nonneg
  have curl := NativeWindowAugmentedTestProduct.curl_original (modes M) z (modes_zero M)
  rw [physical_projection] at curl
  have denominator : 0 < nu.coeff*(2*Real.pi)^2 := by positivity [nu.coeff_pos]
  have gradient : NativeUnheatedStressProduct.gradientMass z.1 ≤
      (2/(nu.coeff*(2*Real.pi)^2))*E := by
    have multiplied : (nu.coeff*(2*Real.pi)^2)*NativeUnheatedStressProduct.gradientMass z.1 ≤ 2*E := by
      rw [curl] at coercive
      nlinarith only [coercive,mass0]
    have divided : NativeUnheatedStressProduct.gradientMass z.1 ≤
        (2*E)/(nu.coeff*(2*Real.pi)^2) :=
      (le_div_iff₀ denominator).mpr (by nlinarith only [multiplied])
    exact divided.trans_eq (by ring)
  have mixed := mixed_half_square_bound u.1 z.1
    (physical_supported u 0 (modes_zero M)) (physical_supported z 0 (modes_zero M))
    (physical_H1 M u) (physical_H1 M z)
  have actual := source inside.1 M
  have first := mul_le_mul_of_nonneg_left actual
    (show 0 ≤ 144*NativeUnheatedRieszKernel.constant by positivity [NativeUnheatedRieszKernel.constant_nonnegative])
  have combined := mul_le_mul first gradient
    (tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative z.1))
    (mul_nonneg (show 0 ≤ 144*NativeUnheatedRieszKernel.constant by positivity [NativeUnheatedRieszKernel.constant_nonnegative])
      (NativeUnheatedSourceGradient.mass_nonnegative seed time))
  change ‖mixedTensor seed M F radius time w‖^2 ≤ _
  exact mixed.trans (combined.trans_eq (by dsimp only [E]; ring))

def pairTensor (M : ℕ) (u z : physicalSpace (modes M)) : NativeCompleteStressCarrier.Space :=
  NativeWindowSobolevProduct.state u.1 z.1
    (physical_supported u 0 (modes_zero M)) (physical_supported z 0 (modes_zero M))
    (physical_H1 M u) (physical_H1 M z)

private theorem pairTensor_add_left (M : ℕ) (u v z : physicalSpace (modes M)) :
    pairTensor M (u+v) z = pairTensor M u z + pairTensor M v z := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro pair
  change NativeWindowSobolevStress.quarter wave •
    NativeHigherTimeJets.mixedFlux (u.1+v.1) z.1 wave pair.1 pair.2 =
      NativeWindowSobolevStress.quarter wave • NativeHigherTimeJets.mixedFlux u.1 z.1 wave pair.1 pair.2 +
      NativeWindowSobolevStress.quarter wave • NativeHigherTimeJets.mixedFlux v.1 z.1 wave pair.1 pair.2
  rw [NativeHigherTimeJets.mixedFlux_add_left,smul_add]

private theorem pairTensor_add_right (M : ℕ) (u z w : physicalSpace (modes M)) :
    pairTensor M u (z+w) = pairTensor M u z + pairTensor M u w := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro pair
  change NativeWindowSobolevStress.quarter wave •
    NativeHigherTimeJets.mixedFlux u.1 (z.1+w.1) wave pair.1 pair.2 =
      NativeWindowSobolevStress.quarter wave • NativeHigherTimeJets.mixedFlux u.1 z.1 wave pair.1 pair.2 +
      NativeWindowSobolevStress.quarter wave • NativeHigherTimeJets.mixedFlux u.1 w.1 wave pair.1 pair.2
  rw [NativeHigherTimeJets.mixedFlux_add_right,smul_add]

private theorem pairTensor_smul_left (M : ℕ) (c : ℝ) (u z : physicalSpace (modes M)) :
    pairTensor M (c • u) z = c • pairTensor M u z := by
  exact tensor_smul c u.1 z.1 _ _ _ _

private theorem pairTensor_smul_right (M : ℕ) (c : ℝ) (u z : physicalSpace (modes M)) :
    pairTensor M u (c • z) = c • pairTensor M u z := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro pair
  change NativeWindowSobolevStress.quarter wave •
    NativeHigherTimeJets.mixedFlux u.1 (c • z.1) wave pair.1 pair.2 =
      c • (NativeWindowSobolevStress.quarter wave •
        NativeHigherTimeJets.mixedFlux u.1 z.1 wave pair.1 pair.2)
  rw [NativeHigherTimeJets.mixedFlux_smul_right,smul_comm]

def pairTensorCLM (M : ℕ) : physicalSpace (modes M) →L[ℝ]
    physicalSpace (modes M) →L[ℝ] NativeCompleteStressCarrier.Space :=
  LinearMap.toContinuousLinearMap {
    toFun := fun u => LinearMap.toContinuousLinearMap {
      toFun := pairTensor M u
      map_add' := pairTensor_add_right M u
      map_smul' := fun c z => pairTensor_smul_right M c u z }
    map_add' := by
      intro u v
      apply ContinuousLinearMap.ext
      exact pairTensor_add_left M u v
    map_smul' := by
      intro c u
      apply ContinuousLinearMap.ext
      exact pairTensor_smul_left M c u }

theorem pairTensorCLM_apply (M : ℕ) (u z : physicalSpace (modes M)) :
    pairTensorCLM M u z = pairTensor M u z := rfl


end
end SaturationMonoid.NavierStokes.NativeResponseTensorPayment
