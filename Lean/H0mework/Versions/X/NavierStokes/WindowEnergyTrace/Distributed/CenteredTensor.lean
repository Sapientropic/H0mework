import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.TensorTime
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Mean

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredResponseTensor
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWindowDistributedAdjoint NativeResponseTensorPayment
open NativeWindowTraceDualEvolution (mass lifted energy)
open NativeWindowHistoryMeanAction (meanValue)
noncomputable section
variable {nu : Viscosity}

def centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ) :=
  NativeWindowTraceAdjoint.value seed M time-meanValue seed M frame

def tensor (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ)
    (w : physicalSpace (modes M)) : NativeCompleteStressCarrier.Space :=
  pairTensor M (centered seed M frame time) (lifted seed M F radius time w)

theorem tensor_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ)
    (w : physicalSpace (modes M)) (k : IntegerWavevector) (i j : Coordinate) :
    tensor seed M F radius frame time w k (i,j) =
      NativeWindowSobolevStress.quarter k • NativeHigherTimeJets.mixedFlux
        (centered seed M frame time).1 (lifted seed M F radius time w).1 k i j := rfl

private theorem projection (M : ℕ) (v : physicalSpace (modes M)) :
    complexSharpSupportProjection (modes M) v.1=v.1 := by
  apply lp.ext
  funext k
  by_cases inside : k∈modes M
  · simp only [complexSharpSupportProjection_apply,if_pos inside]
  · simp only [complexSharpSupportProjection_apply,if_neg inside,physical_supported v k inside]

private theorem curl_nonnegative (M : ℕ) (v : physicalSpace (modes M)) :
    0 ≤ curlPair (modes M) v.1 v.1 := by
  rw [NativeWindowAugmentedTestProduct.curl_original (modes M) v (modes_zero M),projection]
  exact mul_nonneg (sq_nonneg _)
    (tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative v.1))

private theorem pair_curl_bound (M : ℕ) (u z : physicalSpace (modes M)) :
    ‖pairTensor M u z‖^2 ≤
      (144*NativeUnheatedRieszKernel.constant/(2*Real.pi)^4)*
        curlPair (modes M) u.1 u.1*curlPair (modes M) z.1 z.1 := by
  have source : ‖pairTensor M u z‖^2 ≤144*NativeUnheatedRieszKernel.constant*
      NativeUnheatedStressProduct.gradientMass u.1*NativeUnheatedStressProduct.gradientMass z.1 := by
    unfold pairTensor
    exact mixed_half_square_bound ..
  have first := NativeWindowAugmentedTestProduct.curl_original (modes M) u (modes_zero M)
  have last := NativeWindowAugmentedTestProduct.curl_original (modes M) z (modes_zero M)
  rw [projection] at first last
  apply source.trans_eq
  rw [first,last]
  field_simp

private theorem mean_curl_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (frame : ℝ) (inside : frame∈Icc 0 horizon) :
    curlPair (modes M) (meanValue seed M frame).1 (meanValue seed M frame).1 ≤
      |NativeWindowAugmentedPayment.graphBudget seed 0 horizon|+1 := by
  have source := NativeWindowHistoryMeanGradient.source_mean_budget seed horizon M frame inside
  change curlPair (modes M)
    (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed frame M))).1
    (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed frame M))).1 ≤ _ at source
  rw [NativeWindowHistoryCreationHalf.mean_restrict] at source
  exact source.trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))

private theorem norm_sub_square {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x-y‖^2 ≤2*‖x‖^2+2*‖y‖^2 := by
  have first := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [first,sq_nonneg (‖x‖-‖y‖)]

theorem source_tensor_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧∀ radius ≥ low,∀ outerRadius M,
      ∀ frame∈Icc 0 horizon,∀ᵐ time : ℝ,time∈Icc 0 horizon →∀ w : physicalSpace (modes M),
        ‖tensor seed M (integerWaveFrequencyCube outerRadius) radius frame time w‖^2 ≤
          C*(1+NativeUnheatedSourceGradient.mass seed time)*
            energy seed M (integerWaveFrequencyCube outerRadius) radius time w := by
  obtain ⟨first,raw⟩ := source_mixed_tensor_paid seed horizon nonnegative
  obtain ⟨last,D,D0,control⟩ := NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  let A := 288*NativeUnheatedRieszKernel.constant/(nu.coeff*(2*Real.pi)^2)
  let B := |NativeWindowAugmentedPayment.graphBudget seed 0 horizon|+1
  let K := 144*NativeUnheatedRieszKernel.constant/(2*Real.pi)^4
  let C := K*B*(2/nu.coeff)
  have A0 : 0 ≤ A := by dsimp only [A]; positivity [NativeUnheatedRieszKernel.constant_nonnegative,nu.coeff_pos]
  have B0 : 0 ≤ B := by dsimp only [B]; positivity
  have K0 : 0 ≤ K := by dsimp only [K]; positivity [NativeUnheatedRieszKernel.constant_nonnegative]
  have C0 : 0 ≤ C := by dsimp only [C]; positivity [nu.coeff_pos]
  refine ⟨max first last,2*(A+C),by positivity,fun radius above outerRadius M frame framed => ?_⟩
  filter_upwards [raw radius ((le_max_left first last).trans above) outerRadius M] with time actual inside w
  let F := integerWaveFrequencyCube outerRadius
  let z := lifted seed M F radius time w
  let E := energy seed M F radius time w
  let m := meanValue seed M frame
  have source := (control radius ((le_max_right first last).trans above) outerRadius M time inside).2 w
  have E0 : 0 ≤ E := source.1
  have mass0 : 0 ≤ pairing (modes M) z z := by
    change 0 ≤ inner ℝ (coefficients (modes M) z) (coefficients (modes M) z)
    exact real_inner_self_nonneg
  have coerced : pairing (modes M) z z+(nu.coeff/2)*curlPair (modes M) z.1 z.1 ≤ E := source.2.1
  have curl : curlPair (modes M) z.1 z.1 ≤(2/nu.coeff)*E := by
    have divided : curlPair (modes M) z.1 z.1 ≤(2*E)/nu.coeff :=
      (le_div_iff₀ nu.coeff_pos).mpr (by nlinarith only [coerced,mass0])
    exact divided.trans_eq (by ring)
  have mean := pair_curl_bound M m z
  have mixed := mul_le_mul
    (mul_le_mul_of_nonneg_left (mean_curl_bound seed horizon M frame framed) K0)
    curl (curl_nonnegative M z) (mul_nonneg K0 B0)
  have meanPaid : ‖pairTensor M m z‖^2 ≤ C*E :=
    mean.trans (mixed.trans_eq (by dsimp only [C]; ring))
  have rawPaid : ‖mixedTensor seed M F radius time w‖^2 ≤
      A*NativeUnheatedSourceGradient.mass seed time*E := actual inside w
  have split : tensor seed M F radius frame time w =
      mixedTensor seed M F radius time w-pairTensor M m z := by
    change pairTensorCLM M (NativeWindowTraceAdjoint.value seed M time-m) z =
      pairTensorCLM M (NativeWindowTraceAdjoint.value seed M time) z-pairTensorCLM M m z
    rw [map_sub,sub_apply]
  rw [split]
  have triangle := norm_sub_square (mixedTensor seed M F radius time w) (pairTensor M m z)
  have Y0 := NativeUnheatedSourceGradient.mass_nonnegative seed time
  have scalar : A*NativeUnheatedSourceGradient.mass seed time+C ≤
      (A+C)*(1+NativeUnheatedSourceGradient.mass seed time) := by
    nlinarith only [A0,mul_nonneg C0 Y0]
  have paid := mul_le_mul_of_nonneg_right scalar E0
  dsimp only [E,F] at rawPaid meanPaid triangle paid ⊢
  nlinarith only [rawPaid,meanPaid,triangle,paid]

theorem centered_action_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ) :
    NativeWindowTraceAdjoint.forward seed M time (NativeWindowTraceAdjoint.value seed M time)+
      NativeWindowStageNineSource.forcing seed M time =
    NativeWindowTraceAdjoint.forward seed M time (centered seed M frame time)+
      (NativeWindowStageNineSource.forcing seed M time+
        NativeWindowTraceAdjoint.forward seed M time (meanValue seed M frame)) := by
  rw [centered,map_sub]
  abel

theorem source_tensor_rate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ radius ≥ low,∀ outerRadius M observation frame
      (test : physicalSpace (modes M)) a b (ab : a ≤ b),
      ∀ᵐ time : ℝ,time∈Ioo a b →time∈Ioo 0 horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test a b ab
      let u := NativeWindowTraceAdjoint.value seed M time
      let v := centered seed M frame time
      let z := lifted seed M F radius time (p time)
      HasDerivAt (fun t => tensor seed M F radius frame t (p t))
        (pairTensor M (NativeWindowTraceAdjoint.forward seed M time u+
          NativeWindowStageNineSource.forcing seed M time) z+
          pairTensor M v (liftedRate seed M F radius time (p time)
            (load (nu := nu) observation M test time))) time := by
  obtain ⟨low,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M observation frame test a b ab => ?_⟩
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,
    NativeWindowTraceAdjoint.source_action_ae seed M] with time actual source physical clock
  let F := integerWaveFrequencyCube outerRadius
  let p := response seed M observation test a b ab
  have du := (NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual
  change HasDerivAt (NativeWindowTraceAdjoint.value seed M) _ time at du
  rw [source clock.1.le] at du
  have dv := du.sub_const (meanValue seed M frame)
  have dp := (response_derivative seed M observation test a b ab time
    (Ioo_subset_Icc_self physical)).hasDerivAt (Icc_mem_nhds physical.1 physical.2)
  have dz := lifted_hasDerivAt seed M F radius horizon time clock
    (inverted radius above M F (NativeWindowFiniteGramFourier.cube_closed outerRadius)) dp
  exact pairTensor_hasDerivAt M dv dz

end
end SaturationMonoid.NavierStokes.NativeCenteredResponseTensor
