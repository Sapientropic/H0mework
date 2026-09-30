import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.KernelLift
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.PairTrace
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.PotentialWork

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeResponseKernelLift
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint (response load testAction)
open NativeDistributedSourceTest (sourceTest)
open NativeForwardWindowSource (kernel)
open NativeResponseTensorPayment (pairTensor pairTensorCLM pairTensorCLM_apply)
open NativeWindowTraceDualEvolution (mass inverse lifted)
open NativeCenteredResponseTensor (centered)
open NativeWindowHistorySpatialTransport (finite)
open NativeCommonAdvectorAction (curlPair)
noncomputable section
variable {nu : Viscosity}

def traceCost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame time : ℝ) (w : physicalSpace (modes M)) : ℝ :=
  ∑ j : Coordinate,‖pairTensor M (centered seed M frame time) (finite M j (lifted seed M F radius time w))‖^2

private theorem curl_moment (M : ℕ) (v : physicalSpace (modes M)) :
    curlPair (modes M) v.1 v.1 ≤
      (2*Real.pi)^2*NativeWindowHistoryAdjointSpatialHalf.moment (modes M) 2 v := by
  rw [NativeWindowHistoryCreationGeometry.curl_mass (modes M) (modes_zero M),
    NativeWindowHistoryAdjointSpatialHalf.moment_original]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  simp only [show 2*(2 : ℕ)=4 from rfl,NativeUnheatedSexticLatticePower.radical_fourth,
    NativeUnheatedSexticLatticePower.mass]
  linarith

theorem source_kernel_correction_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ radius≥low,∀ outerRadius≤radius,∀ M observation,
      ∀ frame∈Icc 0 horizon,∀ᵐ time : ℝ,time∈Icc 0 horizon →∀ test : physicalSpace (modes M),
        traceCost seed M (integerWaveFrequencyCube outerRadius) radius frame time
          (amplitude nu observation time • test) ≤
        C*kernel (observation-time)^2*(1+NativeUnheatedSourceGradient.mass seed time)*
          ‖coefficients (modes M) test‖^2 := by
  obtain ⟨low,C,C0,trace⟩ := NativeResponsePairTrace.source_pair_trace seed horizon nonnegative
  obtain ⟨V,V0,centeredPaid⟩ := NativeCenteredPotentialPayment.centered_moment seed horizon
  refine ⟨low,C*(2*Real.pi)^2*V/nu.coeff^2,by positivity,
    fun radius above outerRadius covered M observation frame framed => ?_⟩
  filter_upwards [centeredPaid frame framed] with time vc inside test
  have curl := (curl_moment M (centered seed M frame time)).trans
    (mul_le_mul_of_nonneg_left (vc inside.1 M) (sq_nonneg (2*Real.pi)))
  have paid := trace radius above outerRadius covered M time inside
    (centered seed M frame time) (amplitude nu observation time • test)
  have scaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left curl C0)
    (sq_nonneg ‖coefficients (modes M) (amplitude nu observation time • test)‖)
  apply paid.trans (scaled.trans_eq ?_)
  simp only [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,amplitude]
  ring

private theorem norm_add_square {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x+y‖^2≤2*‖x‖^2+2*‖y‖^2 := by
  have first := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith only [first,sq_nonneg (‖x‖-‖y‖)]

theorem traceCost_response_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (observation frame time : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a≤b) :
    traceCost seed M F radius frame time (response seed M observation test a b ab time) ≤
      2*traceCost seed M F radius frame time (kernelLift seed M observation test a b ab time)+
      2*traceCost seed M F radius frame time (amplitude nu observation time • test) := by
  rw [response_restore]
  simp only [traceCost,lifted,map_add,← pairTensorCLM_apply,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_square _ _

private theorem traceCost_continuousOn (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (frame : ℝ) {S : Set ℝ}
    {w : ℝ→physicalSpace (modes M)} (wc : ContinuousOn w S)
    (generated : ∀ t∈S,(mass seed M F radius t).IsInvertible) :
    ContinuousOn (fun t => traceCost seed M F radius frame t (w t)) S := by
  have ic : ContinuousOn (inverse seed M F radius) S := fun t ht =>
    (NativeWindowTraceDualEvolution.inverse_differentiableAt seed M F radius t
      (generated t ht)).continuousAt.continuousWithinAt
  have vc : ContinuousOn (centered seed M frame) S :=
    (NativeWindowTraceAdjoint.value_continuous seed M).continuousOn.sub continuousOn_const
  exact continuousOn_finsetSum _ fun j _ =>
    (((pairTensorCLM M).continuous.comp_continuousOn vc).clm_apply
      ((finite M j).continuous.comp_continuousOn (ic.clm_apply wc))).norm.pow 2

theorem source_kernel_integral_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) (rate : ℝ) (rate0 : 0≤rate) :
    ∃ low : ℕ,∃ K : ℝ,0≤K ∧∀ radius≥low,∀ outerRadius≤radius,∀ M observation,
      ∀ frame∈Icc 0 horizon,∀ test : physicalSpace (modes M),∀ b,0≤b →b≤horizon →
        (∫ time in (0 : ℝ)..b,Real.exp (rate*time)*
          traceCost seed M (integerWaveFrequencyCube outerRadius) radius frame time
            (amplitude nu observation time • test)) ≤ K*‖coefficients (modes M) test‖^2 := by
  obtain ⟨first,D,D0,point⟩ := source_kernel_correction_paid seed horizon nonnegative
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  let k := NativeWindowFiniteStressUniform.kernelBound 0
  let s := fun t => 1+NativeUnheatedSourceGradient.mass seed t
  let B := ∫ t in (0 : ℝ)..horizon,s t
  have si : IntervalIntegrable s volume 0 horizon :=
    intervalIntegrable_const.add ((intervalIntegrable_iff_integrableOn_Icc_of_le nonnegative).mpr
      (NativeUnheatedSourceGradient.mass_integrable seed horizon nonnegative))
  have s0 (t : ℝ) : 0 ≤ s t := add_nonneg zero_le_one (NativeUnheatedSourceGradient.mass_nonnegative seed t)
  have B0 : 0≤B := intervalIntegral.integral_nonneg nonnegative (fun t _ => s0 t)
  refine ⟨max first last,D*k^2*Real.exp (rate*horizon)*B,by positivity,
    fun radius above outerRadius covered M observation frame framed test b ordered within => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let n := ‖coefficients (modes M) test‖^2
  have generated := inverted radius ((le_max_right first last).trans above) M F
    (NativeWindowFiniteGramFourier.cube_closed outerRadius)
  have ac : Continuous (fun t => amplitude nu observation t • test) :=
    ((NativeForwardWindowSource.kernel_smooth.continuous.comp (continuous_const.sub continuous_id)).div_const _).smul continuous_const
  have tc := traceCost_continuousOn seed M F radius frame ac.continuousOn
    (fun t ht => generated t (Icc_subset_Icc le_rfl within ht))
  have ec : Continuous (fun t : ℝ => Real.exp (rate*t)) := by fun_prop
  have ti := (ec.continuousOn.mul tc).intervalIntegrable_of_Icc (μ := volume) ordered
  have subi : IntervalIntegrable s volume 0 b := si.mono_set (by
    rw [uIcc_of_le ordered,uIcc_of_le nonnegative]
    exact Icc_subset_Icc le_rfl within)
  have gi := subi.const_mul (D*k^2*Real.exp (rate*horizon)*n)
  have paid := intervalIntegral.integral_mono_ae_restrict ordered ti gi ?_
  · rw [intervalIntegral.integral_const_mul] at paid
    have mono := intervalIntegral.integral_mono_interval le_rfl ordered within
      (Eventually.of_forall s0) si
    have scaled := mul_le_mul_of_nonneg_left mono
      (show 0≤D*k^2*Real.exp (rate*horizon)*n by dsimp only [n]; positivity)
    exact paid.trans (scaled.trans_eq (by dsimp only [B,n]; ring))
  · filter_upwards [ae_restrict_of_ae
        (point radius ((le_max_left first last).trans above) outerRadius covered M observation frame framed),
      ae_restrict_mem measurableSet_Icc] with t bound inside
    have actual := bound (Icc_subset_Icc le_rfl within inside) test
    have kb := NativeWindowFiniteStressUniform.kernel_bounded 0 (observation-t)
    simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero,Real.norm_eq_abs] at kb
    have ks : kernel (observation-t)^2≤k^2 := sq_le_sq.mpr (by
      simpa only [k,abs_of_pos (NativeWindowFiniteStressUniform.kernelBound_positive 0)] using kb)
    have cap := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ks D0) (s0 t))
      (sq_nonneg ‖coefficients (modes M) test‖)
    have exponent := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (inside.2.trans within) rate0)
    have weight := mul_le_mul exponent (actual.trans cap)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Real.exp_pos (rate*horizon)).le
    exact weight.trans_eq (by dsimp only [n,s]; ring)

theorem source_test_trace_recovery (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) (rate : ℝ) (rate0 : 0≤rate) :
    ∃ low : ℕ,∃ K : ℝ,0≤K ∧∀ radius≥low,∀ outerRadius≤radius,∀ M observation,
      ∀ (observation0 : 0≤observation),observation+2≤horizon →
      let F := integerWaveFrequencyCube outerRadius
      let test := sourceTest seed M observation
      let p := response seed M observation test 0 (observation+2) (by linarith)
      let q := kernelLift seed M observation test 0 (observation+2) (by linarith)
      (∫ time in (0 : ℝ)..(observation+2),Real.exp (rate*time)*
        traceCost seed M F radius observation time (p time)) ≤
      2*(∫ time in (0 : ℝ)..(observation+2),Real.exp (rate*time)*
        traceCost seed M F radius observation time (q time))+K*‖coefficients (modes M) test‖^2 := by
  obtain ⟨first,D,D0,correction⟩ := source_kernel_integral_paid seed horizon nonnegative rate rate0
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  refine ⟨max first last,2*D,by positivity,fun radius above outerRadius covered M observation observation0 within => ?_⟩
  dsimp only
  let F := integerWaveFrequencyCube outerRadius
  let test := sourceTest seed M observation
  have ordered : 0≤observation+2 := by linarith
  let p := response seed M observation test 0 (observation+2) ordered
  let q := kernelLift seed M observation test 0 (observation+2) ordered
  let c := fun t => amplitude nu observation t • test
  have generated := fun t ht => inverted radius ((le_max_right first last).trans above) M F
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) t (Icc_subset_Icc le_rfl within ht)
  have pc := NativeWindowDistributedAdjoint.response_continuous seed M observation test 0 (observation+2) ordered
  have cc : Continuous c := continuous_iff_continuousAt.mpr fun t =>
    ((amplitude_derivative (nu := nu) observation t).smul_const test).continuousAt
  have qc : ContinuousOn q (Icc 0 (observation+2)) := pc.sub cc.continuousOn
  have ec : Continuous (fun t : ℝ => Real.exp (rate*t)) := by fun_prop
  have pi := (ec.continuousOn.mul (traceCost_continuousOn seed M F radius observation pc generated)).intervalIntegrable_of_Icc
    (μ := volume) ordered
  have qi := (ec.continuousOn.mul (traceCost_continuousOn seed M F radius observation qc generated)).intervalIntegrable_of_Icc
    (μ := volume) ordered
  have ci := (ec.continuousOn.mul (traceCost_continuousOn seed M F radius observation cc.continuousOn generated)).intervalIntegrable_of_Icc
    (μ := volume) ordered
  have split := intervalIntegral.integral_mono_on ordered pi ((qi.const_mul 2).add (ci.const_mul 2)) ?_
  · rw [intervalIntegral.integral_add (qi.const_mul 2) (ci.const_mul 2),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at split
    have paid := correction radius ((le_max_left first last).trans above) outerRadius covered M observation
      observation ⟨observation0,by linarith⟩ test (observation+2) ordered within
    dsimp only [p,q,c,F,test,Pi.mul_apply] at split paid ⊢
    linarith only [split,paid]
  · intro t _
    have split := mul_le_mul_of_nonneg_left
      (traceCost_response_split seed M F radius observation observation t test 0 (observation+2) ordered)
      (Real.exp_pos (rate*t)).le
    convert! split using 1
    dsimp only [Pi.add_apply,Pi.mul_apply,p,q,c]
    ring

end
end SaturationMonoid.NavierStokes.NativeResponseKernelLift
