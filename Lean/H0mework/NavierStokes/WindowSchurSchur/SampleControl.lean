import H0mework.NavierStokes.WindowSchurSchur.Completion
import H0mework.NavierStokes.WindowHistory.Gradient

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurSampleControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action rateHistory forcingHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistorySchurAction (remainder)
open NativeWindowHistorySchurCompletion (completion commonForce)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

theorem pairing_scale (M : ℕ) (v : physicalSpace (modes M)) (s : ℝ) :
    pairing (modes M) (s • v) (s • v)=s^2*pairing (modes M) v v := by
  change inner ℝ (coefficients (modes M) (s • v)) (coefficients (modes M) (s • v))=
    s^2*inner ℝ (coefficients (modes M) v) (coefficients (modes M) v)
  rw [map_smul,real_inner_smul_left,real_inner_smul_right]
  ring

theorem gradient_scale (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) (s : ℝ) :
    curlPair (modes M) (s • v).1 (s • v).1=s^2*curlPair (modes M) v.1 v.1 := by
  rw [← NativeWindowOperatorGreen.laplacian_pairing (modes M) (modes_zero M) (modes_closed M) nu,
    ← NativeWindowOperatorGreen.laplacian_pairing (modes M) (modes_zero M) (modes_closed M) nu v v]
  change inner ℝ (coefficients (modes M) (s • v))
    (coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu (s • v)))=
    s^2*inner ℝ (coefficients (modes M) v)
      (coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v))
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right]
  ring

theorem gradient_nonnegative (M : ℕ) (v : physicalSpace (modes M)) : 0 ≤ curlPair (modes M) v.1 v.1 := by
  rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
  exact sq_nonneg _

private theorem rescaled_bound (n C : ℝ) (n0 : 0 < n) (C0 : 0 ≤ C) (m g p : ℝ) (m0 : 0 ≤ m) (g0 : 0 ≤ g)
    (bound : (4*(C+1))⁻¹*|p| ≤ (n/4)*((4*(C+1))⁻¹)^2*g+C*(((4*(C+1))⁻¹)^2*m+1)) :
    |p| ≤ (n/4)*g+(1/4 : ℝ)*m+C*(4*(C+1)) := by
  let d:=4*(C+1)
  have d0:0 < d:=by dsimp only [d]; linarith
  have s0:0 ≤ d⁻¹:=inv_nonneg.mpr d0.le
  have normalized:d*d⁻¹=1:=mul_inv_cancel₀ d0.ne'
  have s1:d⁻¹ ≤ 1 := by dsimp only [d] at normalized; nlinarith [mul_nonneg C0 s0]
  have Cs:C*d⁻¹ ≤ 1/4 := by dsimp only [d] at normalized; nlinarith only [normalized,s0]
  have paid:=mul_le_mul_of_nonneg_left bound d0.le
  change d*(d⁻¹*|p|) ≤ d*((n/4)*(d⁻¹)^2*g+C*((d⁻¹)^2*m+1)) at paid
  have left:d*(d⁻¹*|p|)=|p|:=by rw [← mul_assoc,normalized,one_mul]
  have right:d*((n/4)*(d⁻¹)^2*g+C*((d⁻¹)^2*m+1))=(n/4)*d⁻¹*g+C*d⁻¹*m+C*d := by field_simp [d0.ne']; ring
  rw [left,right] at paid
  apply paid.trans
  have first:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s1 (by positivity : 0 ≤ n/4)) g0
  have last:=mul_le_mul_of_nonneg_right Cs m0
  linarith only [first,last]

theorem source_common_force_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ D : ℝ,0 ≤ D ∧∀ M ≥ low,∀ time∈Icc 0 horizon,∀ v : physicalSpace (modes M),
      |inner ℝ (includeCLM (modes M) (modes_closed M) v) (commonForce seed M time)| ≤
        (1/2 : ℝ)*pairing (modes M) v v+(nu.coeff/4)*curlPair (modes M) v.1 v.1+D := by
  obtain ⟨low,C,C0,paid⟩:=NativeWindowHistorySchurTemporalControl.source_remainder_bound seed horizon nonnegative
    (nu.coeff/4) (div_pos nu.coeff_pos (by norm_num))
  let B:=NativeForwardWindowJets.budget seed 0+NativeForwardWindowJets.budget seed 1
  refine ⟨low,C*(4*(C+1))+B^2,by positivity,fun M above time inside v => ?_⟩
  let s:=(4*(C+1))⁻¹
  have s0:0 ≤ s:=by dsimp only [s]; positivity
  have source:=paid M above time inside (s • v)
  rw [map_smul,real_inner_smul_left (F := wholePhysical),abs_mul,abs_of_nonneg s0,pairing_scale,gradient_scale nu] at source
  have rem:=rescaled_bound nu.coeff C nu.coeff_pos C0 (pairing (modes M) v v) (curlPair (modes M) v.1 v.1)
    (inner ℝ (includeCLM (modes M) (modes_closed M) v) (remainder seed M time))
    (real_inner_self_nonneg (x := coefficients (modes M) v)) (gradient_nonnegative M v)
      (by simpa only [s,mul_assoc] using source)
  have meanBound:‖mean (finiteHistory seed time M)‖ ≤ NativeForwardWindowJets.budget seed 0 := by
    change ‖(mean (finiteHistory seed time M)).1‖ ≤ _
    rw [NativeWindowHistoryMeanTime.source_mean]
    exact NativeWindowHistoryMeanTime.jet_bound seed M 0 time
  have difference:‖mean (finiteHistory seed time M)-mean (rateHistory seed M time)‖ ≤ B :=
    (norm_sub_le _ _).trans (add_le_add meanBound (NativeWindowHistoryMeanTime.source_rate_bound seed M time))
  have cauchy:|inner ℝ (includeCLM (modes M) (modes_closed M) v)
      (mean (finiteHistory seed time M)-mean (rateHistory seed M time))| ≤
        ‖coefficients (modes M) v‖*B := by
    have bound:=(abs_real_inner_le_norm (includeCLM (modes M) (modes_closed M) v) _).trans
      (mul_le_mul_of_nonneg_left difference (norm_nonneg (includeCLM (modes M) (modes_closed M) v)))
    simpa only [include_norm (modes M) (modes_zero M)] using bound
  have first:|inner ℝ (includeCLM (modes M) (modes_closed M) v)
      (mean (finiteHistory seed time M)-mean (rateHistory seed M time))| ≤ (1/4 : ℝ)*pairing (modes M) v v+B^2 := by
    have mass:pairing (modes M) v v=‖coefficients (modes M) v‖^2:=real_inner_self_eq_norm_sq (coefficients (modes M) v)
    nlinarith only [cauchy,mass,sq_nonneg (‖coefficients (modes M) v‖/2-B)]
  unfold commonForce
  rw [inner_add_right]
  exact ((abs_add_le _ _).trans (add_le_add first rem)).trans_eq (by ring)

def sample (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) : physicalSpace (modes M) :=
  restrictCLM (modes M) (modes_zero M) (modes_closed M) (completion seed M time lag)

def sampleEnergy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) : ℝ :=
  pairing (modes M) (sample seed M time lag) (sample seed M time lag)+
    nu.coeff*curlPair (modes M) (sample seed M time lag).1 (sample seed M time lag).1

theorem sample_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) :
    0 ≤ sampleEnergy seed M time lag := add_nonneg
  (real_inner_self_nonneg (x := coefficients (modes M) (sample seed M time lag)))
    (mul_nonneg nu.coeff_pos.le (gradient_nonnegative M _))

theorem sample_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∀ᵐ lag ∂averageMeasure,sampleEnergy seed M time lag=
      inner ℝ (includeCLM (modes M) (modes_closed M) (sample seed M time lag)) (commonForce seed M time) := by
  filter_upwards [NativeWindowHistorySchurCompletion.completion_equation_ae seed M time] with lag actual
  let v:=sample seed M time lag
  have paired:=congrArg (fun x : wholePhysical => inner ℝ (includeCLM (modes M) (modes_closed M) v) x) actual
  rw [inner_sub_right,include_inner (modes M) (modes_zero M)] at paired
  have drift:inner ℝ (includeCLM (modes M) (modes_closed M) v)
      (NativeWindowHistoryOseen.forwardFiber seed M (time-lag) (completion seed M time lag))=
        -nu.coeff*curlPair (modes M) v.1 v.1 := by
    change inner ℝ (includeCLM (modes M) (modes_closed M) v)
      (includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.forward seed M (time-lag) v))=_
    rw [include_inner (modes M) (modes_zero M),restrict_include]
    exact physicalOperator_pairing (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.advector seed M (time-lag)) (NativeWindowTraceAdjoint.advector_reality seed M (time-lag)) v
  rw [drift] at paired
  change pairing (modes M) v v-(-nu.coeff*curlPair (modes M) v.1 v.1)=_ at paired
  exact (show sampleEnergy seed M time lag=pairing (modes M) v v-(-nu.coeff*curlPair (modes M) v.1 v.1) by
    change pairing (modes M) v v+nu.coeff*curlPair (modes M) v.1 v.1=_; ring).trans paired

theorem source_sample_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ∀ᵐ lag ∂averageMeasure,sampleEnergy seed M time lag ≤ C := by
  obtain ⟨low,D,D0,paid⟩:=source_common_force_bound seed horizon nonnegative
  refine ⟨low,2*D,by positivity,fun M above time inside => ?_⟩
  filter_upwards [sample_equation seed M time] with lag actual
  have bound:=(le_abs_self _).trans (paid M above time inside (sample seed M time lag))
  rw [← actual] at bound
  have g0:=gradient_nonnegative M (sample seed M time lag)
  have v0:0 ≤ pairing (modes M) (sample seed M time lag) (sample seed M time lag) :=
    real_inner_self_nonneg (x := coefficients (modes M) (sample seed M time lag))
  unfold sampleEnergy at bound ⊢
  nlinarith only [bound,mul_nonneg nu.coeff_pos.le g0,v0]

theorem sample_include (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∀ᵐ lag ∂averageMeasure,includeCLM (modes M) (modes_closed M) (sample seed M time lag)=completion seed M time lag := by
  filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL (completion seed M time)] with lag actual
  have same:=congrArg (fun h : H => h lag) (NativeWindowHistorySchurCompletion.completion_projected seed M time)
  exact actual.symm.trans same

theorem sample_energy_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Integrable (sampleEnergy seed M time) averageMeasure := by
  have projected:MemLp (sample seed M time) 2 averageMeasure :=
    (Lp.memLp (completion seed M time)).continuousLinearMap_comp (restrictCLM (modes M) (modes_zero M) (modes_closed M))
  have coefficient:=projected.continuousLinearMap_comp (LinearMap.toContinuousLinearMap (coefficients (modes M)))
  have mass:Integrable (fun lag => pairing (modes M) (sample seed M time lag) (sample seed M time lag)) averageMeasure := by
    apply (coefficient.integrable_norm_pow (by decide : (2 : ℕ)≠0)).congr
    filter_upwards with lag
    exact (real_inner_self_eq_norm_sq (coefficients (modes M) (sample seed M time lag))).symm
  have grad:Integrable (fun lag => curlPair (modes M) (sample seed M time lag).1 (sample seed M time lag).1) averageMeasure :=
    NativeWindowTraceWholeHistory.gradient_integrable nu M (completion seed M time)
  exact mass.add (grad.const_mul nu.coeff)

theorem sample_energy_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∀ᵐ lag ∂averageMeasure,sampleEnergy seed M time lag=‖completion seed M time lag‖^2+
      nu.coeff*curlPair (modes M) (sample seed M time lag).1 (sample seed M time lag).1 := by
  filter_upwards [sample_include seed M time] with lag actual
  have mass:=congrArg (fun h : wholePhysical => ‖h‖^2) actual
  rw [include_norm (modes M) (modes_zero M)] at mass
  have original:pairing (modes M) (sample seed M time lag) (sample seed M time lag)=‖completion seed M time lag‖^2 :=
    (real_inner_self_eq_norm_sq (coefficients (modes M) (sample seed M time lag))).trans mass
  exact congrArg (fun x : ℝ => x+nu.coeff*curlPair (modes M) (sample seed M time lag).1 (sample seed M time lag).1) original

theorem source_weighted_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      Integrable (fun lag => NativeUnheatedSourceGradient.mass seed (time-lag)*sampleEnergy seed M time lag) averageMeasure ∧
      (∫lag,NativeUnheatedSourceGradient.mass seed (time-lag)*sampleEnergy seed M time lag ∂averageMeasure) ≤
        C*(∫lag,NativeUnheatedSourceGradient.mass seed (time-lag) ∂averageMeasure) ∧
      (∫lag,NativeUnheatedSourceGradient.mass seed (time-lag)*sampleEnergy seed M time lag ∂averageMeasure) ≤
        C*NativeWindowHistoryGradient.ceiling*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2) := by
  obtain ⟨low,C,C0,paid⟩:=source_sample_bound seed horizon nonnegative
  refine ⟨low,C,C0,fun M above time inside => ?_⟩
  have valid:-1 ≤ time:=by linarith [inside.1]
  have gPaid:=NativeWindowHistoryGradient.weighted_mass_integrable seed time valid
  have energyPaid:=sample_energy_integrable seed M time
  have dominated:∀ᵐ lag ∂averageMeasure,‖NativeUnheatedSourceGradient.mass seed (time-lag)*sampleEnergy seed M time lag‖ ≤
      C*NativeUnheatedSourceGradient.mass seed (time-lag) := by
    filter_upwards [paid M above time inside] with lag bound
    have mass0:=NativeUnheatedSourceGradient.mass_nonnegative seed (time-lag)
    rw [Real.norm_of_nonneg (mul_nonneg mass0 (sample_nonnegative seed M time lag))]
    exact (mul_le_mul_of_nonneg_left bound mass0).trans_eq (mul_comm _ _)
  have integrable:Integrable (fun lag => NativeUnheatedSourceGradient.mass seed (time-lag)*sampleEnergy seed M time lag) averageMeasure :=
    (gPaid.const_mul C).mono' (gPaid.aestronglyMeasurable.mul energyPaid.aestronglyMeasurable) dominated
  have bounded:=integral_mono_ae integrable (gPaid.const_mul C) (by
    filter_upwards [dominated] with lag bound
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le bound))
  rw [integral_const_mul] at bounded
  refine ⟨integrable,bounded,?_⟩
  exact bounded.trans ((mul_le_mul_of_nonneg_left (NativeWindowHistoryGradient.weighted_mass_bound seed time valid) C0).trans_eq (by ring))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem sample_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    sampleEnergy seed M (step.2.clockAdvance+time)=sampleEnergy step.1 M time := by
  funext lag
  simp only [sampleEnergy,sample,NativeWindowHistorySchurCompletion.completion_next seed M step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurSampleControl
