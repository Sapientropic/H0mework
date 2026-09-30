import H0mework.NavierStokes.WindowEnergyAugmented.HierarchySource
import H0mework.NavierStokes.WindowStressHeat.Time

set_option autoImplicit false
open scoped BigOperators Topology Convolution ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHierarchyPairWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeResolventCompactness NativeUnheatedGlobalNegativeOne NativeUnheatedIntegralBilinear
open NativeUnheatedStressPairEvolution NativeUnheatedPairGlobalWindow NativeForwardWindowJets
noncomputable section
variable {nu : Viscosity}

theorem state_before (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (before : time ≤ 0) :
    state seed time=state seed 0 := by
  simp only [state,NativeWindowPreparationSource.complete_nonpositive seed time before]

theorem rate_before (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (before : time < 0) :
    rate seed time=0 := by simp only [rate,dif_neg (not_le.mpr before)]

theorem state_continuous (seed : GeneratedWholeRestartCurrent nu) : Continuous (state seed) := by
  have clipped : Continuous (fun time => state seed (max 0 time)) :=
    (state_continuousOn seed).comp_continuous (continuous_const.max continuous_id) (fun time => le_max_left 0 time)
  convert clipped using 1
  funext time
  by_cases positive : 0 ≤ time
  · rw [max_eq_right positive]
  · rw [max_eq_left (le_of_not_ge positive),state_before seed time (le_of_not_ge positive)]

theorem rate_integrable_total (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) :
    IntervalIntegrable (rate seed) volume a b := by
  let H:=max 0 (max a b)
  have paid : Integrable ((Icc 0 H).indicator (rate seed)) (volume : Measure ℝ) :=
    (integrable_indicator_iff measurableSet_Icc).2 (rate_integrable seed H (le_max_left _ _))
  have same : (rate seed)=ᵐ[volume.restrict (uIcc a b)] (Icc 0 H).indicator (rate seed) := by
    filter_upwards [ae_restrict_mem measurableSet_uIcc] with time inside
    by_cases positive : 0 ≤ time
    · have member : time∈Icc 0 H := ⟨positive,inside.2.trans (le_max_right _ _)⟩
      rw [indicator_of_mem member]
    · rw [indicator_of_notMem (fun member => positive member.1),rate_before seed time (lt_of_not_ge positive)]
  have localPaid : IntegrableOn (rate seed) (uIcc a b) (volume : Measure ℝ) := paid.integrableOn.congr same.symm
  exact localPaid.intervalIntegrable

theorem source_from_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    state seed time-state seed 0=∫sample in 0..time,rate seed sample := by
  by_cases positive : 0 ≤ time
  · exact source_integral seed 0 time le_rfl positive
  · rw [state_before seed time (le_of_not_ge positive),sub_self]
    have zero : (∫sample in 0..time,rate seed sample)=(∫sample in 0..time,(0 : State)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with sample unequal inside
      have upper : sample ≤ 0 := by simpa only [max_eq_left (le_of_not_ge positive)] using inside.2
      exact rate_before seed sample (lt_of_le_of_ne upper unequal)
    rw [zero,intervalIntegral.integral_zero]

theorem source_write_total (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) :
    state seed b-state seed a=∫sample in a..b,rate seed sample := by
  calc
    _=(state seed b-state seed 0)-(state seed a-state seed 0) := by abel
    _=(∫sample in 0..b,rate seed sample)-(∫sample in 0..a,rate seed sample) := by rw [source_from_zero,source_from_zero]
    _=_ := intervalIntegral.integral_interval_sub_left (rate_integrable_total seed 0 b) (rate_integrable_total seed 0 a)

theorem state_ac_total (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (state seed) a b :=
  written_ac _ _ (rate_integrable_total seed a b) (fun x _ y _ => source_write_total seed x y)

theorem source_derivative_total (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ,HasDerivAt (state seed) (rate seed time) time := by
  filter_upwards [source_hasDerivAt_ae seed,(volume : Measure ℝ).ae_ne 0] with time positive unequal
  by_cases above : 0 < time
  · exact positive above
  · have before : time < 0 := lt_of_le_of_ne (le_of_not_gt above) unequal
    rw [rate_before seed time before]
    apply (hasDerivAt_const time (state seed 0)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds before] with sample negative
    exact state_before seed sample negative.le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def pair (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E) (sample : ℝ) : E :=
  B (state seed sample) (state seed sample)

def action (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E) (sample : ℝ) : E :=
  B (rate seed sample) (state seed sample)+B (state seed sample) (rate seed sample)

omit [CompleteSpace E] in
theorem pair_continuous (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E) :
    Continuous (pair seed B) := (B.continuous.comp (state_continuous seed)).clm_apply (state_continuous seed)

omit [CompleteSpace E] in
theorem pair_ac (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (pair seed B) a b := diagonal_ac B (state_ac_total seed a b)

omit [CompleteSpace E] in
theorem pair_derivative (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E) :
    ∀ᵐ sample : ℝ,HasDerivAt (pair seed B) (action seed B sample) sample := by
  filter_upwards [source_derivative_total seed] with sample actual
  simpa only [pair,action,Function.comp_def] using! (B.hasFDerivAt.comp_hasDerivAt sample actual).clm_apply actual

omit [CompleteSpace E] in
theorem action_integrable (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E) (a b : ℝ) :
    IntervalIntegrable (action seed B) volume a b := by
  let bound:=NativeUnifiedCompleteSource.budget seed
  have bounded := NativeUnheatedSourceWeightedTail.state_bound seed
  have normed (sample : ℝ) : ‖action seed B sample‖≤(2*‖B‖*bound)*‖rate seed sample‖ := by
    apply (norm_add_le _ _).trans
    have first := (B.le_opNorm₂ (rate seed sample) (state seed sample)).trans
      (mul_le_mul_of_nonneg_left (bounded sample) (mul_nonneg (norm_nonneg B) (norm_nonneg _)))
    have last := (B.le_opNorm₂ (state seed sample) (rate seed sample)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bounded sample) (norm_nonneg B)) (norm_nonneg _))
    exact (add_le_add first last).trans_eq (by ring)
  have measured : AEStronglyMeasurable (action seed B) (volume.restrict (uIoc a b)) :=
    (B.aestronglyMeasurable_comp₂ (rate_integrable_total seed a b).def'.aestronglyMeasurable
      (state_continuous seed).aestronglyMeasurable.restrict).add
      (B.aestronglyMeasurable_comp₂ (state_continuous seed).aestronglyMeasurable.restrict
        (rate_integrable_total seed a b).def'.aestronglyMeasurable)
  apply intervalIntegrable_iff.mpr
  exact ((rate_integrable_total seed a b).def'.norm.const_mul (2*‖B‖*bound)).mono' measured (Eventually.of_forall normed)

def window (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E) (order : ℕ) : ℝ → E :=
  kernelJet order ⋆[ContinuousLinearMap.lsmul ℝ ℝ] pair seed B

omit [CompleteSpace E] in
theorem window_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E)
    (order : ℕ) (observation : ℝ) : HasDerivAt (window seed B order) (window seed B (order+1) observation) observation := by
  have localPaid : LocallyIntegrable (pair seed B) (volume : Measure ℝ) := (pair_continuous seed B).locallyIntegrable
  have original := (kernelJet_compact order).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth order).of_le (by simp)) localPaid observation
  simpa only [window,kernelJet,iteratedDeriv_succ] using original

omit [CompleteSpace E] in
theorem window_original (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E)
    (order : ℕ) (observation : ℝ) : window seed B order observation=
      ∫sample in observation+1..observation+2,kernelWeight order observation 0 sample • pair seed B sample :=
  NativeWindowStressHeatTime.kernel_integral _ _ _

theorem window_write (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E)
    (order : ℕ) (observation : ℝ) : window seed B (order+1) observation=
      ∫sample in observation+1..observation+2,kernelWeight order observation 0 sample • action seed B sample := by
  have base := (pair_continuous seed B).intervalIntegrable (μ := volume) (a := observation+1) (b := observation+2)
  have p (n : ℕ) := base.continuousOn_smul (kernelWeight_continuous n observation 0).continuousOn
  have q := (action_integrable seed B (observation+1) (observation+2)).continuousOn_smul
    (kernelWeight_continuous order observation 0).continuousOn
  have written : kernelWeight order observation 0 (observation+2) • pair seed B (observation+2)-
      kernelWeight order observation 0 (observation+1) • pair seed B (observation+1)=
      ∫sample in observation+1..observation+2,kernelWeight order observation 0 sample • action seed B sample-
        kernelWeight (order+1) observation 0 sample • pair seed B sample := by
    apply integral_of_ac_derivative _ _
      ((kernel_ac order observation 0 (observation+1) (observation+2)).smul (pair_ac seed B (observation+1) (observation+2))) (q.sub (p (order+1)))
    filter_upwards [pair_derivative seed B] with sample actual _
    convert! (kernelWeight_hasDerivAt order observation 0 sample).smul actual using 1
    simp only [neg_smul]
    abel
  have left : kernelWeight order observation 0 (observation+1)=0 := by
    simp only [kernelWeight,zero_add,show observation-(observation+1)=(-1:ℝ) by ring,kernelJet_right_zero]
  have right : kernelWeight order observation 0 (observation+2)=0 := by
    simp only [kernelWeight,zero_add,show observation-(observation+2)=(-2:ℝ) by ring,kernelJet_left_zero]
  simp only [left,right,zero_smul,sub_self] at written
  rw [intervalIntegral.integral_sub q (p (order+1))] at written
  rw [window_original]
  exact (sub_eq_zero.mp written.symm).symm

theorem window_initial (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E)
    (observation : ℝ) (before : observation ≤ -2) : window seed B 0 observation=pair seed B 0 := by
  change (∫shift : ℝ,NativeForwardWindowSource.kernel shift • pair seed B (observation-shift))=_
  calc
    _=(∫shift : ℝ,NativeForwardWindowSource.kernel shift • pair seed B 0) := by
      apply integral_congr_ae
      filter_upwards with shift
      by_cases zero : NativeForwardWindowSource.kernel shift=0
      · simp only [zero,zero_smul]
      · have past : observation-shift ≤ 0 := by linarith [(NativeViewPreparation.kernel_window shift zero).1]
        simp only [pair,state_before seed (observation-shift) past]
    _=_ := by rw [integral_smul_const,NativeForwardWindowSource.kernel_mass,one_smul]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

omit [CompleteSpace E] in
theorem window_next (seed : GeneratedWholeRestartCurrent nu) (B : State →L[ℝ] State →L[ℝ] E) (order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (observation : ℝ) (nonnegative : 0 ≤ observation) :
    window seed B order (step.2.clockAdvance+observation)=window step.1 B order observation := by
  change (∫shift : ℝ,kernelJet order shift • pair seed B (step.2.clockAdvance+observation-shift))=
    ∫shift : ℝ,kernelJet order shift • pair step.1 B (observation-shift)
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernelJet order shift=0
  · simp only [zero,zero_smul]
  · simp only [pair,add_sub_assoc,state_next seed step generated (observation-shift)
      (by linarith [kernelJet_nonpositive order shift zero])]

end
end SaturationMonoid.NavierStokes.NativeWindowHierarchyPairWindow
