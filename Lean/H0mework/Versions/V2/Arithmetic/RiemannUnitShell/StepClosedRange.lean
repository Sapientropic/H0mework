import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.OrbitSmoothing

/-! Actual compact-source approximations generate the reciprocal step wave in the original Pa closed range. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem burnolReciprocalStepSmoothedSource_realizes (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperBound : upper ≤ 4)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead ((burnolReciprocalStepSmoothedSource pulse lower upper).toLp 2 volume) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolReciprocalStepSmoothedValue pulse (burnolReciprocalStepWaveL2 lower upper lowerPositive ordered))) test := by
  rw [burnolReciprocalStepSmoothedSource_toLp pulse lower upper lowerPositive ordered,
    burnolReciprocalStepSmoothedValue_integral, burnolReciprocalStepSmoothedValue_integral]
  exact burnolRemainderSourceRead_dilation_average (pulse.normed volume) (fun h => -h)
    (burnolReciprocalStepSourceL2 lower upper lowerPositive ordered)
    (burnolReciprocalStepWaveL2 lower upper lowerPositive ordered)
    (burnolReciprocalStepSource_realizes lower upper lowerPositive ordered upperBound)
    (burnolReciprocalStepSmoothOrbit_integrable pulse _) (burnolReciprocalStepSmoothOrbit_integrable pulse _) test

theorem burnolReciprocalStepSmoothedValue_generator (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperBound : upper ≤ 4)
    (innerMargin : (1 / 4 : ℝ) ≤ Real.exp (-Real.log upper - pulse.rOut))
    (outerMargin : Real.exp (-Real.log lower + pulse.rOut) ≤ 4) :
    burnolReciprocalStepSmoothedValue pulse (burnolReciprocalStepWaveL2 lower upper lowerPositive ordered) =
      (burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource
        (burnolReciprocalStepAnnulusSmoothedSource pulse lower upper innerMargin outerMargin)) : BurnolL2) := by
  let smooth := burnolReciprocalStepAnnulusSmoothedSource pulse lower upper innerMargin outerMargin
  let compact := burnolCompactTateReciprocalSource smooth
  have sourceRead : burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState compact) =
      (burnolReciprocalStepSmoothedSource pulse lower upper).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [burnolMobiusSourceExtension_compact_coeFn compact,
      (burnolReciprocalStepSmoothedSource pulse lower upper).coeFn_toLp 2 volume] with x compactAt smoothAt
    change burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState compact) x =
      burnolCompactAdditiveSource compact x at compactAt
    rw [compactAt, smoothAt]
    exact burnolCompactTateReciprocalSource_additiveSource smooth x
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (burnolReciprocalStepSmoothedValue pulse (burnolReciprocalStepWaveL2 lower upper lowerPositive ordered))) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolCompactAdditivePhysicalState compact : BurnolL2)) test
  rw [← burnolReciprocalStepSmoothedSource_realizes pulse lower upper lowerPositive ordered upperBound,
    ← sourceRead, burnolRemainderSourceRead_compact,
    Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [burnolCompactAdditiveL2_coeFn compact] with x valueAt
  change test x * burnolCompactAdditiveCoSum compact x = test x * burnolCompactAdditiveL2 compact x
  rw [valueAt]

private theorem dilation_zero (value : BurnolL2) : burnolMultiplicativeDilation 0 value = value := by
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn 0 value] with x hx
  simpa only [burnolL2RawNormalizedDilation, zero_div, Real.exp_zero,
    Complex.ofReal_one, one_mul] using hx

private theorem burnolReciprocalStepAnnulus_pulse_exists (lower upper δ : ℝ)
    (lowerStrict : (1 / 4 : ℝ) < lower) (ordered : lower ≤ upper)
    (upperStrict : upper < 4) (positive : 0 < δ) :
    ∃ pulse : ContDiffBump (0 : ℝ), pulse.rOut < δ ∧
      (1 / 4 : ℝ) ≤ Real.exp (-Real.log upper - pulse.rOut) ∧
      Real.exp (-Real.log lower + pulse.rOut) ≤ 4 := by
  have lowerPositive : 0 < lower := lt_trans (by norm_num) lowerStrict
  have upperPositive := lowerPositive.trans_le ordered
  have lowerRoom : 0 < Real.log lower - Real.log (1 / 4 : ℝ) :=
    sub_pos.mpr (Real.log_lt_log (by norm_num) lowerStrict)
  have upperRoom : 0 < Real.log 4 - Real.log upper :=
    sub_pos.mpr (Real.log_lt_log upperPositive upperStrict)
  let room := min δ (min (Real.log lower - Real.log (1 / 4 : ℝ))
    (Real.log 4 - Real.log upper))
  have roomPositive : 0 < room := lt_min positive (lt_min lowerRoom upperRoom)
  let pulse : ContDiffBump (0 : ℝ) := ⟨room / 4, room / 2, by positivity, by linarith⟩
  have within : pulse.rOut ≤ room := by change room / 2 ≤ room; linarith
  have hδ : pulse.rOut < δ := lt_of_lt_of_le (by change room / 2 < room; linarith) (min_le_left _ _)
  have hLower : pulse.rOut ≤ Real.log lower - Real.log (1 / 4 : ℝ) :=
    within.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUpper : pulse.rOut ≤ Real.log 4 - Real.log upper :=
    within.trans ((min_le_right _ _).trans (min_le_right _ _))
  have reciprocalLog : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  refine ⟨pulse, hδ, ?_, ?_⟩
  · rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 4), Real.exp_le_exp, reciprocalLog]
    linarith
  · rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_le_exp]
    rw [reciprocalLog] at hLower
    linarith

def burnolReciprocalStepPhysicalState (lower upper : ℝ) (lowerStrict : (1 / 4 : ℝ) < lower)
    (ordered : lower ≤ upper) (upperBound : upper ≤ 4) : BurnolPaAmbientCarrier :=
  ⟨burnolReciprocalStepWaveL2 lower upper (lt_trans (by norm_num) lowerStrict) ordered,
    burnolReciprocalStepWave_physical lower upper lowerStrict ordered upperBound⟩

theorem burnolReciprocalStepWave_memPa (lower upper : ℝ) (lowerStrict : (1 / 4 : ℝ) < lower)
    (ordered : lower ≤ upper) (upperStrict : upper < 4) :
    burnolReciprocalStepPhysicalState lower upper lowerStrict ordered upperStrict.le ∈
      burnolCompactCoPoissonClosedRange := by
  let value := burnolReciprocalStepWaveL2 lower upper (lt_trans (by norm_num) lowerStrict) ordered
  change burnolReciprocalStepPhysicalState lower upper lowerStrict ordered upperStrict.le ∈
    (burnolCompactCoPoissonClosedRange : Set BurnolPaAmbientCarrier)
  rw [← burnolCompactCoPoissonClosedRange.isClosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε positive
  obtain ⟨δ, δPositive, close⟩ := Metric.continuousAt_iff.mp
    (burnolMultiplicativeDilation_stronglyContinuous value).continuousAt (ε / 2) (by positivity)
  obtain ⟨pulse, small, innerMargin, outerMargin⟩ :=
    burnolReciprocalStepAnnulus_pulse_exists lower upper δ lowerStrict ordered upperStrict δPositive
  let smooth := burnolReciprocalStepAnnulusSmoothedSource pulse lower upper innerMargin outerMargin
  let compact := burnolCompactTateReciprocalSource smooth
  refine ⟨burnolCompactAdditivePhysicalState compact, ?_, ?_⟩
  · simpa [burnolCompactCoPoissonGenerator] using
      burnolCompactCoPoissonGenerator_mem_closedRange (compact, (0 : Fin 2))
  · have bound : dist (burnolReciprocalStepSmoothedValue pulse value) value ≤ ε / 2 := by
      have native := pulse.dist_normed_convolution_le (μ := (volume : Measure ℝ))
        (burnolMultiplicativeDilation_stronglyContinuous value).aestronglyMeasurable
        (x₀ := (0 : ℝ)) (ε := ε / 2) (fun h inBall =>
          (close ((Metric.mem_ball.mp inBall).trans small)).le)
      simpa only [burnolReciprocalStepSmoothedValue, dilation_zero] using native
    have generated := burnolReciprocalStepSmoothedValue_generator pulse lower upper
      (lt_trans (by norm_num) lowerStrict) ordered upperStrict.le innerMargin outerMargin
    change dist value (burnolCompactAdditivePhysicalState compact : BurnolL2) < ε
    rw [← generated, dist_comm]
    exact lt_of_le_of_lt bound (by linarith)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
