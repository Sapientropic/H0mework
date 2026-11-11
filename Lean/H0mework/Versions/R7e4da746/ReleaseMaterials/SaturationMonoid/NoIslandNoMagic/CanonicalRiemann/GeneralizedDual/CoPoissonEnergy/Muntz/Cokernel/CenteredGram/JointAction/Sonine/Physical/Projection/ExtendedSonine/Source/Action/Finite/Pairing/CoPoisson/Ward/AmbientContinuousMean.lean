import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WholeSourceWindow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.AmbientContinuousMean

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource InverseAction
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

private theorem integral_inverse_weight (raw : ℝ → ℂ) :
    (∫ a : ℝ in Ioi 0, (a : ℂ)⁻¹ * raw a⁻¹) =
      ∫ t : ℝ in Ioi 0, (t : ℂ)⁻¹ * raw t := by
  have changeVariables := integral_comp_rpow_Ioi
    (fun t : ℝ => (t : ℂ)⁻¹ * raw t) (by norm_num : (-1 : ℝ) ≠ 0)
  convert changeVariables using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro a positive
  dsimp only
  rw [show (-1 : ℝ) - 1 = -2 by norm_num,
    show |(-1 : ℝ)| = 1 by norm_num, one_mul,
    Real.rpow_neg_one, show (-2 : ℝ) = -(2 : ℕ) by norm_num,
    Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_inv, inv_inv]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']

private theorem integral_scaled_inverse_weight (raw : ℝ → ℂ) (x : ℝ)
    (positive : 0 < x) :
    (∫ a : ℝ in Ioi 0, (a : ℂ)⁻¹ * raw (x / a)) =
      ∫ t : ℝ in Ioi 0, (t : ℂ)⁻¹ * raw t := by
  have changed := integral_comp_mul_left_Ioi'
    (fun a : ℝ => (a : ℂ)⁻¹ * raw (x / a)) 0 positive
  rw [mul_zero] at changed
  rw [← changed, ← integral_smul]
  calc
    _ = ∫ a : ℝ in Ioi 0, (a : ℂ)⁻¹ * raw a⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a aPositive
      dsimp only
      rw [Complex.real_smul, Complex.ofReal_mul]
      have argument : x / (x * a) = a⁻¹ := by field_simp
      rw [argument]
      field_simp [Complex.ofReal_ne_zero.mpr positive.ne',
        Complex.ofReal_ne_zero.mpr aPositive.ne']
    _ = _ := integral_inverse_weight raw

/-- The complete positive scale integral reads the original reciprocal moment.
The value at zero is excluded only at the final L² representative. -/
theorem countingRaw_integral (raw : ℝ → ℂ) (even : ∀ x, raw (-x) = raw x)
    (x : ℝ) (nonzero : x ≠ 0) :
    (∫ a : ℝ in Ioi 0, countingRaw a raw x) =
      ∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * raw t := by
  let extended := (symmetricInterval q).indicator raw
  have extendedEven : ∀ y, extended (-y) = extended y := by
    intro y
    have same : -y ∈ symmetricInterval q ↔ y ∈ symmetricInterval q := by
      change -q ≤ -y ∧ -y ≤ q ↔ -q ≤ y ∧ y ≤ q
      constructor <;> rintro ⟨lower, upper⟩ <;> constructor <;> linarith
    change (symmetricInterval q).indicator raw (-y) = (symmetricInterval q).indicator raw y
    by_cases inside : y ∈ symmetricInterval q
    · rw [indicator_of_mem (same.mpr inside), indicator_of_mem inside, even]
    · rw [indicator_of_notMem (fun member => inside (same.mp member)), indicator_of_notMem inside]
  have absolute : ∀ y, extended y = extended |y| := by
    intro y
    rcases le_total 0 y with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, extendedEven]
  calc
    _ = ∫ a : ℝ in Ioi 0, (a : ℂ)⁻¹ * extended (|x| / a) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a positive
      change (a : ℂ)⁻¹ * extended (x / a) = _
      simpa only [abs_div, abs_of_pos (show 0 < a from positive)] using
        congrArg (fun z : ℂ => (a : ℂ)⁻¹ * z) (absolute (x / a))
    _ = ∫ t : ℝ in Ioi 0, (t : ℂ)⁻¹ * extended t :=
      integral_scaled_inverse_weight extended |x| (abs_pos.mpr nonzero)
    _ = ∫ t : ℝ in Ioi 0,
        (symmetricInterval q).indicator (fun t : ℝ => (t : ℂ)⁻¹ * raw t) t := by
      apply integral_congr_ae
      filter_upwards with t
      change (t : ℂ)⁻¹ * (symmetricInterval q).indicator raw t = _
      by_cases inside : t ∈ symmetricInterval q
      · rw [indicator_of_mem inside, indicator_of_mem inside]
      · rw [indicator_of_notMem inside, indicator_of_notMem inside, mul_zero]
    _ = _ := by
      rw [integral_indicator (measurableSet_symmetricInterval q),
        Measure.restrict_restrict (measurableSet_symmetricInterval q)]
      have intersection : symmetricInterval q ∩ Ioi 0 = Ioc 0 q := by
        ext t
        simp only [mem_inter_iff, symmetricInterval, mem_Icc, mem_Ioi, mem_Ioc]
        constructor
        · rintro ⟨⟨_, upper⟩, lower⟩
          exact ⟨lower, upper⟩
        · rintro ⟨lower, upper⟩
          exact ⟨⟨by linarith, upper⟩, lower⟩
      rw [intersection]

private theorem extended_read (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    (burnolQuarterZeroExtension state : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval q).indicator raw := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp represents
  filter_upwards [burnolQuarterZeroExtension_coe state, localRead] with x extension same
  rw [extension]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, same inside]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

/-- Whole-window integration is taken before its mean-zero cotest.
Its Bochner integrability belongs to the original source family. -/
theorem countingWindow_integral (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (measured : Measurable raw) (even : ∀ x, raw (-x) = raw x)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (integrable : IntegrableOn (fun a : ℝ => countingWindow a state) (Ioi 0)) :
    (∫ a : ℝ in Ioi 0, countingWindow a state) =
      (∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * raw t) • intervalConstant q := by
  classical
  let family : ℝ → BurnolL2 := fun a => burnolQuarterZeroExtension (countingWindow a state)
  let fullRaw : ℝ × ℝ → ℂ := fun point =>
    (symmetricInterval q).indicator (countingRaw point.1 raw) point.2
  have fullIntegrable : IntegrableOn family (Ioi 0) :=
    burnolQuarterZeroExtension.integrable_comp integrable
  have joint : Measurable fullRaw := by
    have countMeasured : Measurable (fun point : ℝ × ℝ => countingRaw point.1 raw point.2) := by
      unfold countingRaw
      exact (by fun_prop : Measurable (fun point : ℝ × ℝ => (point.1 : ℂ)⁻¹)).mul
        ((measured.indicator (measurableSet_symmetricInterval q)).comp (by fun_prop))
    change Measurable (fun point : ℝ × ℝ =>
      if point.2 ∈ symmetricInterval q then countingRaw point.1 raw point.2 else 0)
    exact countMeasured.ite ((measurableSet_symmetricInterval q).preimage measurable_snd)
      measurable_const
  have fullRead : ∀ᵐ a ∂volume.restrict (Ioi 0),
      (family a : ℝ → ℂ) =ᵐ[volume] fun x => fullRaw (a, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a positive
    exact extended_read _ _ (countingWindow_raw a positive state raw represents)
  have bochner := OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioi 0)) family fullIntegrable fullRaw joint fullRead
  have fullConstant :
      (∫ a : ℝ in Ioi 0, family a) = burnolQuarterZeroExtension
        ((∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * raw t) • intervalConstant q) := by
    have constantRead :
        (((∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * raw t) • intervalConstant q :
          BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq]
        fun _ => ∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * raw t := by
      filter_upwards [Lp.coeFn_smul (∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * raw t)
        (intervalConstant q), intervalConstant_coeFn q] with x scalarAt constantAt
      rw [scalarAt]
      change (∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * raw t) * intervalConstant q x = _
      rw [constantAt, mul_one]
    apply Lp.ext
    filter_upwards [bochner, extended_read _ _ constantRead, volume.ae_ne (0 : ℝ)]
      with x integralAt constantAt nonzero
    rw [integralAt, constantAt]
    by_cases inside : x ∈ symmetricInterval q
    · simp only [fullRaw, indicator_of_mem inside]
      exact countingRaw_integral raw even x nonzero
    · simp only [fullRaw, indicator_of_notMem inside, integral_zero]
  have same := congrArg burnolQuarterRestriction fullConstant
  rw [show (∫ a : ℝ in Ioi 0, family a) = burnolQuarterZeroExtension
      (∫ a : ℝ in Ioi 0, countingWindow a state) from
      burnolQuarterZeroExtension.integral_comp_comm integrable,
    burnolQuarterRestriction_zeroExtension, burnolQuarterRestriction_zeroExtension] at same
  exact same

theorem forcing_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ a : ℝ in Ioi 0, countingWindow a (ForcingTail.forcingRemainderState coordinate)) =
      (∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * ForcingTail.forcingRemainder coordinate t) • intervalConstant q := by
  apply countingWindow_integral _ _ (ForcingTail.forcingRemainder_measurable coordinate)
    _ (ForcingTail.forcingRemainderState_ae_raw coordinate)
    (WholeSourceWindow.forcing_window_integrable coordinate)
  intro x
  simp only [ForcingTail.forcingRemainder, ForcingTail.edgeRemainder, abs_neg]

theorem return_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ a : ℝ in Ioi 0, countingWindow a (WholeSourceWindow.smoothState coordinate)) =
      (∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * InverseTail.smoothFourier coordinate t) • intervalConstant q := by
  apply countingWindow_integral _ _ _ _ (WholeSourceWindow.smoothState_ae_raw coordinate)
    (WholeSourceWindow.smooth_window_integrable coordinate)
  · exact (continuous_iff_continuousAt.mpr (fun x =>
      (Constructor.fourierRaw_hasDerivAt _
        (burnolRieszReturnRaw_continuous coordinate) x).continuousAt)).measurable
  · intro x
    have reflected := intervalIntegral.integral_comp_neg
      (f := fun y => Constructor.phase x y * burnolRieszReturnRaw coordinate y)
      (a := -q) (b := q)
    simp only [neg_neg] at reflected
    rw [InverseTail.smoothFourier, Constructor.fourierRaw_integral,
      Constructor.fourierRaw_integral, ← reflected]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [OriginalRieszFinitePairing.return_raw_even]
    congr 1
    simp only [Constructor.phase, neg_mul, mul_neg, neg_neg]

private theorem reciprocal_integrable_of_quadratic (raw : ℝ → ℂ) (measured : Measurable raw)
    (bound : ℝ) (quadratic : ∀ t ∈ Ioc 0 q, ‖raw t‖ ≤ bound * t ^ 2) :
    IntegrableOn (fun t : ℝ => (t : ℂ)⁻¹ * raw t) (Ioc 0 q) := by
  have envelope : IntegrableOn (fun t : ℝ => bound * t) (Ioc 0 q) :=
    ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply envelope.mono' ((by fun_prop : Measurable (fun t : ℝ => (t : ℂ)⁻¹)).mul measured).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  change ‖(t : ℂ)⁻¹ * raw t‖ ≤ bound * t
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos inside.1]
  exact (mul_le_mul_of_nonneg_left (quadratic t inside) (inv_nonneg.mpr inside.1.le)).trans_eq
    (by field_simp)

theorem forcing_reciprocal_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => (t : ℂ)⁻¹ * ForcingTail.forcingRemainder coordinate t) (Ioc 0 q) := by
  apply reciprocal_integrable_of_quadratic _ (ForcingTail.forcingRemainder_measurable coordinate)
    (4 * ‖Translator.ForcingWhole.coefficient coordinate‖)
  intro t inside
  exact ForcingTail.forcingRemainder_bound coordinate (by rw [abs_of_pos inside.1]; exact inside.2)

theorem return_reciprocal_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => (t : ℂ)⁻¹ * InverseTail.smoothFourier coordinate t) (Ioc 0 q) := by
  apply reciprocal_integrable_of_quadratic _
    (Constructor.fourierRaw_continuous _ (burnolRieszReturnRaw_continuous coordinate)).measurable
    (16 * InverseTail.returnMass coordinate)
  intro t inside
  have large : 1 ≤ q / t := (le_div_iff₀ inside.1).mpr (by simpa using inside.2)
  have bound := InverseTail.smoothFourier_bound coordinate (q / t) large
    (x := q) (by norm_num)
  have argument : q / (q / t) = t := by field_simp
  rw [argument, inv_div] at bound
  exact bound.trans_eq (by ring)

private theorem meanZero_constant_pair (scalar : ℂ) (test : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (scalar • intervalConstant q) (test : BurnolQuarterIntervalL2) = 0 := by
  rw [inner_smul_left, (Submodule.mem_orthogonal _ _).mp test.property _
    (Submodule.mem_span_singleton_self _), mul_zero]

theorem forcing_meanZero_pair (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (∫ a : ℝ in Ioi 0, countingWindow a (ForcingTail.forcingRemainderState coordinate))
      (test : BurnolQuarterIntervalL2) = 0 := by
  rw [forcing_continuous]
  exact meanZero_constant_pair _ test

theorem return_meanZero_pair (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (∫ a : ℝ in Ioi 0, countingWindow a (WholeSourceWindow.smoothState coordinate))
      (test : BurnolQuarterIntervalL2) = 0 := by
  rw [return_continuous]
  exact meanZero_constant_pair _ test

/-- The original b and its actual Fourier return both consume the full continuous source. -/
theorem original_continuous_contacts (coordinate : BurnolCompletedMellinCoordinate) :
    let first := ∫ a : ℝ in Ioi 0, countingWindow a (ForcingTail.forcingRemainderState coordinate)
    let second := ∫ a : ℝ in Ioi 0, countingWindow a (WholeSourceWindow.smoothState coordinate)
    let b := burnolRieszSingleFourierSource coordinate
    let r := burnolMeanZeroTruncatedFourier b
    inner ℂ first (b : BurnolQuarterIntervalL2) = 0 ∧
      inner ℂ second (b : BurnolQuarterIntervalL2) = 0 ∧
      inner ℂ first (r : BurnolQuarterIntervalL2) = 0 ∧
      inner ℂ second (r : BurnolQuarterIntervalL2) = 0 :=
  ⟨forcing_meanZero_pair coordinate _, return_meanZero_pair coordinate _,
    forcing_meanZero_pair coordinate _, return_meanZero_pair coordinate _⟩

/-- The n=1 return term reads the norm of the same original source return. -/
theorem original_return_source_pair (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ (WholeSourceWindow.smoothState coordinate)
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
        (‖burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)‖ ^ 2 : ℂ) := by
  let b := burnolRieszSingleFourierSource coordinate
  let r := burnolMeanZeroTruncatedFourier b
  have centered : inner ℂ (WholeSourceWindow.smoothState coordinate) (b : BurnolQuarterIntervalL2) =
      inner ℂ (burnolMeanZeroTruncatedFourier r) b := by
    unfold burnolMeanZeroTruncatedFourier
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    rfl
  rw [centered, OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection r b
    (burnolRieszSingleFourierSource_reflection_fixed coordinate)]
  exact inner_self_eq_norm_sq_to_K _

end
end OriginalRieszFinitePairing.CoPoisson.Ward.AmbientContinuousMean
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
