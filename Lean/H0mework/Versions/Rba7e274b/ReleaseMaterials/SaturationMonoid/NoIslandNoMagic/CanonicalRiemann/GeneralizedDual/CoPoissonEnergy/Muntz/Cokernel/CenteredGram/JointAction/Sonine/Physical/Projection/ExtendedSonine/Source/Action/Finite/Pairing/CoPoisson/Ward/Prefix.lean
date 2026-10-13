import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.StepCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.Prefix

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace

noncomputable section

/-- Discrete and continuous source channels are cut at the same integer. -/
def prefixChannels (lower upper : ℝ) (N : ℕ) (x : ℝ) : Finset ℕ :=
  (burnolReciprocalStepChannels lower upper x).filter (fun n => n < N)

def prefixReal (lower upper : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    ((prefixChannels lower upper N x).card -
      (min (upper * |x|) (N : ℝ) - min (lower * |x|) (N : ℝ))) / |x|

def prefixRaw (lower upper : ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  prefixReal lower upper N x

theorem prefixChannels_eq (lower upper : ℝ) (N : ℕ) (x : ℝ) :
    prefixChannels lower upper N x =
      Finset.Ico (min ⌈lower * |x|⌉₊ N) (min ⌈upper * |x|⌉₊ N) := by
  ext n
  simp only [prefixChannels, burnolReciprocalStepChannels, Finset.mem_filter, Finset.mem_Ico]
  omega

private theorem clippedCeil_error (t : ℝ) (nonnegative : 0 ≤ t) (N : ℕ) :
    0 ≤ (min ⌈t⌉₊ N : ℕ) - min t (N : ℝ) ∧
      (min ⌈t⌉₊ N : ℕ) - min t (N : ℝ) ≤ 1 := by
  rw [Nat.cast_min]
  constructor
  · exact sub_nonneg.mpr (min_le_min (Nat.le_ceil t) le_rfl)
  · by_cases clipped : (N : ℝ) ≤ t
    · rw [min_eq_right clipped, min_eq_right (clipped.trans (Nat.le_ceil t))]
      norm_num
    · rw [min_eq_left (le_of_not_ge clipped)]
      have ceiling := Nat.ceil_lt_add_one nonnegative
      have lower := min_le_left (⌈t⌉₊ : ℝ) (N : ℝ)
      linarith

theorem prefix_bound (lower upper : ℝ) (N : ℕ) (x : ℝ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (nonzero : x ≠ 0) :
    ‖prefixRaw lower upper N x‖ ≤ |x|⁻¹ := by
  have positive := abs_pos.mpr nonzero
  have indexOrder : min ⌈lower * |x|⌉₊ N ≤ min ⌈upper * |x|⌉₊ N :=
    min_le_min (Nat.ceil_mono (mul_le_mul_of_nonneg_right ordered positive.le)) le_rfl
  have lowerError := clippedCeil_error (lower * |x|) (mul_nonneg lowerPositive.le positive.le) N
  have upperError := clippedCeil_error (upper * |x|)
    (mul_nonneg (lowerPositive.trans_le ordered).le positive.le) N
  unfold prefixRaw prefixReal
  rw [if_neg nonzero, prefixChannels_eq, Nat.card_Ico, Nat.cast_sub indexOrder,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos positive, inv_eq_one_div,
    div_le_div_iff_of_pos_right positive, abs_le]
  constructor <;> linarith [lowerError.1, lowerError.2, upperError.1, upperError.2]

theorem prefix_measurable (lower upper : ℝ) (N : ℕ) :
    Measurable (prefixRaw lower upper N) := by
  unfold prefixRaw prefixReal
  simp only [prefixChannels_eq, Nat.card_Ico]
  apply Complex.measurable_ofReal.comp
  apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
  fun_prop

theorem prefix_eq_wave (lower upper : ℝ) (N : ℕ) (x : ℝ)
    (_lowerPositive : 0 < lower) (ordered : lower ≤ upper) (nonzero : x ≠ 0)
    (included : upper * |x| ≤ (N : ℝ)) :
    prefixRaw lower upper N x = burnolReciprocalStepWaveRaw lower upper x := by
  have lowerIncluded : lower * |x| ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_right ordered (abs_nonneg x)).trans included
  have upperIndex : ⌈upper * |x|⌉₊ ≤ N := Nat.ceil_le.mpr included
  have lowerIndex : ⌈lower * |x|⌉₊ ≤ N := Nat.ceil_le.mpr lowerIncluded
  simp only [prefixRaw, prefixReal, if_neg nonzero, prefixChannels_eq,
    min_eq_left upperIndex, min_eq_left lowerIndex, min_eq_left included,
    min_eq_left lowerIncluded, burnolReciprocalStepWaveRaw, burnolReciprocalStepWaveReal,
    burnolReciprocalStepChannels]
  congr 1
  field_simp

theorem prefix_eq_zero_tail (lower upper : ℝ) (N : ℕ) (x : ℝ)
    (ordered : lower ≤ upper) (excluded : (N : ℝ) ≤ lower * |x|) :
    prefixRaw lower upper N x = 0 := by
  have upperExcluded : (N : ℝ) ≤ upper * |x| :=
    excluded.trans (mul_le_mul_of_nonneg_right ordered (abs_nonneg x))
  have lowerIndex : N ≤ ⌈lower * |x|⌉₊ := by
    exact_mod_cast excluded.trans (Nat.le_ceil (lower * |x|))
  have upperIndex : N ≤ ⌈upper * |x|⌉₊ := by
    exact_mod_cast upperExcluded.trans (Nat.le_ceil (upper * |x|))
  simp [prefixRaw, prefixReal, prefixChannels_eq, min_eq_right lowerIndex,
    min_eq_right upperIndex, min_eq_right excluded, min_eq_right upperExcluded]

theorem prefix_zero (lower upper : ℝ) (lowerPositive : 0 < lower) (ordered : lower ≤ upper) :
    prefixRaw lower upper 0 = 0 := by
  funext x
  exact prefix_eq_zero_tail lower upper 0 x ordered
    (by simpa using mul_nonneg lowerPositive.le (abs_nonneg x))

theorem prefix_small_bound (lower upper : ℝ) (N : ℕ) (x : ℝ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (small : |x| ≤ upper⁻¹) :
    ‖prefixRaw lower upper N x‖ ≤ upper := by
  have upperPositive := lowerPositive.trans_le ordered
  by_cases zero : x = 0
  · simp [prefixRaw, prefixReal, zero, upperPositive.le]
  by_cases noChannels : N = 0
  · subst N
    rw [prefix_zero lower upper lowerPositive ordered]
    simpa using upperPositive.le
  have included : upper * |x| ≤ (N : ℝ) := by
    have oneLe : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr noChannels
    have upperSmall : upper * |x| ≤ 1 := by
      rw [inv_eq_one_div, le_div_iff₀ upperPositive] at small
      nlinarith
    exact upperSmall.trans oneLe
  rw [prefix_eq_wave lower upper N x lowerPositive ordered zero included,
    burnolReciprocalStepWave_small lower upper x lowerPositive ordered small,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr ordered)]
  linarith

/-- The common finite counting primitive retains its continuous normalization. -/
def primitiveRaw (N : ℕ) (x : ℝ) : ℂ :=
  ((((min ⌈|x|⌉₊ N : ℕ) : ℝ) - min |x| (N : ℝ) - (min 1 N : ℕ)) / |x| : ℝ)

theorem primitive_zero : primitiveRaw 0 = 0 := by
  funext x
  simp [primitiveRaw]

theorem primitive_measurable (N : ℕ) : Measurable (primitiveRaw N) := by
  unfold primitiveRaw
  fun_prop

theorem primitive_bound (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    ‖primitiveRaw N x‖ ≤ |x|⁻¹ := by
  by_cases noChannels : N = 0
  · subst N
    simp only [primitive_zero, Pi.zero_apply, norm_zero]
    positivity
  have oneLe : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr noChannels
  have error := clippedCeil_error |x| (abs_nonneg x) N
  have positive := abs_pos.mpr nonzero
  unfold primitiveRaw
  rw [min_eq_left oneLe]
  simp only [Nat.cast_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos positive, inv_eq_one_div,
    div_le_div_iff_of_pos_right positive, abs_le]
  constructor <;> linarith [error.1, error.2]

theorem primitive_eq_unit (N : ℕ) (x : ℝ) (nonzero : x ≠ 0)
    (included : |x| ≤ (N : ℝ)) :
    primitiveRaw N x = burnolUnitCountingPrimitiveRaw x := by
  have index : ⌈|x|⌉₊ ≤ N := Nat.ceil_le.mpr included
  have oneLe : 1 ≤ N := by
    have Npositive : (0 : ℝ) < N := (abs_pos.mpr nonzero).trans_le included
    exact_mod_cast Npositive
  simp only [primitiveRaw, min_eq_left index, min_eq_left included,
    min_eq_left oneLe, Nat.cast_one, burnolUnitCountingPrimitiveRaw, if_neg nonzero]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (abs_pos.mpr nonzero).ne']
  ring

theorem primitive_eq_tail (N : ℕ) (x : ℝ) (positive : 0 < N)
    (excluded : (N : ℝ) ≤ |x|) :
    primitiveRaw N x = -((|x| : ℝ) : ℂ)⁻¹ := by
  have index : N ≤ ⌈|x|⌉₊ := by exact_mod_cast excluded.trans (Nat.le_ceil |x|)
  simp [primitiveRaw, div_eq_mul_inv, min_eq_right index, min_eq_right excluded,
    min_eq_left (Nat.one_le_iff_ne_zero.mpr positive.ne')]

private def envelopeRaw (x : ℝ) : ℂ :=
  (symmetricInterval 1).indicator (fun _ : ℝ => (1 : ℂ)) x + burnolUnitReciprocalPrimitiveRaw x

private theorem envelope_memLp : MemLp envelopeRaw 2 volume := by
  have rawMem : MemLp burnolUnitReciprocalPrimitiveRaw 2 volume :=
    (Lp.memLp burnolUnitReciprocalPrimitiveL2).ae_eq burnolUnitReciprocalPrimitive_coeFn
  have headMem : MemLp ((symmetricInterval 1).indicator (fun _ : ℝ => (1 : ℂ))) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval 1) 1 (Or.inr (by simp [symmetricInterval]))
  exact headMem.add rawMem

private theorem envelope_norm_small (x : ℝ) (small : |x| ≤ 1) :
    ‖envelopeRaw x‖ = 1 := by
  unfold envelopeRaw
  rw [indicator_of_mem (show x ∈ symmetricInterval 1 from abs_le.mp small)]
  simp [burnolUnitReciprocalPrimitiveRaw, not_lt.mpr small]

private theorem envelope_norm_large (x : ℝ) (large : 1 < |x|) :
    ‖envelopeRaw x‖ = |x|⁻¹ := by
  unfold envelopeRaw
  rw [indicator_of_notMem (show x ∉ symmetricInterval 1 from
    fun hx => large.not_ge (abs_le.mpr hx))]
  simp [burnolUnitReciprocalPrimitiveRaw, large]

private theorem primitive_le_envelope (N : ℕ) (x : ℝ) :
    ‖primitiveRaw N x‖ ≤ ‖envelopeRaw x‖ := by
  by_cases zero : x = 0
  · simp [primitiveRaw, zero]
  by_cases noChannels : N = 0
  · subst N
    simp [primitive_zero]
  by_cases small : |x| ≤ 1
  · have oneLe : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr noChannels
    rw [primitive_eq_unit N x zero (small.trans oneLe),
      burnolUnitCountingPrimitive_small x small, norm_neg, norm_one, envelope_norm_small x small]
  · rw [envelope_norm_large x (lt_of_not_ge small)]
    exact primitive_bound N x zero

private theorem unit_le_envelope (x : ℝ) :
    ‖burnolUnitCountingPrimitiveRaw x‖ ≤ ‖envelopeRaw x‖ := by
  by_cases small : |x| ≤ 1
  · rw [burnolUnitCountingPrimitive_small x small, norm_neg, norm_one, envelope_norm_small x small]
  · rw [envelope_norm_large x (lt_of_not_ge small)]
    exact burnolUnitCountingPrimitive_bound x (abs_pos.mp (by linarith [abs_nonneg x]))

theorem primitive_memLp (N : ℕ) : MemLp (primitiveRaw N) 2 volume := by
  exact envelope_memLp.mono (primitive_measurable N).aestronglyMeasurable
    (Filter.Eventually.of_forall (primitive_le_envelope N))

def primitiveL2 (N : ℕ) : BurnolL2 := (primitive_memLp N).toLp (primitiveRaw N)

theorem primitive_coeFn (N : ℕ) :
    (primitiveL2 N : ℝ → ℂ) =ᵐ[volume] primitiveRaw N := (primitive_memLp N).coeFn_toLp

theorem primitive_tendsto_ae :
    ∀ᵐ x : ℝ ∂volume, Tendsto (fun N => primitiveRaw N x) atTop
      (𝓝 (burnolUnitCountingPrimitiveRaw x)) := by
  filter_upwards [ae_iff.mpr (show volume {x : ℝ | ¬ x ≠ 0} = 0 by simp)] with x nonzero
  apply tendsto_const_nhds.congr'
  refine Filter.eventually_atTop.mpr ⟨⌈|x|⌉₊, fun N after => ?_⟩
  exact (primitive_eq_unit N x nonzero
    ((Nat.le_ceil |x|).trans (by exact_mod_cast after))).symm

theorem primitive_tendsto :
    Tendsto primitiveL2 atTop (𝓝 burnolUnitCountingPrimitiveL2) := by
  have unitMeasurable : Measurable burnolUnitCountingPrimitiveRaw := by
    unfold burnolUnitCountingPrimitiveRaw
    apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
    fun_prop
  have squareLimit : Tendsto
      (fun N => ∫ x : ℝ, ‖primitiveRaw N x - burnolUnitCountingPrimitiveRaw x‖ ^ 2)
      atTop (𝓝 0) := by
    have limit := tendsto_integral_of_dominated_convergence
      (fun x : ℝ => 4 * ‖envelopeRaw x‖ ^ 2)
      (F := fun N x => ‖primitiveRaw N x - burnolUnitCountingPrimitiveRaw x‖ ^ 2)
      (f := fun _ => (0 : ℝ))
      (fun N => (((primitive_measurable N).sub unitMeasurable).norm.pow_const 2).aestronglyMeasurable)
      (envelope_memLp.norm.integrable_sq.const_mul 4) ?_ ?_
    · simpa using limit
    · intro N
      filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have bound : ‖primitiveRaw N x - burnolUnitCountingPrimitiveRaw x‖ ≤ 2 * ‖envelopeRaw x‖ := by
        calc
          _ ≤ ‖primitiveRaw N x‖ + ‖burnolUnitCountingPrimitiveRaw x‖ := norm_sub_le _ _
          _ ≤ _ := by linarith [primitive_le_envelope N x, unit_le_envelope x]
      nlinarith [sq_nonneg (‖primitiveRaw N x - burnolUnitCountingPrimitiveRaw x‖ -
        2 * ‖envelopeRaw x‖), norm_nonneg (primitiveRaw N x - burnolUnitCountingPrimitiveRaw x),
        norm_nonneg (envelopeRaw x)]
    · filter_upwards [primitive_tendsto_ae] with x pointwise
      simpa using (pointwise.sub (tendsto_const_nhds (x := burnolUnitCountingPrimitiveRaw x))).norm.pow 2
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (primitiveRaw ·) primitive_memLp
    burnolUnitCountingPrimitiveRaw burnolUnitCountingPrimitive_memLp).mpr
  have rootLimit := squareLimit.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
  have limit := ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using rootLimit)
  convert limit using 1
  · ext N
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((primitive_memLp N).sub burnolUnitCountingPrimitive_memLp)]
    simp
  · simp

theorem primitive_difference (lower upper : ℝ) (N : ℕ) (x : ℝ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) :
    (upper : ℂ) * primitiveRaw N (upper * x) -
      (lower : ℂ) * primitiveRaw N (lower * x) = prefixRaw lower upper N x := by
  by_cases zero : x = 0
  · simp [primitiveRaw, prefixRaw, prefixReal, zero]
  have upperPositive := lowerPositive.trans_le ordered
  have indexOrder : min ⌈lower * |x|⌉₊ N ≤ min ⌈upper * |x|⌉₊ N :=
    min_le_min (Nat.ceil_mono (mul_le_mul_of_nonneg_right ordered (abs_nonneg x))) le_rfl
  simp only [primitiveRaw, prefixRaw, prefixReal, if_neg zero, prefixChannels_eq,
    Nat.card_Ico, Nat.cast_sub indexOrder, abs_mul, abs_of_pos lowerPositive,
    abs_of_pos upperPositive]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr lowerPositive.ne',
    Complex.ofReal_ne_zero.mpr upperPositive.ne',
    Complex.ofReal_ne_zero.mpr (abs_pos.mpr zero).ne']
  ring

/-- One finite primitive generates both actual endpoint scales. -/
def prefixL2 (lower upper : ℝ) (N : ℕ) : BurnolL2 :=
  burnolSourceScalePrimitive (primitiveL2 N) upper - burnolSourceScalePrimitive (primitiveL2 N) lower

theorem prefix_coeFn (lower upper : ℝ) (N : ℕ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) :
    (prefixL2 lower upper N : ℝ → ℂ) =ᵐ[volume] prefixRaw lower upper N := by
  filter_upwards [Lp.coeFn_sub (burnolSourceScalePrimitive (primitiveL2 N) upper)
    (burnolSourceScalePrimitive (primitiveL2 N) lower),
    burnolSourceScalePrimitive_coeFn (primitiveL2 N) (primitiveRaw N) (primitive_coeFn N)
      upper (lowerPositive.trans_le ordered),
    burnolSourceScalePrimitive_coeFn (primitiveL2 N) (primitiveRaw N) (primitive_coeFn N)
      lower lowerPositive] with x differenceAt upperAt lowerAt
  change (burnolSourceScalePrimitive (primitiveL2 N) upper -
    burnolSourceScalePrimitive (primitiveL2 N) lower : BurnolL2) x = _
  rw [differenceAt]
  change burnolSourceScalePrimitive (primitiveL2 N) upper x -
    burnolSourceScalePrimitive (primitiveL2 N) lower x = _
  rw [upperAt, lowerAt]
  exact primitive_difference lower upper N x lowerPositive ordered

theorem prefix_memLp (lower upper : ℝ) (N : ℕ) (lowerPositive : 0 < lower)
    (ordered : lower ≤ upper) : MemLp (prefixRaw lower upper N) 2 volume :=
  (Lp.memLp (prefixL2 lower upper N)).ae_eq (prefix_coeFn lower upper N lowerPositive ordered)

theorem prefix_continuous_upper (lower : ℝ) (N : ℕ) :
    ContinuousOn (fun upper => prefixL2 lower upper N) (Ioi 0) :=
  (burnolSourceScalePrimitive_continuous (primitiveL2 N)).sub continuousOn_const

theorem prefix_tendsto (lower upper : ℝ) :
    Tendsto (prefixL2 lower upper) atTop (𝓝 (burnolReciprocalStepNativeWave lower upper)) := by
  have scaleLimit (scale : ℝ) :
      Tendsto (fun N => burnolSourceScalePrimitive (primitiveL2 N) scale) atTop
        (𝓝 (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 scale)) := by
    unfold burnolSourceScalePrimitive
    exact ((burnolMultiplicativeDilation (Real.log scale)).continuous.tendsto
      burnolUnitCountingPrimitiveL2 |>.comp primitive_tendsto).const_smul (Real.sqrt scale)
  exact (scaleLimit upper).sub (scaleLimit lower)

theorem finiteSource_count (lower upper : ℝ) (N : ℕ) (x : ℝ)
    (lowerPositive : 0 < lower) (nonzero : x ≠ 0) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ)⁻¹ *
      burnolReciprocalStepSourceRaw lower upper (x / (n : ℝ))) =
        ((prefixChannels lower upper N x).card : ℂ) * ((|x| : ℝ) : ℂ)⁻¹ := by
  classical
  have positiveIndex : 0 < ⌈lower * |x|⌉₊ :=
    Nat.ceil_pos.mpr (mul_pos lowerPositive (abs_pos.mpr nonzero))
  have activeSet : (Finset.Ico 1 N).filter
      (fun n => n ∈ burnolReciprocalStepChannels lower upper x) = prefixChannels lower upper N x := by
    ext n
    simp only [prefixChannels, burnolReciprocalStepChannels, Finset.mem_filter, Finset.mem_Ico]
    omega
  calc
    _ = ∑ n ∈ Finset.Ico 1 N,
        if n ∈ burnolReciprocalStepChannels lower upper x then ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro n belongs
      exact burnolReciprocalStep_source_term lower upper x nonzero
        (⟨n, Nat.lt_of_lt_of_le (by decide : 0 < 1) (Finset.mem_Ico.mp belongs).1⟩ : ℕ+)
    _ = ∑ _ ∈ prefixChannels lower upper N x, ((|x| : ℝ) : ℂ)⁻¹ := by
      rw [← activeSet, Finset.sum_filter]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The mean is the continuous channel integral over the same finite range. -/
theorem prefix_finite_source (lower upper : ℝ) (N : ℕ) (x : ℝ)
    (lowerPositive : 0 < lower) (nonzero : x ≠ 0) :
    prefixRaw lower upper N x =
      (∑ n ∈ Finset.Ico 1 N, (n : ℂ)⁻¹ *
        burnolReciprocalStepSourceRaw lower upper (x / (n : ℝ))) -
          (((min (upper * |x|) (N : ℝ) - min (lower * |x|) (N : ℝ)) / |x| : ℝ) : ℂ) := by
  rw [finiteSource_count lower upper N x lowerPositive nonzero]
  unfold prefixRaw prefixReal
  rw [if_neg nonzero]
  push_cast
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.Prefix
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
