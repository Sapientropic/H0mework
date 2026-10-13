import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WholeSourceWindow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DualSourceRaw

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def seedRaw (coordinate : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate)

def raw (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, seedRaw coordinate ((n : ℝ) * x)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)

theorem seedRaw_measurable (coordinate : BurnolCompletedMellinCoordinate) :
    Measurable (seedRaw coordinate) := by
  apply Measurable.indicator _ (measurableSet_symmetricInterval q)
  apply measurable_of_continuousOn_compl_singleton 0
  intro x outside
  exact (burnolRieszSingleFourierSourceRaw_continuousAt coordinate
    (by simpa only [mem_compl_iff, mem_singleton_iff] using outside)).continuousWithinAt

theorem seedRaw_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[volume]
        seedRaw coordinate := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolRieszSingleFourierSource_ae_raw coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2), localRead]
      with x extension read
  rw [extension]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, seedRaw, indicator_of_mem inside, read inside]
  · rw [indicator_of_notMem inside, seedRaw, indicator_of_notMem inside]

theorem channel_coeFn (seed : BurnolL2) (seedRaw : ℝ → ℂ)
    (represents : (seed : ℝ → ℂ) =ᵐ[volume] seedRaw) (a : ℝ) (positive : 0 < a) :
    (ContinuousChannels.channel 1 a seed : ℝ → ℂ) =ᵐ[volume]
      fun x => seedRaw (a * x) := by
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) positive.ne').ae represents
  have squareRoot : Real.sqrt a = Real.exp (Real.log a / 2) := by
    rw [Real.exp_half, Real.exp_log positive]
  simp only [ContinuousChannels.channel, one_mul]
  filter_upwards [Lp.coeFn_smul (Real.sqrt a : ℂ)⁻¹
    (burnolMultiplicativeDilation (Real.log a) seed),
    burnolMultiplicativeDilation_coeFn (Real.log a) seed, moved] with x scalarAt dilatedAt sourceAt
  change (((Real.sqrt a : ℂ)⁻¹ • burnolMultiplicativeDilation (Real.log a) seed : BurnolL2) x) = _
  rw [scalarAt]
  change (Real.sqrt a : ℂ)⁻¹ * burnolMultiplicativeDilation (Real.log a) seed x = _
  rw [dilatedAt, burnolL2RawNormalizedDilation, Real.exp_log positive]
  rw [← mul_assoc]
  change (Real.sqrt a : ℂ)⁻¹ * ((Real.exp (Real.log a / 2) : ℝ) : ℂ) * seed (a * x) = _
  rw [← squareRoot, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr positive).ne'), one_mul]
  exact sourceAt

theorem normalization_coeFn (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) : BurnolL2) :
        ℝ → ℂ) =ᵐ[volume] fun x => ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x) := by
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc 0 (N : ℝ))) _
    (ContinuousChannels.channel_integrable 1 (N : ℝ) _)
    (fun point : ℝ × ℝ => seedRaw coordinate (point.1 * point.2))
    ((seedRaw_measurable coordinate).comp (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  exact channel_coeFn _ _ (seedRaw_read coordinate) a inside.1

/-- Both finite directions retain the same cutoff and all small positive scales. -/
theorem original_coeFn (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    (DualSource.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) : ℝ → ℂ) =ᵐ[volume]
        raw coordinate N := by
  let seed := burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  have channels : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n : ℝ) seed x = seedRaw coordinate ((n : ℝ) * x) := by
    apply ae_all_iff.mpr
    intro n
    exact channel_coeFn seed _ (seedRaw_read coordinate) (n : ℝ)
      (by exact_mod_cast (Finset.mem_Ico.mp n.2).1)
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed)
    (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel 1 (n : ℝ) seed),
    normalization_coeFn coordinate N, channels] with x differenceAt sumAt integralAt channelAt
  change ((∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed : BurnolL2) x = _
  rw [differenceAt, Pi.sub_apply, sumAt, integralAt]
  unfold raw
  congr 1
  apply Finset.sum_congr rfl
  intro n inside
  exact channelAt ⟨n, inside⟩

/-- The original log source pays the complete dual q-mean; no mean-zero output is imposed. -/
theorem original_mean (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (DualSource.source N
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))) =
      2 * inner ℂ SmallScaleLog.logL2 (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) := by
  let b := burnolRieszSingleFourierSource coordinate
  have first : inner ℂ (intervalConstant q) (burnolQuarterRestriction (DualSource.source N
      (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2)))) =
      inner ℂ (WindowCounting.windowSource N (intervalConstant q)) (b : BurnolQuarterIntervalL2) := by
    calc
      _ = inner ℂ (burnolQuarterZeroExtension (intervalConstant q))
          (DualSource.source N (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2))) :=
        (ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _).symm
      _ = inner ℂ (FiniteForcing.source N (burnolQuarterZeroExtension (intervalConstant q)))
          (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2)) := (CountingDual.source_pairing N _ _).symm
      _ = _ := ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _
  have meanZero : inner ℂ (intervalConstant q) (b : BurnolQuarterIntervalL2) = 0 :=
    (Submodule.mem_orthogonal _ _).mp b.property _ (Submodule.mem_span_singleton_self _)
  unfold burnolQuarterMeanCoefficient
  rw [first, WindowCounting.constant_source N positive, inner_add_left, inner_smul_left,
    meanZero, mul_zero, zero_add, Complex.ofReal_pow,
    burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
  norm_num
  ring

theorem seedRaw_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    seedRaw coordinate (-x) = seedRaw coordinate x := by
  have same : -x ∈ symmetricInterval q ↔ x ∈ symmetricInterval q := by
    change -q ≤ -x ∧ -x ≤ q ↔ -q ≤ x ∧ x ≤ q
    constructor <;> rintro ⟨lower, upper⟩ <;> constructor <;> linarith
  unfold seedRaw
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem (same.mpr inside), indicator_of_mem inside, source_raw_even]
  · rw [indicator_of_notMem (fun member => inside (same.mp member)), indicator_of_notMem inside]

private theorem even_absolute (f : ℝ → ℂ) (even : ∀ x, f (-x) = f x) (x : ℝ) : f x = f |x| := by
  rcases le_total 0 x with positive | negative
  · rw [abs_of_nonneg positive]
  · rw [abs_of_nonpos negative, even]

private theorem even_half_integral (f : ℝ → ℂ) (integrable : IntegrableOn f (symmetricInterval q))
    (even : ∀ x, f (-x) = f x) :
    (∫ x : ℝ in symmetricInterval q, f x) = 2 * ∫ x : ℝ in Ioc 0 q, f x := by
  have first : IntegrableOn f (Ioc (-q) 0) := integrable.mono_set (by
    intro x inside
    exact ⟨inside.1.le, inside.2.trans (by norm_num)⟩)
  have second : IntegrableOn f (Ioc 0 q) := integrable.mono_set (by
    intro x inside
    exact ⟨by linarith [inside.1], inside.2⟩)
  have split := setIntegral_union (Ioc_disjoint_Ioc_of_le (a := -q) (b := (0 : ℝ)) (c := 0) (d := q) le_rfl)
    measurableSet_Ioc first second
  rw [Ioc_union_Ioc_eq_Ioc (by norm_num : -q ≤ (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ q)] at split
  have reflected : (∫ x : ℝ in Ioc (-q) 0, f x) = ∫ x : ℝ in Ioc 0 q, f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : -q ≤ (0 : ℝ)),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)]
    have result := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := q)
    rw [show (fun x => f (-x)) = f from funext even, neg_zero] at result
    exact result.symm
  change (∫ x : ℝ in Icc (-q) q, f x) = _
  rw [integral_Icc_eq_integral_Ioc, split, reflected]
  ring

theorem source_half_integral_zero (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ t : ℝ in Ioc 0 q, burnolRieszSingleFourierSourceRaw coordinate t) = 0 := by
  let b := burnolRieszSingleFourierSource coordinate
  have integrable : IntegrableOn (burnolRieszSingleFourierSourceRaw coordinate) (symmetricInterval q) :=
    ((Lp.memLp (b : BurnolQuarterIntervalL2)).integrable (by norm_num)).congr
      (burnolRieszSingleFourierSource_ae_raw coordinate)
  have meanZero := Constructor.mean_zero b
  rw [Constructor.mean_integral, integral_congr_ae (burnolRieszSingleFourierSource_ae_raw coordinate),
    even_half_integral _ integrable (source_raw_even coordinate)] at meanZero
  linear_combination meanZero / 4

theorem original_mean_integral (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (DualSource.source N
      (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))) =
      4 * ∫ t : ℝ in Ioc 0 q,
        burnolRieszSingleFourierSourceRaw coordinate t * (Real.log (t / q) : ℂ) := by
  let b := burnolRieszSingleFourierSource coordinate
  let product : ℝ → ℂ := fun x => SmallScaleLog.logRaw x * burnolRieszSingleFourierSourceRaw coordinate x
  have pairRead : (fun x : ℝ => inner ℂ (SmallScaleLog.logL2 x)
      ((b : BurnolQuarterIntervalL2) x)) =ᵐ[μq] product := by
    filter_upwards [SmallScaleLog.log_coeFn, burnolRieszSingleFourierSource_ae_raw coordinate]
      with x logarithm original
    rw [logarithm, original]
    change burnolRieszSingleFourierSourceRaw coordinate x *
      (starRingEnd ℂ) (Real.log (|x| / q) : ℂ) =
        (Real.log (|x| / q) : ℂ) * burnolRieszSingleFourierSourceRaw coordinate x
    rw [conj_ofReal, mul_comm]
  have integrable : IntegrableOn product (symmetricInterval q) :=
    (L2.integrable_inner (𝕜 := ℂ) SmallScaleLog.logL2 (b : BurnolQuarterIntervalL2)).congr pairRead
  have even : ∀ x, product (-x) = product x := by
    intro x
    simp only [product, SmallScaleLog.logRaw, abs_neg, source_raw_even]
  rw [original_mean coordinate N positive, L2.inner_def, integral_congr_ae pairRead,
    even_half_integral product integrable even]
  have half : (∫ t : ℝ in Ioc 0 q, product t) = ∫ t : ℝ in Ioc 0 q,
      burnolRieszSingleFourierSourceRaw coordinate t * (Real.log (t / q) : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t inside
    simp only [product, SmallScaleLog.logRaw, abs_of_pos inside.1]
    exact mul_comm _ _
  rw [half]
  ring

/-- For a fixed nonzero observation the entire continuous channel is paid by original b's mean. -/
theorem continuous_raw_zero (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (covered : q ≤ (N : ℝ) * |x|) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) = 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have scaled : (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) =
      |x|⁻¹ • ∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), seedRaw coordinate t := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a inside => by
      simpa only [abs_mul, abs_of_pos inside.1] using
        even_absolute (seedRaw coordinate) (seedRaw_even coordinate) (a * x)),
      ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ absolute.ne', zero_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ) * |x|)]
  have intersection : symmetricInterval q ∩ Ioc 0 ((N : ℝ) * |x|) = Ioc 0 q := by
    ext t
    simp only [mem_inter_iff, symmetricInterval, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨_, upper⟩, lower, _⟩
      exact ⟨lower, upper⟩
    · rintro ⟨lower, upper⟩
      exact ⟨⟨by linarith, upper⟩, lower, upper.trans covered⟩
  rw [scaled, seedRaw, integral_indicator (measurableSet_symmetricInterval q),
    Measure.restrict_restrict (measurableSet_symmetricInterval q), intersection,
    source_half_integral_zero, smul_zero]

theorem raw_outside (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ)
    (positive : 0 < N) (x : ℝ) (outside : q < |x|) : raw coordinate N x = 0 := by
  have nonzero : x ≠ 0 := abs_pos.mp (lt_trans (by norm_num : (0 : ℝ) < q) outside)
  have one : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have covered : q ≤ (N : ℝ) * |x| := by nlinarith [abs_nonneg x]
  rw [raw, continuous_raw_zero coordinate N x nonzero covered, sub_zero]
  apply Finset.sum_eq_zero
  intro n inside
  have oneIndex : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp inside).1
  apply indicator_of_notMem
  intro member
  have located := abs_le.mpr member
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at located
  nlinarith [abs_nonneg x]

def channels (x : ℝ) : Finset ℕ := Finset.Icc 1 ⌊q / |x|⌋₊

def eventRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n ∈ channels x, burnolRieszSingleFourierSourceRaw coordinate ((n : ℝ) * |x|)

theorem seedRaw_channel (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x ≠ 0)
    (n : ℕ) (positive : 0 < n) :
    seedRaw coordinate ((n : ℝ) * x) =
      if n ∈ channels x then burnolRieszSingleFourierSourceRaw coordinate ((n : ℝ) * |x|) else 0 := by
  classical
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have incidence : (n : ℝ) * x ∈ symmetricInterval q ↔ n ∈ channels x := by
    simp only [channels, Finset.mem_Icc, show 1 ≤ n from positive, true_and,
      symmetricInterval, mem_Icc, ← abs_le, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
      Nat.le_floor_iff' positive.ne', le_div_iff₀ absolute]
  unfold seedRaw
  by_cases active : n ∈ channels x
  · rw [indicator_of_mem (incidence.mpr active), if_pos active]
    simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using
      even_absolute _ (source_raw_even coordinate) ((n : ℝ) * x)
  · rw [indicator_of_notMem (fun member => active (incidence.mp member)), if_neg active]

/-- Once the original observation has seen all its channels, their exact finite sum remains. -/
theorem raw_event (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (complete : q / |x| < (N : ℝ)) : raw coordinate N x = eventRaw coordinate x := by
  classical
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have covered : q ≤ (N : ℝ) * |x| := (div_lt_iff₀ absolute).mp complete |>.le
  have subset : channels x ⊆ Finset.Ico 1 N := by
    intro n inside
    have members := Finset.mem_Icc.mp inside
    have bounded : (n : ℝ) ≤ q / |x| :=
      (Nat.le_floor_iff' (by omega : n ≠ 0)).mp members.2
    exact Finset.mem_Ico.mpr ⟨members.1, by exact_mod_cast bounded.trans_lt complete⟩
  rw [raw, continuous_raw_zero coordinate N x nonzero covered, sub_zero]
  unfold eventRaw
  calc
    _ = ∑ n ∈ Finset.Ico 1 N, if n ∈ channels x then
        burnolRieszSingleFourierSourceRaw coordinate ((n : ℝ) * |x|) else 0 := by
      apply Finset.sum_congr rfl
      intro n inside
      exact seedRaw_channel coordinate x nonzero n (Finset.mem_Ico.mp inside).1
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun member => member.2, fun member => ⟨subset member, member⟩⟩

theorem raw_eventually (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x ≠ 0) :
    ∀ᶠ N : ℕ in atTop, raw coordinate N x = eventRaw coordinate x := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_gt_atTop (q / |x|))] with N complete
  exact raw_event coordinate N x nonzero complete

end
end OriginalRieszFinitePairing.CoPoisson.Ward.DualSourceRaw
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
