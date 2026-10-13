import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ResponseProfile
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ResponseCounting

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

def seedRaw (side : Bool) (x : ℝ) : ℂ :=
  if |x| ≤ q then ResponseProfile.raw side |x| else 0

def raw (side : Bool) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, seedRaw side ((n : ℝ) * x)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw side (a * x)

def eventRaw (side : Bool) (x : ℝ) : ℂ :=
  ∑ n ∈ DualSourceRaw.channels x, ResponseProfile.raw side ((n : ℝ) * |x|)

def finite (side : Bool) (N : ℕ) : BurnolL2 :=
  DualSource.source N (burnolQuarterZeroExtension (ResponseProfile.state side : BurnolQuarterIntervalL2))

theorem seed_measurable (side : Bool) : Measurable (seedRaw side) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    ((ResponseProfile.continuous side).comp continuous_abs).measurable measurable_const

theorem seed_read (side : Bool) : (burnolQuarterZeroExtension
    (ResponseProfile.state side : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[volume] seedRaw side := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (ResponseProfile.read side)
  filter_upwards [burnolQuarterZeroExtension_coe (ResponseProfile.state side : BurnolQuarterIntervalL2), localRead]
    with x extension read
  rw [extension]
  by_cases inside : |x| ≤ q
  · rw [seedRaw, if_pos inside, indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside),
      read (abs_le.mp inside)]
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, ResponseProfile.even_on side x (abs_le.mp inside)]
  · rw [seedRaw, if_neg inside,
      indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h))]

theorem raw_measurable (side : Bool) (N : ℕ) : StronglyMeasurable (raw side N) := by
  have kernel : StronglyMeasurable (fun p : ℝ × ℝ => seedRaw side (p.1 * p.2)) :=
    ((seed_measurable side).comp (by fun_prop)).stronglyMeasurable
  have integralRead : StronglyMeasurable (fun x : ℝ => ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw side (a * x)) :=
    kernel.integral_prod_left'
  apply StronglyMeasurable.sub _ integralRead
  apply Finset.stronglyMeasurable_fun_sum
  intro n _
  exact ((seed_measurable side).comp (by fun_prop)).stronglyMeasurable

private theorem normalization_coeFn (side : Bool) (N : ℕ) :
    ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a
      (burnolQuarterZeroExtension (ResponseProfile.state side : BurnolQuarterIntervalL2)) : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw side (a * x) := by
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc 0 (N : ℝ))) _ (ContinuousChannels.channel_integrable 1 (N : ℝ) _)
    (fun p : ℝ × ℝ => seedRaw side (p.1 * p.2)) ((seed_measurable side).comp (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  exact DualSourceRaw.channel_coeFn _ _ (seed_read side) a inside.1

theorem finite_coeFn (side : Bool) (N : ℕ) : (finite side N : ℝ → ℂ) =ᵐ[volume] raw side N := by
  let seed := burnolQuarterZeroExtension (ResponseProfile.state side : BurnolQuarterIntervalL2)
  have channels : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n : ℝ) seed x = seedRaw side ((n : ℝ) * x) := by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn seed _ (seed_read side) (n : ℝ)
      (by exact_mod_cast (Finset.mem_Ico.mp n.2).1)
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed)
    (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel 1 (n : ℝ) seed),
    normalization_coeFn side N, channels] with x difference sum integral channel
  change ((∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed : BurnolL2) x = _
  rw [difference, Pi.sub_apply, sum, integral]
  unfold raw
  congr 1
  apply Finset.sum_congr rfl
  intro n inside
  exact channel ⟨n, inside⟩

theorem finite_mean (side : Bool) (N : ℕ) (positive : 0 < N) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (finite side N)) =
      2 * inner ℂ SmallScaleLog.logL2 (ResponseProfile.state side : BurnolQuarterIntervalL2) := by
  let b := ResponseProfile.state side
  have first : inner ℂ (intervalConstant q) (burnolQuarterRestriction (finite side N)) =
      inner ℂ (WindowCounting.windowSource N (intervalConstant q)) (b : BurnolQuarterIntervalL2) := by
    calc
      _ = inner ℂ (burnolQuarterZeroExtension (intervalConstant q)) (finite side N) :=
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

/-- The full continuous channel vanishes only after the actual mean-zero source interval is covered. -/
theorem continuous_raw_zero (side : Bool) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (covered : q ≤ (N : ℝ) * |x|) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw side (a * x)) = 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have even (a : ℝ) (positive : 0 < a) : seedRaw side (a * x) = seedRaw side (a * |x|) := by
    simp only [seedRaw, abs_mul, abs_of_pos positive, abs_abs]
  have scaled : (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw side (a * x)) =
      |x|⁻¹ • ∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), seedRaw side t := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a inside => even a inside.1),
      ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ absolute.ne', zero_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ) * |x|)]
  have intervalRead : (∫ t : ℝ in Ioc 0 ((N : ℝ) * |x|), seedRaw side t) =
      ∫ t : ℝ in Ioc 0 q, ResponseProfile.raw side t := by
    have pointwise : EqOn (seedRaw side) ((Ioc 0 q).indicator (ResponseProfile.raw side))
        (Ioc 0 ((N : ℝ) * |x|)) := by
      intro t inside
      simp only [seedRaw, abs_of_pos inside.1, indicator_apply, mem_Ioc, inside.1, true_and]
    rw [setIntegral_congr_fun measurableSet_Ioc pointwise, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc le_rfl covered)]
  rw [scaled, intervalRead, ResponseProfile.half_integral_zero, smul_zero]

theorem seed_channel (side : Bool) (x : ℝ) (nonzero : x ≠ 0)
    (n : ℕ) (positive : 0 < n) :
    seedRaw side ((n : ℝ) * x) =
      if n ∈ DualSourceRaw.channels x then ResponseProfile.raw side ((n : ℝ) * |x|) else 0 := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have incidence : (n : ℝ) * |x| ≤ q ↔ n ∈ DualSourceRaw.channels x := by
    simp only [DualSourceRaw.channels, Finset.mem_Icc, show 1 ≤ n from positive, true_and,
      Nat.le_floor_iff' positive.ne', le_div_iff₀ absolute]
  simp only [seedRaw, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), incidence]

theorem raw_event (side : Bool) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (complete : q / |x| < (N : ℝ)) : raw side N x = eventRaw side x := by
  classical
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have subset : DualSourceRaw.channels x ⊆ Finset.Ico 1 N := by
    intro n inside
    have members := Finset.mem_Icc.mp inside
    have bounded : (n : ℝ) ≤ q / |x| := (Nat.le_floor_iff' (by omega : n ≠ 0)).mp members.2
    exact Finset.mem_Ico.mpr ⟨members.1, by exact_mod_cast bounded.trans_lt complete⟩
  rw [raw, continuous_raw_zero side N x nonzero ((div_lt_iff₀ absolute).mp complete).le, sub_zero]
  calc
    _ = ∑ n ∈ Finset.Ico 1 N, if n ∈ DualSourceRaw.channels x then
        ResponseProfile.raw side ((n : ℝ) * |x|) else 0 := by
      apply Finset.sum_congr rfl
      intro n inside
      exact seed_channel side x nonzero n (Finset.mem_Ico.mp inside).1
    _ = _ := by
      rw [← Finset.sum_filter]
      unfold eventRaw
      congr 1
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun member => member.2, fun member => ⟨subset member, member⟩⟩

theorem raw_eventually (side : Bool) (x : ℝ) (nonzero : x ≠ 0) :
    ∀ᶠ N : ℕ in atTop, raw side N x = eventRaw side x := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop (q / |x|))] with N complete
  exact raw_event side N x nonzero complete

theorem event_aestronglyMeasurable (side : Bool) :
    AEStronglyMeasurable (eventRaw side) volume := by
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun N => (raw_measurable side N).aestronglyMeasurable)
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  apply tendsto_const_nhds.congr'
  filter_upwards [raw_eventually side x nonzero] with N read
  exact read.symm

theorem event_outside (side : Bool) (x : ℝ) (outside : q < |x|) :
    eventRaw side x = 0 := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have index : ⌊q / |x|⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one absolute).mpr outside)
  rw [eventRaw, DualSourceRaw.channels, index]
  simp


private theorem cell_error (f : ℝ → ℂ) (continuous : ContinuousOn f (Icc 0 q))
    (L : ℝ) (nonnegative : 0 ≤ L)
    (lipschitz : ∀ x ∈ Icc 0 q, ∀ y ∈ Icc 0 q, ‖f y - f x‖ ≤ L * ‖y - x‖)
    (a x : ℝ) (positive : 0 < x) (lower : 0 ≤ a) (upper : a + x ≤ q) :
    ‖(x : ℂ) * f (a + x) - ∫ t : ℝ in a..(a + x), f t‖ ≤ L * x ^ 2 := by
  have ordered : a ≤ a + x := by linarith
  have subset : Icc a (a + x) ⊆ Icc 0 q := fun t inside => ⟨lower.trans inside.1, inside.2.trans upper⟩
  have regular : IntervalIntegrable f volume a (a + x) :=
    (continuous.mono subset).intervalIntegrable_of_Icc ordered
  have identity : (x : ℂ) * f (a + x) - ∫ t : ℝ in a..(a + x), f t =
      ∫ t : ℝ in a..(a + x), f (a + x) - f t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const regular, intervalIntegral.integral_const,
      add_sub_cancel_left, Complex.real_smul]
  rw [identity]
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := a + x) (C := L * x) (f := fun t : ℝ => f (a + x) - f t) (fun t inside => by
      have located : t ∈ Icc a (a + x) := Ioc_subset_Icc_self
        (by simpa only [uIoc_of_le ordered] using inside)
      have actual := lipschitz t (subset located) (a + x) ⟨by linarith, upper⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr located.2)] at actual
      exact actual.trans (mul_le_mul_of_nonneg_left (by linarith [located.1]) nonnegative))
  simpa only [add_sub_cancel_left, abs_of_pos positive, pow_two, mul_assoc] using bound

private theorem complete_grid_error (f : ℝ → ℂ) (continuous : ContinuousOn f (Icc 0 q))
    (L : ℝ) (nonnegative : 0 ≤ L)
    (lipschitz : ∀ x ∈ Icc 0 q, ∀ y ∈ Icc 0 q, ‖f y - f x‖ ≤ L * ‖y - x‖)
    (x : ℝ) (positive : 0 < x) (M : ℕ) (inside : (M : ℝ) * x ≤ q) :
    ‖(x : ℂ) * (∑ n ∈ Finset.range M, f (((n + 1 : ℕ) : ℝ) * x)) -
      ∫ t : ℝ in (0 : ℝ)..((M : ℝ) * x), f t‖ ≤ L * ((M : ℝ) * x) * x := by
  have upper (n : ℕ) (hn : n < M) : (n : ℝ) * x + x ≤ q := by
    have natBound : (n : ℝ) + 1 ≤ M := by exact_mod_cast hn
    nlinarith
  have integrable (n : ℕ) (hn : n < M) :
      IntervalIntegrable f volume ((n : ℝ) * x) (((n + 1 : ℕ) : ℝ) * x) := by
    apply (continuous.mono _).intervalIntegrable_of_Icc (by push_cast; nlinarith)
    intro t ht
    constructor
    · exact (mul_nonneg (Nat.cast_nonneg n) positive.le).trans ht.1
    · exact ht.2.trans (by push_cast; nlinarith [upper n hn])
  have adjacent := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ) * x) integrable
  simp only [Nat.cast_zero, zero_mul] at adjacent
  rw [← adjacent, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range M, ‖(x : ℂ) * f (((n + 1 : ℕ) : ℝ) * x) -
        ∫ t : ℝ in ((n : ℝ) * x)..(((n + 1 : ℕ) : ℝ) * x), f t‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range M, L * x ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have actual := cell_error f continuous L nonnegative lipschitz ((n : ℝ) * x) x positive
        (mul_nonneg (Nat.cast_nonneg n) positive.le) (upper n (Finset.mem_range.mp hn))
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using actual
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring


private theorem partial_quadrature (side : Bool)
    (N : ℕ) (indexPositive : 0 < N) (x : ℝ) (positive : 0 < x) (inside : (N : ℝ) * x ≤ q) :
    ‖(∑ n ∈ Finset.Ico 1 N, ResponseProfile.raw side ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), ResponseProfile.raw side t‖ ≤
      ResponseProfile.slopeBound side * q + ResponseProfile.bound side := by
  have grid := complete_grid_error _ (ResponseProfile.continuous side).continuousOn
    (ResponseProfile.slopeBound side) (ResponseProfile.slopeBound_nonnegative side)
    (fun a ha b hb => ResponseProfile.lipschitz side a ha b hb) x positive N inside
  have indices : (∑ n ∈ Finset.Ico 1 N, ResponseProfile.raw side ((n : ℝ) * x)) +
      ResponseProfile.raw side ((N : ℝ) * x) =
      ∑ n ∈ Finset.range N, ResponseProfile.raw side (((n + 1 : ℕ) : ℝ) * x) := by
    rw [Finset.sum_Ico_add_eq_sum_Icc (Nat.one_le_iff_ne_zero.mpr indexPositive.ne'),
      ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  have whole : ‖(∑ n ∈ Finset.range N, ResponseProfile.raw side (((n + 1 : ℕ) : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), ResponseProfile.raw side t‖ ≤
      ResponseProfile.slopeBound side * q := by
    have scaled : (∑ n ∈ Finset.range N, ResponseProfile.raw side (((n + 1 : ℕ) : ℝ) * x)) -
        (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), ResponseProfile.raw side t =
        (x : ℂ)⁻¹ * ((x : ℂ) * (∑ n ∈ Finset.range N, ResponseProfile.raw side (((n + 1 : ℕ) : ℝ) * x)) -
          ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), ResponseProfile.raw side t) := by
      rw [mul_sub, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr positive.ne')]
    rw [scaled, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    calc
      _ ≤ x⁻¹ * (ResponseProfile.slopeBound side * ((N : ℝ) * x) * x) :=
        mul_le_mul_of_nonneg_left grid (inv_nonneg.mpr positive.le)
      _ = ResponseProfile.slopeBound side * ((N : ℝ) * x) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left inside (ResponseProfile.slopeBound_nonnegative side)
  have last := ResponseProfile.bounded side ((N : ℝ) * x) ⟨by positivity, inside⟩
  have difference : (∑ n ∈ Finset.Ico 1 N, ResponseProfile.raw side ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), ResponseProfile.raw side t =
      ((∑ n ∈ Finset.range N, ResponseProfile.raw side (((n + 1 : ℕ) : ℝ) * x)) -
        (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), ResponseProfile.raw side t) -
      ResponseProfile.raw side ((N : ℝ) * x) := by rw [← indices]; ring
  rw [difference]
  exact (norm_sub_le _ _).trans (add_le_add whole last)


def bound (side : Bool) : ℝ := ResponseProfile.slopeBound side * q + ResponseProfile.bound side

theorem bound_nonnegative (side : Bool) : 0 ≤ bound side :=
  add_nonneg (mul_nonneg (ResponseProfile.slopeBound_nonnegative side) (by norm_num))
    (ResponseProfile.bound_nonnegative side)

theorem event_bound (side : Bool) (x : ℝ) : ‖eventRaw side x‖ ≤ bound side := by
  by_cases atZero : x = 0
  · simp only [atZero, eventRaw, DualSourceRaw.channels, abs_zero, div_zero, Nat.floor_zero,
      Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty, norm_zero]
    exact bound_nonnegative side
  have mean : (∫ t : ℝ in (0 : ℝ)..q, ResponseProfile.raw side t) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q), ResponseProfile.half_integral_zero]
  have actual := RegularQuadrature.quadrature_bound (ResponseProfile.raw side)
    (ResponseProfile.continuous side).continuousOn (ResponseProfile.slopeBound side) (ResponseProfile.bound side)
    (ResponseProfile.slopeBound_nonnegative side) (ResponseProfile.bound_nonnegative side)
    (fun a ha b hb => ResponseProfile.lipschitz side a ha b hb) (ResponseProfile.bounded side)
    |x| (abs_pos.mpr atZero)
  simpa only [mean, mul_zero, sub_zero, eventRaw, DualSourceRaw.channels, bound] using actual

private theorem partial_raw (side : Bool) (N : ℕ) (x : ℝ) (positive : 0 < x)
    (inside : (N : ℝ) * x ≤ q) : raw side N x =
    (∑ n ∈ Finset.Ico 1 N, ResponseProfile.raw side ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), ResponseProfile.raw side t := by
  have seed (a : ℝ) (ha : 0 < a) (haN : a ≤ N) : seedRaw side (a * x) = ResponseProfile.raw side (a * x) := by
    rw [seedRaw, abs_of_pos (mul_pos ha positive), if_pos ((mul_le_mul_of_nonneg_right haN positive.le).trans inside)]
  have channels : (∑ n ∈ Finset.Ico 1 N, seedRaw side ((n : ℝ) * x)) =
      ∑ n ∈ Finset.Ico 1 N, ResponseProfile.raw side ((n : ℝ) * x) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact seed n (by exact_mod_cast (Finset.mem_Ico.mp hn).1)
      (by exact_mod_cast (Finset.mem_Ico.mp hn).2.le)
  unfold raw
  rw [channels, setIntegral_congr_fun measurableSet_Ioc (fun a located => seed a located.1 located.2),
    ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
    intervalIntegral.integral_comp_mul_right _ positive.ne', zero_mul, Complex.real_smul, ofReal_inv]

theorem raw_bound (side : Bool) (N : ℕ) (indexPositive : 0 < N) (x : ℝ) (nonzero : x ≠ 0) :
    ‖raw side N x‖ ≤ bound side := by
  have absolute : raw side N x = raw side N |x| := by
    simp only [raw, seedRaw, abs_mul, abs_abs]
  have positive := abs_pos.mpr nonzero
  by_cases covered : q < (N : ℝ) * |x|
  · rw [raw_event side N x nonzero ((div_lt_iff₀ positive).mpr covered)]
    exact event_bound side x
  · rw [absolute, partial_raw side N |x| positive (le_of_not_gt covered)]
    exact partial_quadrature side N indexPositive |x| positive (le_of_not_gt covered)

theorem raw_outside (side : Bool) (N : ℕ) (indexPositive : 0 < N) (x : ℝ) (outside : q < |x|) :
    raw side N x = 0 := by
  have positive : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have complete : q / |x| < (N : ℝ) := ((div_lt_one positive).mpr outside).trans_le
    (by exact_mod_cast indexPositive)
  rw [raw_event side N x (abs_pos.mp positive) complete, event_outside side x outside]

theorem event_memLp_two (side : Bool) : MemLp (eventRaw side) 2 volume := by
  have dominant : MemLp ((symmetricInterval q).indicator (fun _ : ℝ => (bound side : ℂ))) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval q) _ (Or.inr (by simp [symmetricInterval]))
  apply dominant.mono (event_aestronglyMeasurable side)
  filter_upwards with x
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bound_nonnegative side)]
    exact event_bound side x
  · rw [indicator_of_notMem inside, event_outside side x (lt_of_not_ge (fun small => inside (abs_le.mp small))), norm_zero]

def value (side : Bool) : BurnolL2 := (event_memLp_two side).toLp (eventRaw side)

theorem value_coeFn (side : Bool) : (value side : ℝ → ℂ) =ᵐ[volume] eventRaw side :=
  (event_memLp_two side).coeFn_toLp

theorem value_support (side : Bool) : OriginalPaPhysicalGreen.originalPhysicalCutoff q (value side) = value side := by
  apply OriginalRieszFiniteColumns.cutoff_eq_self_of_ae_zero
  filter_upwards [value_coeFn side] with x read outside
  rw [read, event_outside side x (lt_of_not_ge (fun small => outside (abs_le.mp small)))]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ResponseCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
