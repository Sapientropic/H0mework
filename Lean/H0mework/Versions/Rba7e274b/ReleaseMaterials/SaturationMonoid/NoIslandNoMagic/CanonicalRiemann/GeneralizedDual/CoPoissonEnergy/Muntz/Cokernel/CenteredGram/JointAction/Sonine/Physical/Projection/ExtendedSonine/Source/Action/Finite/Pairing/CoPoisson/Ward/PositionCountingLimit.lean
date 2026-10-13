import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionCountingLimit

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal
open OriginalRieszSource PositionCounting
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

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


private theorem return_partial_bound (coordinate : BurnolCompletedMellinCoordinate)
    (N : ℕ) (indexPositive : 0 < N) (x : ℝ) (positive : 0 < x) (inside : (N : ℝ) * x ≤ q) :
    ‖(∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t‖ ≤
      returnSlopeBound coordinate * q + returnBound coordinate := by
  have grid := complete_grid_error _ (burnolRieszReturnRaw_continuous coordinate).continuousOn
    (returnSlopeBound coordinate) (return_slope_nonnegative coordinate)
    (fun a ha b hb => return_lipschitz coordinate a b ha hb) x positive N inside
  have indices : (∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) +
      burnolRieszReturnRaw coordinate ((N : ℝ) * x) =
      ∑ n ∈ Finset.range N, burnolRieszReturnRaw coordinate (((n + 1 : ℕ) : ℝ) * x) := by
    rw [Finset.sum_Ico_add_eq_sum_Icc (Nat.one_le_iff_ne_zero.mpr indexPositive.ne'),
      ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  have whole : ‖(∑ n ∈ Finset.range N, burnolRieszReturnRaw coordinate (((n + 1 : ℕ) : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t‖ ≤
      returnSlopeBound coordinate * q := by
    have scaled : (∑ n ∈ Finset.range N, burnolRieszReturnRaw coordinate (((n + 1 : ℕ) : ℝ) * x)) -
        (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t =
        (x : ℂ)⁻¹ * ((x : ℂ) * (∑ n ∈ Finset.range N, burnolRieszReturnRaw coordinate (((n + 1 : ℕ) : ℝ) * x)) -
          ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t) := by
      rw [mul_sub, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr positive.ne')]
    rw [scaled, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    calc
      _ ≤ x⁻¹ * (returnSlopeBound coordinate * ((N : ℝ) * x) * x) :=
        mul_le_mul_of_nonneg_left grid (inv_nonneg.mpr positive.le)
      _ = returnSlopeBound coordinate * ((N : ℝ) * x) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left inside (return_slope_nonnegative coordinate)
  have last := return_bound coordinate ((N : ℝ) * x) ⟨by positivity, inside⟩
  have difference : (∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t =
      ((∑ n ∈ Finset.range N, burnolRieszReturnRaw coordinate (((n + 1 : ℕ) : ℝ) * x)) -
        (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t) -
      burnolRieszReturnRaw coordinate ((N : ℝ) * x) := by rw [← indices]; ring
  rw [difference]
  exact (norm_sub_le _ _).trans (add_le_add whole last)

private theorem partial_raw (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (indexPositive : 0 < N)
    (x : ℝ) (positive : 0 < x) (inside : (N : ℝ) * x ≤ q) :
    raw coordinate N x =
      (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) * FiniteForcing.coefficient (star coordinate.value) N +
        GapEuler.gapMean q coordinate -
      ((∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
        (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t) := by
  have seed (a : ℝ) (ha : 0 < a) (haN : a ≤ N) : seedRaw coordinate (a * x) = positionSource coordinate (a * x) := by
    rw [seedRaw, abs_of_pos (mul_pos ha positive), if_pos ((mul_le_mul_of_nonneg_right haN positive.le).trans inside)]
  have continuousRead : (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)) =
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), positionSource coordinate t := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a located => seed a located.1 located.2),
      ← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ positive.ne', zero_mul, Complex.real_smul, Complex.ofReal_inv]
  have power : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-star coordinate.value)) volume 0 ((N : ℝ) * x) :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [neg_re, star_def, conj_re]; linarith [coordinate.belowOne])
  have returned : IntervalIntegrable (burnolRieszReturnRaw coordinate) volume 0 ((N : ℝ) * x) :=
    (burnolRieszReturnRaw_continuous coordinate).intervalIntegrable _ _
  have notPole : 1 - star coordinate.value ≠ 0 := by
    intro h
    have re := congrArg Complex.re h
    simp only [sub_re, one_re, star_def, conj_re, zero_re] at re
    linarith [coordinate.belowOne]
  have powerMass : (∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), (t : ℂ) ^ (-star coordinate.value)) =
      ((((N : ℝ) * x : ℝ) : ℂ) ^ (1 - star coordinate.value)) / (1 - star coordinate.value) := by
    rw [integral_cpow (Or.inl (by simp only [neg_re, star_def, conj_re]; linarith [coordinate.belowOne])),
      show -star coordinate.value + 1 = 1 - star coordinate.value by ring, Complex.ofReal_zero,
      zero_cpow notPole, sub_zero]
  have normalizedPower : (x : ℂ)⁻¹ * ((((N : ℝ) * x : ℝ) : ℂ) ^ (1 - star coordinate.value)) =
      (x : ℂ) ^ (-star coordinate.value) * (N : ℂ) ^ (1 - star coordinate.value) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg N) positive.le,
      Complex.ofReal_natCast, show 1 - star coordinate.value = -star coordinate.value + 1 by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'), cpow_one]
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  have powers : (∑ n ∈ Finset.Ico 1 N, (((n : ℝ) * x : ℝ) : ℂ) ^ (-star coordinate.value)) =
      (x : ℂ) ^ (-star coordinate.value) * (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-star coordinate.value)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) positive.le, Complex.ofReal_natCast, mul_comm]
  rw [raw, continuousRead]
  have sourceSum : (∑ n ∈ Finset.Ico 1 N, seedRaw coordinate ((n : ℝ) * x)) =
      (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) * (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-star coordinate.value)) -
      ((N : ℂ) - 1) * GapEuler.gapMean q coordinate -
      (∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) := by
    rw [Finset.sum_congr rfl (fun (n : ℕ) hn => seed (n : ℝ) (by exact_mod_cast (Finset.mem_Ico.mp hn).1)
      (by exact_mod_cast (Finset.mem_Ico.mp hn).2.le))]
    simp only [positionSource, Finset.sum_sub_distrib, ← Finset.mul_sum, powers,
      Finset.sum_const, Nat.card_Ico, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr indexPositive.ne'), Nat.cast_one, nsmul_eq_mul]
    ring
  rw [sourceSum]
  unfold positionSource
  rw [intervalIntegral.integral_sub ((power.const_mul _).sub intervalIntegrable_const) returned,
    intervalIntegral.integral_sub (power.const_mul _) intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, powerMass]
  simp only [sub_zero, Complex.real_smul]
  have scaled := normalizedPower
  unfold FiniteForcing.coefficient
  rw [mul_sub, mul_sub]
  rw [show (x : ℂ)⁻¹ * ((1 / 2 : ℂ) * ((((N : ℝ) * x : ℝ) : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value))) =
    (1 / 2 : ℂ) * ((x : ℂ)⁻¹ * (((N : ℝ) * x : ℝ) : ℂ) ^ (1 - star coordinate.value)) / (1 - star coordinate.value) by ring,
    scaled, Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  simp only [mul_comm (x : ℝ)]
  ring

private theorem source_constant_nonnegative (coordinate : BurnolCompletedMellinCoordinate) :
    0 ≤ DirichletRate.constant (star coordinate.value) := by
  have positive : 0 < (star coordinate.value).re := by simp only [star_def, conj_re]; linarith [coordinate.rightHalf]
  unfold DirichletRate.constant
  positivity

private theorem partial_bound (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (N : ℕ) (indexPositive : 0 < N)
    (x : ℝ) (positive : 0 < x) (inside : (N : ℝ) * x ≤ q) :
    ‖raw coordinate N x‖ ≤
      (1 / 2 : ℝ) * DirichletRate.constant (star coordinate.value) * x ^ (-coordinate.value.re) +
      ‖GapEuler.gapMean q coordinate‖ + (returnSlopeBound coordinate * q + returnBound coordinate) := by
  have selected : riemannZeta (star coordinate.value) = 0 := by
    simpa only [star_def, zero, map_zero] using riemannZeta_conj coordinate.value
  have positiveSource : 0 < (star coordinate.value).re := by simp only [star_def, conj_re]; linarith [coordinate.rightHalf]
  have rate := DirichletRate.coefficient_rate (star coordinate.value) positiveSource
    (by simpa only [star_def, conj_re] using coordinate.belowOne) N indexPositive
  rw [selected, sub_zero] at rate
  have decay : (N : ℝ) ^ (-(star coordinate.value).re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast indexPositive) (neg_nonpos.mpr positiveSource.le)
  have coefficient : ‖FiniteForcing.coefficient (star coordinate.value) N‖ ≤ DirichletRate.constant (star coordinate.value) :=
    rate.trans ((mul_le_mul_of_nonneg_left decay (source_constant_nonnegative coordinate)).trans_eq (mul_one _))
  have singular : ‖(1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) * FiniteForcing.coefficient (star coordinate.value) N‖ ≤
      (1 / 2 : ℝ) * DirichletRate.constant (star coordinate.value) * x ^ (-coordinate.value.re) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive]
    simp only [neg_re, star_def, conj_re]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left coefficient (by positivity)).trans_eq (by ring_nf; rfl)
  rw [partial_raw coordinate N indexPositive x positive inside]
  exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    (add_le_add (add_le_add singular le_rfl) (return_partial_bound coordinate N indexPositive x positive inside)))

def majorant (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * DirichletRate.constant (star coordinate.value) * |x| ^ (-coordinate.value.re) +
    PositionCounting.bound coordinate + ‖GapEuler.gapMean q coordinate‖ +
      (returnSlopeBound coordinate * q + returnBound coordinate)

private theorem raw_absolute (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) :
    raw coordinate N x = raw coordinate N |x| := by
  simp only [raw, seedRaw, abs_mul, abs_abs]

theorem raw_bound (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) (indexPositive : 0 < N) (x : ℝ) (nonzero : x ≠ 0) :
    ‖raw coordinate N x‖ ≤ majorant coordinate x := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have base := bound_nonnegative coordinate
  have slope := return_slope_nonnegative coordinate
  have valueBound := return_bound_nonnegative coordinate
  have constant := source_constant_nonnegative coordinate
  rw [raw_absolute coordinate N x]
  by_cases covered : q < (N : ℝ) * |x|
  · rw [raw_event coordinate N |x| (abs_pos.mp (by simpa only [abs_abs] using absolute))
      (by rw [abs_abs]; exact (div_lt_iff₀ absolute).mpr covered)]
    apply (event_bound coordinate zero |x|).trans
    have extra : 0 ≤ (1 / 2 : ℝ) * DirichletRate.constant (star coordinate.value) * |x| ^ (-coordinate.value.re) +
        ‖GapEuler.gapMean q coordinate‖ + (returnSlopeBound coordinate * q + returnBound coordinate) := by positivity
    unfold majorant
    linarith
  · have actual := partial_bound coordinate zero N indexPositive |x| absolute (le_of_not_gt covered)
    exact actual.trans (by unfold majorant; linarith)

theorem majorant_integrable (coordinate : BurnolCompletedMellinCoordinate) : Integrable (majorant coordinate) μq := by
  have power : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ ((-coordinate.value.re : ℝ) : ℂ)) volume (-q) q :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [ofReal_re]; linarith [coordinate.belowOne])
  have absolutePower : Integrable (fun x : ℝ => |x| ^ (-coordinate.value.re)) μq := by
    have actual := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q ≤ q)).mp power.norm
    apply actual.congr
    filter_upwards with x
    simp only [Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs]
  exact (((absolutePower.const_mul _).add (integrable_const _)).add (integrable_const _)).add (integrable_const _)

theorem finite_integrable (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) : Integrable (raw coordinate N) μq := by
  by_cases atZero : N = 0
  · subst N
    have vanishes : raw coordinate 0 = (0 : ℝ → ℂ) := by
      funext x
      simp [raw]
    rw [vanishes]
    exact integrable_zero ℝ ℂ μq
  · apply (majorant_integrable coordinate).mono' (raw_measurable coordinate N).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x nonzero
    exact raw_bound coordinate zero N (Nat.pos_of_ne_zero atZero) x nonzero

/-- The actual finite L¹ source converges on the entire original q-window to the source-generated L² result. -/
theorem finite_tendsto_value_L1 (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => ∫ x : ℝ, ‖raw coordinate N x - PositionCounting.value coordinate zero x‖ ∂μq)
      atTop (𝓝 0) := by
  have eventMeasured : AEStronglyMeasurable (eventRaw coordinate) μq :=
    (event_aestronglyMeasurable coordinate).mono_measure Measure.restrict_le_self
  have measured : ∀ᶠ N : ℕ in atTop, AEStronglyMeasurable (fun x : ℝ => ‖raw coordinate N x - eventRaw coordinate x‖) μq :=
    Eventually.of_forall (fun N => ((raw_measurable coordinate N).aestronglyMeasurable.sub eventMeasured).norm)
  have dominated : ∀ᶠ N : ℕ in atTop, ∀ᵐ x : ℝ ∂μq,
      ‖‖raw coordinate N x - eventRaw coordinate x‖‖ ≤ majorant coordinate x + PositionCounting.bound coordinate := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positive
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x nonzero
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (raw_bound coordinate zero N positive x nonzero) (event_bound coordinate zero x))
  have pointwise : ∀ᵐ x : ℝ ∂μq, Tendsto (fun N : ℕ => ‖raw coordinate N x - eventRaw coordinate x‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x nonzero
    apply tendsto_const_nhds.congr'
    filter_upwards [raw_eventually coordinate x nonzero] with N actual
    simp only [actual, sub_self, norm_zero]
  have actual := tendsto_integral_filter_of_dominated_convergence
    (fun x => majorant coordinate x + PositionCounting.bound coordinate) measured dominated
    ((majorant_integrable coordinate).add (integrable_const _)) pointwise
  simp only [integral_zero] at actual
  apply actual.congr'
  apply Eventually.of_forall
  intro N
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (value_coeFn coordinate zero)] with x read
  rw [read]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionCountingLimit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
