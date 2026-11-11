import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCountingSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.TrapezoidSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.KCountingSource

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal
open OriginalRieszSource OriginalRieszSourceGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem partial_raw (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ)
    (positiveN : 0 < N) (x : ℝ) (positive : 0 < x) (inside : (N : ℝ) * x ≤ q) :
    raw coordinate N x = -GapEuler.gapMean q coordinate +
      ((∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
        (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t) := by
  have channel (a : ℝ) (ha : 0 < a) (upper : a ≤ N) :
      baseRaw coordinate (a * x) = GapEuler.gapMean q coordinate + burnolRieszReturnRaw coordinate (a * x) := by
    rw [baseRaw, abs_of_pos (mul_pos ha positive), if_pos ((mul_le_mul_of_nonneg_right upper positive.le).trans inside)]
  have discrete : (∑ n ∈ Finset.Ico 1 N, baseRaw coordinate ((n : ℝ) * x)) =
      ((N : ℂ) - 1) * GapEuler.gapMean q coordinate +
        ∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x) := by
    calc
      _ = ∑ n ∈ Finset.Ico 1 N, (GapEuler.gapMean q coordinate + burnolRieszReturnRaw coordinate ((n : ℝ) * x)) := by
        apply Finset.sum_congr rfl
        intro n member
        exact channel n (by exact_mod_cast (Finset.mem_Ico.mp member).1)
          (by exact_mod_cast (Finset.mem_Ico.mp member).2.le)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
          Nat.cast_sub positiveN, Nat.cast_one]
  have returned : IntegrableOn (fun a : ℝ => burnolRieszReturnRaw coordinate (a * x)) (Ioc 0 (N : ℝ)) :=
    ((burnolRieszReturnRaw_continuous coordinate).comp (by fun_prop)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have integral : (∫ a : ℝ in Ioc 0 (N : ℝ), baseRaw coordinate (a * x)) =
      (N : ℂ) * GapEuler.gapMean q coordinate +
        (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun a located => channel a located.1 located.2),
      integral_add (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) returned,
      ← intervalIntegral.integral_of_le (Nat.cast_nonneg N), intervalIntegral.integral_const]
    rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      intervalIntegral.integral_comp_mul_right _ positive.ne', zero_mul]
    simp only [sub_zero, Complex.real_smul, ofReal_inv, ofReal_natCast]
  rw [raw, discrete, integral]
  ring

private theorem partial_quadrature (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ)
    (positiveN : 0 < N) (x : ℝ) (positive : 0 < x) (inside : (N : ℝ) * x ≤ q) :
    ‖(∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t‖ ≤
        4 * PositionCounting.returnSlopeBound coordinate * q + PositionCounting.returnBound coordinate := by
  have grid := TrapezoidSource.grid_bound (burnolRieszReturnRaw coordinate) (burnolRieszReturnRawDerivative coordinate)
    (burnolRieszReturnRaw_continuous coordinate).continuousOn
    (fun t _ => burnolRieszReturnRaw_hasDerivAt coordinate t)
    x (2 * PositionCounting.returnSlopeBound coordinate) positive
    (mul_nonneg (by norm_num) (PositionCounting.return_slope_nonnegative coordinate)) N inside
    (fun a ha b hb _ => (norm_sub_le _ _).trans ((add_le_add (PositionCounting.return_slope_bound coordinate b hb)
      (PositionCounting.return_slope_bound coordinate a ha)).trans_eq (by ring)))
  have indices := Finset.sum_Ico_add_eq_sum_Icc (f := fun n : ℕ => burnolRieszReturnRaw coordinate ((n : ℝ) * x))
    (show 1 ≤ N from positiveN)
  have identity : (∑ n ∈ Finset.Ico 1 N, burnolRieszReturnRaw coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..((N : ℝ) * x), burnolRieszReturnRaw coordinate t =
      TrapezoidSource.grid (burnolRieszReturnRaw coordinate) x N -
        (burnolRieszReturnRaw coordinate ((N : ℝ) * x) + burnolRieszReturnRaw coordinate 0) / 2 := by
    unfold TrapezoidSource.grid
    rw [← indices]
    ring
  have endpoints : ‖(burnolRieszReturnRaw coordinate ((N : ℝ) * x) + burnolRieszReturnRaw coordinate 0) / 2‖ ≤
      PositionCounting.returnBound coordinate := by
    rw [norm_div, Complex.norm_ofNat]
    have bound := (norm_add_le _ _).trans (add_le_add (PositionCounting.return_bound coordinate ((N : ℝ) * x) ⟨by positivity, inside⟩)
      (PositionCounting.return_bound coordinate 0 (by norm_num)))
    linarith
  rw [identity]
  exact (norm_sub_le _ _).trans ((add_le_add grid endpoints).trans_eq (by ring))

private def arithmeticConstant (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  DirichletRate.constant (star coordinate.value)

private theorem arithmetic_nonnegative (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ arithmeticConstant coordinate := by
  have positive : 0 < coordinate.value.re := by linarith [coordinate.rightHalf]
  unfold arithmeticConstant DirichletRate.constant
  simp only [star_def, conj_re]
  positivity

private theorem coefficient_bound (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) (positiveN : 0 < N) : ‖FiniteForcing.coefficient (star coordinate.value) N‖ ≤
      arithmeticConstant coordinate * (N : ℝ) ^ (-coordinate.value.re) := by
  have selected : riemannZeta (star coordinate.value) = 0 := by
    simpa only [star_def, zero, map_zero] using riemannZeta_conj coordinate.value
  have actual := DirichletRate.coefficient_rate (star coordinate.value)
    (by simp only [star_def, conj_re]; linarith [coordinate.rightHalf])
    (by simpa only [star_def, conj_re] using coordinate.belowOne) N positiveN
  rw [selected, sub_zero] at actual
  simpa only [arithmeticConstant, star_def, conj_re] using actual

private def headBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  ‖GapEuler.gapMean q coordinate‖ + 4 * PositionCounting.returnSlopeBound coordinate * q + PositionCounting.returnBound coordinate +
    (1 / 2 : ℝ) * arithmeticConstant coordinate * q ^ (-coordinate.value.re) + PositionCounting.bound coordinate

private theorem head_nonnegative (coordinate : BurnolCompletedMellinCoordinate) : 0 ≤ headBound coordinate := by
  have first := PositionCounting.return_slope_nonnegative coordinate
  have second := PositionCounting.return_bound_nonnegative coordinate
  have third := arithmetic_nonnegative coordinate
  have fourth := PositionCounting.bound_nonnegative coordinate
  unfold headBound
  positivity

private theorem raw_head_bound (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) (positiveN : 0 < N) (x : ℝ) (nonzero : x ≠ 0) : ‖raw coordinate N x‖ ≤ headBound coordinate := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have positiveBase : (0 : ℝ) < N := by exact_mod_cast positiveN
  have same : raw coordinate N x = raw coordinate N |x| := by simp only [raw, baseRaw, abs_mul, abs_abs]
  have base := coefficient_bound coordinate zero N positiveN
  by_cases covered : q < (N : ℝ) * |x|
  · rw [raw_synthesis coordinate N x nonzero, PositionCounting.raw_event coordinate N x nonzero ((div_lt_iff₀ absolute).mpr covered)]
    have power : ‖(1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value) *
        FiniteForcing.coefficient (star coordinate.value) N‖ ≤
        (1 / 2 : ℝ) * arithmeticConstant coordinate * q ^ (-coordinate.value.re) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos absolute]
      simp only [neg_re, star_def, conj_re]
      norm_num only [norm_div, norm_one, Complex.norm_ofNat]
      have product : |x| ^ (-coordinate.value.re) * (N : ℝ) ^ (-coordinate.value.re) =
          ((N : ℝ) * |x|) ^ (-coordinate.value.re) := by rw [Real.mul_rpow positiveBase.le absolute.le]; ring
      calc
        _ ≤ (1 / 2 : ℝ) * |x| ^ (-coordinate.value.re) *
            (arithmeticConstant coordinate * (N : ℝ) ^ (-coordinate.value.re)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [star_def] using base
        _ = (1 / 2 : ℝ) * arithmeticConstant coordinate * ((N : ℝ) * |x|) ^ (-coordinate.value.re) := by
          rw [← product]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by norm_num) covered.le (by linarith [coordinate.rightHalf]))
          (mul_nonneg (by norm_num) (arithmetic_nonnegative coordinate))
    have actual := (norm_sub_le _ _).trans (add_le_add power (PositionCounting.event_bound coordinate zero x))
    have extra : 0 ≤ ‖GapEuler.gapMean q coordinate‖ + 4 * PositionCounting.returnSlopeBound coordinate * q + PositionCounting.returnBound coordinate := by
      have first := PositionCounting.return_slope_nonnegative coordinate
      have second := PositionCounting.return_bound_nonnegative coordinate
      positivity
    unfold headBound
    linarith
  · rw [same, partial_raw coordinate N positiveN |x| absolute (le_of_not_gt covered)]
    have actual := (norm_add_le _ _).trans (add_le_add (le_refl ‖-GapEuler.gapMean q coordinate‖)
      (partial_quadrature coordinate N positiveN |x| absolute (le_of_not_gt covered)))
    rw [norm_neg] at actual
    have extra : 0 ≤ (1 / 2 : ℝ) * arithmeticConstant coordinate * q ^ (-coordinate.value.re) + PositionCounting.bound coordinate := by
      have first := arithmetic_nonnegative coordinate
      have second := PositionCounting.bound_nonnegative coordinate
      positivity
    unfold headBound
    linarith

private theorem raw_tail_bound (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) (positiveN : 0 < N) (x : ℝ) (outside : q < |x|) :
    ‖raw coordinate N x‖ ≤ (1 / 2 : ℝ) * arithmeticConstant coordinate * |x| ^ (-coordinate.value.re) := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have coefficient := coefficient_bound coordinate zero N positiveN
  have power : (N : ℝ) ^ (-coordinate.value.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast positiveN) (by linarith [coordinate.rightHalf])
  have bounded : ‖FiniteForcing.coefficient (star coordinate.value) N‖ ≤ arithmeticConstant coordinate :=
    coefficient.trans ((mul_le_mul_of_nonneg_left power (arithmetic_nonnegative coordinate)).trans_eq (mul_one _))
  rw [raw_synthesis coordinate N x (abs_pos.mp absolute), PositionCountedEuler.raw_outside coordinate N x outside, sub_zero,
    norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos absolute]
  simp only [neg_re, star_def, conj_re]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left bounded (by positivity)).trans_eq (by ring)

def envelope (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℝ :=
  if |x| ≤ q then headBound coordinate else (1 / 2 : ℝ) * arithmeticConstant coordinate * |x| ^ (-coordinate.value.re)

theorem envelope_nonnegative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : 0 ≤ envelope coordinate x := by
  unfold envelope
  split_ifs
  · exact head_nonnegative coordinate
  · have positive := arithmetic_nonnegative coordinate
    positivity

theorem raw_bound (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) (positiveN : 0 < N) (x : ℝ) (nonzero : x ≠ 0) : ‖raw coordinate N x‖ ≤ envelope coordinate x := by
  by_cases inside : |x| ≤ q
  · rw [envelope, if_pos inside]
    exact raw_head_bound coordinate zero N positiveN x nonzero
  · rw [envelope, if_neg inside]
    exact raw_tail_bound coordinate zero N positiveN x (lt_of_not_ge inside)

theorem envelope_memLp_two (coordinate : BurnolCompletedMellinCoordinate) : MemLp (envelope coordinate) 2 volume := by
  let regular := fun x : ℝ => GapEuler.gapMean q coordinate + burnolRieszReturnRaw coordinate |x|
  have regularContinuous : Continuous regular := continuous_const.add ((burnolRieszReturnRaw_continuous coordinate).comp continuous_abs)
  have core : MemLp ((symmetricInterval q).indicator regular) 2 volume :=
    (memLp_indicator_iff_restrict (measurableSet_symmetricInterval q)).mpr (Constructor.continuous_memLp regular regularContinuous)
  have native := (((Lp.memLp (base coordinate)).ae_eq (base_coeFn coordinate)).sub core).norm
  have tail : MemLp (fun x : ℝ => if |x| ≤ q then (0 : ℝ) else |x| ^ (-coordinate.value.re)) 2 volume := by
    apply (native.const_mul (2 : ℝ)).ae_eq
    filter_upwards with x
    simp only [Pi.sub_apply]
    by_cases inside : |x| ≤ q
    · rw [if_pos inside, baseRaw, if_pos inside, indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside)]
      change 2 * ‖regular x - regular x‖ = 0
      simp
    · have positive : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans (lt_of_not_ge inside)
      rw [if_neg inside, baseRaw, if_neg inside,
        indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h)), sub_zero,
        norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive]
      simp only [neg_re, star_def, conj_re]
      norm_num
      ring
  have head : MemLp ((symmetricInterval q).indicator (fun _ : ℝ => headBound coordinate)) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval q) _ (Or.inr (by simp [symmetricInterval]))
  apply (head.add (tail.const_mul ((1 / 2 : ℝ) * arithmeticConstant coordinate))).ae_eq
  filter_upwards with x
  simp only [Pi.add_apply]
  by_cases inside : |x| ≤ q
  · rw [envelope, if_pos inside, indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside), if_pos inside, mul_zero, add_zero]
  · rw [envelope, if_neg inside, indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h)), if_neg inside, zero_add]

/-- The whole original g+Er source converges strongly; the singular terms cancel before L² estimates are made. -/
theorem finite_tendsto (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    Tendsto (finite coordinate) atTop (𝓝 (-PositionCounting.value coordinate zero)) := by
  let limitRaw : ℝ → ℂ := -PositionCounting.eventRaw coordinate
  let majorant := fun x : ℝ => (envelope coordinate x + ‖PositionCounting.eventRaw coordinate x‖) ^ 2
  have sourceMem := PositionCounting.event_memLp_two coordinate zero
  have integrable : Integrable majorant := ((envelope_memLp_two coordinate).add sourceMem.norm).integrable_sq
  have measured : ∀ᶠ N : ℕ in atTop, AEStronglyMeasurable
      (fun x : ℝ => ‖finite coordinate N x - limitRaw x‖ ^ 2) volume :=
    Eventually.of_forall (fun N => ((Lp.aestronglyMeasurable (finite coordinate N)).sub sourceMem.neg.aestronglyMeasurable).norm.pow 2)
  have dominated : ∀ᶠ N : ℕ in atTop, ∀ᵐ x : ℝ ∂volume,
      ‖‖finite coordinate N x - limitRaw x‖ ^ 2‖ ≤ majorant x := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positiveN
    filter_upwards [finite_coeFn coordinate N, volume.ae_ne (0 : ℝ)] with x read nonzero
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), read]
    have difference : ‖raw coordinate N x - limitRaw x‖ ≤ envelope coordinate x + ‖PositionCounting.eventRaw coordinate x‖ := by
      have bound := (norm_sub_le (raw coordinate N x) (limitRaw x)).trans
        (add_le_add (raw_bound coordinate zero N positiveN x nonzero) le_rfl)
      simpa only [limitRaw, Pi.neg_apply, norm_neg] using bound
    exact pow_le_pow_left₀ (norm_nonneg _) difference 2
  have reads : ∀ᵐ x : ℝ ∂volume, ∀ N : ℕ, finite coordinate N x = raw coordinate N x :=
    ae_all_iff.mpr (finite_coeFn coordinate)
  have pointwise : ∀ᵐ x : ℝ ∂volume, Tendsto
      (fun N : ℕ => ‖finite coordinate N x - limitRaw x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [reads, volume.ae_ne (0 : ℝ)] with x read nonzero
    have arithmetic := (DirichletCoefficient.original_coefficient_limits coordinate zero).1.const_mul
      ((1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value))
    simp only [mul_zero] at arithmetic
    have actual : Tendsto (fun N : ℕ => finite coordinate N x - limitRaw x) atTop (𝓝 0) := by
      apply arithmetic.congr'
      filter_upwards [PositionCounting.raw_eventually coordinate x nonzero] with N complete
      rw [read N, raw_synthesis coordinate N x nonzero, complete]
      change _ = _ - -PositionCounting.eventRaw coordinate x
      ring
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using actual.norm.pow 2
  have integralLimit := tendsto_integral_filter_of_dominated_convergence majorant measured dominated integrable pointwise
  simp only [integral_zero] at integralLimit
  have rootLimit := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp integralLimit
  simp only [Real.sqrt_zero] at rootLimit
  have normLimit := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp rootLimit
  simp only [ENNReal.ofReal_zero] at normLimit
  change Tendsto (finite coordinate) atTop (𝓝 (sourceMem.neg.toLp limitRaw))
  apply Lp.tendsto_Lp_of_tendsto_eLpNorm limitRaw sourceMem.neg
  apply normLimit.congr'
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ((Lp.memLp (finite coordinate N)).sub sourceMem.neg)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Pi.sub_apply, Real.sqrt_eq_rpow, one_div, limitRaw]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.KCountingSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
