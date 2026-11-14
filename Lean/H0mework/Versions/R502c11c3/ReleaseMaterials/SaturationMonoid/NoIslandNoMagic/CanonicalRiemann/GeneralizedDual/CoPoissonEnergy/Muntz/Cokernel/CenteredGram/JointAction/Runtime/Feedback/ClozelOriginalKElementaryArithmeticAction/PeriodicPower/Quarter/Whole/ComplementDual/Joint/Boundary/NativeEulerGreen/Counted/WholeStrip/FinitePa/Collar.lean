import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Mass

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward OriginalKCoefficientBFiniteAction
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace

open private compact_finite_event from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactFloor
open private log_return_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa
open private mean_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open private elementary_projection from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Physical

local notation "q" => (1/4 : ℝ)
local notation "window" => Ioc (q/2) q
local notation "μ" => volume.restrict window
local notation "Hq" => BurnolQuarterIntervalL2
local notation "D" => DualSource.source
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "P" => burnolEvenAmbientProjection
local notation "K" => burnolCompletedMellinRieszVector
local notation "Z" => fun c : BurnolCompletedMellinCoordinate => FiniteForcing.coefficient (star (BurnolCompletedMellinCoordinate.value c))
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance finiteWindow : IsFiniteMeasure μ where
  measure_univ_lt_top := by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top

def coefficientStep (c : BurnolCompletedMellinCoordinate) (N : ℕ) : ℂ :=
  Z c (N+1) - Z c N

def difference (c : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  compensated c (N+1) - compensated c N

/-- The next difference is the actual discrete cell and its own continuous normalization. -/
theorem actual_increment (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    difference c N = ContinuousChannels.channel 1 (N : ℝ) (input c) -
      (∫ a : ℝ in Ioc (N : ℝ) ((N+1 : ℕ) : ℝ), ContinuousChannels.channel 1 a (input c)) +
      coefficientStep c N • elementarySource c := by
  let channel := fun a : ℝ => ContinuousChannels.channel 1 a (input c)
  have nonnegative : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have ordered : (N : ℝ) ≤ ((N+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have first : IntervalIntegrable channel volume 0 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le nonnegative).mpr
      (ContinuousChannels.channel_integrable 1 N (input c))
  have last : IntervalIntegrable channel volume (N : ℝ) ((N+1 : ℕ) : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ordered).mpr
      ((ContinuousChannels.channel_integrable 1 ((N+1 : ℕ) : ℝ) (input c)).mono_set
        (Ioc_subset_Ioc nonnegative le_rfl))
  have split := intervalIntegral.integral_add_adjacent_intervals first last
  rw [intervalIntegral.integral_of_le nonnegative, intervalIntegral.integral_of_le ordered,
    intervalIntegral.integral_of_le (nonnegative.trans ordered)] at split
  dsimp only [channel] at split
  unfold difference compensated DualSource.source coefficientStep
  rw [Finset.sum_Ico_succ_top (show 1 ≤ N from positive), ← split]
  module

private theorem log_stable (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    ∀ᵐ x ∂volume, x ≠ 0 → q/|x| < (N : ℝ) →
      logCount c N x = compactReverseFloorRaw (burnolMeanZeroFourierRaw (logBFirst c 0)) x := by
  let raw := burnolMeanZeroFourierRaw (logBFirst c 0)
  have read := burnolMeanZeroFourier_ae_raw (logBFirst c 0)
  have measured := (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative.actual_return_contDiff
    (logBFirst c 0)).continuous.measurable
  filter_upwards [actual_compact_reverse_finite_raw (S (logBFirst c 0) : Hq)
    raw read (log_return_even c) measured N] with x finite nonzero covered
  exact finite.trans (compact_finite_event (S (logBFirst c 0)) raw read (log_return_even c) N x nonzero covered)

/-- In this fixed window both original compact channels have completed, so the adjacent source difference keeps its actual centered power. -/
theorem actual_difference_raw (c : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N) :
    (difference c N : ℝ → ℂ) =ᵐ[μ] fun x => -(coefficientStep c N)*seedRaw c.value x := by
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (compensated c (N+1)) (compensated c N)),
    ae_restrict_of_ae (actual_compensated_raw c (N+1)), ae_restrict_of_ae (actual_compensated_raw c N),
    ae_restrict_of_ae (log_stable c (N+1)), ae_restrict_of_ae (log_stable c N),
    ae_restrict_mem measurableSet_Ioc] with x subtract next current logNext logCurrent inside
  have positive : 0 < x := lt_trans (by norm_num : 0 < q/2) inside.1
  have member : x ∈ symmetricInterval q := abs_le.mp (by rw [abs_of_pos positive]; exact inside.2)
  have large : q/|x| < (N : ℝ) := by
    apply lt_of_lt_of_le _ (by exact_mod_cast covered : (2 : ℝ) ≤ (N : ℝ))
    rw [abs_of_pos positive, div_lt_iff₀ positive]
    linarith [inside.1]
  have nextLarge : q/|x| < ((N+1 : ℕ) : ℝ) := large.trans_le (by exact_mod_cast Nat.le_succ N)
  change (compensated c (N+1)-compensated c N : BurnolL2) x = _
  rw [subtract, Pi.sub_apply, next, current, logNext positive.ne' nextLarge,
    logCurrent positive.ne' large, PositionCounting.raw_event c (N+1) x positive.ne' nextLarge,
    PositionCounting.raw_event c N x positive.ne' large, indicator_of_mem member]
  unfold coefficientStep
  ring

theorem actual_coefficient_step (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    coefficientStep c N = (N : ℂ)^(-star c.value) -
      ∫ a : ℝ in (N : ℝ)..((N+1 : ℕ) : ℝ), (a : ℂ)^(-star c.value) := by
  have exponent : -1 < (-star c.value).re := by
    simp only [neg_re, star_def, conj_re]
    linarith [c.belowOne]
  unfold coefficientStep FiniteForcing.coefficient
  dsimp only
  rw [Finset.sum_Ico_succ_top (show 1 ≤ N from positive),
    integral_cpow (Or.inl exponent), show -star c.value+1=1-star c.value by ring]
  simp only [Complex.ofReal_natCast]
  ring

theorem actual_coefficient_step_ne_zero (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    coefficientStep c N ≠ 0 := by
  have start : (0 : ℝ) < N := by exact_mod_cast positive
  have increasing : (N : ℝ) < ((N+1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self N
  have exponent : -c.value.re < 0 := by linarith [c.rightHalf]
  have cont : ContinuousOn (fun a : ℝ => a^(-c.value.re)) (Icc (N : ℝ) ((N+1 : ℕ) : ℝ)) :=
    fun a ha => (Real.continuousAt_rpow_const a _ (Or.inl (start.trans_le ha.1).ne')).continuousWithinAt
  have smaller := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt increasing cont
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (N : ℝ)^(-c.value.re)) _)
    (fun a ha => Real.rpow_le_rpow_of_nonpos start ha.1.le exponent.le)
    ⟨_, ⟨increasing.le, le_rfl⟩, Real.rpow_lt_rpow_of_neg start increasing exponent⟩
  have width : ((N+1 : ℕ) : ℝ)-(N : ℝ)=1 := by push_cast; ring
  rw [intervalIntegral.integral_const, width, one_smul] at smaller
  have norms : (∫ a : ℝ in (N : ℝ)..((N+1 : ℕ) : ℝ), ‖(a : ℂ)^(-star c.value)‖) =
      ∫ a : ℝ in (N : ℝ)..((N+1 : ℕ) : ℝ), a^(-c.value.re) := by
    apply intervalIntegral.integral_congr_Ioo_of_le increasing.le
    intro a ha
    change ‖(a : ℂ)^(-star c.value)‖ = a^(-c.value.re)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (start.trans ha.1)]
    simp only [neg_re, star_def, conj_re]
  have base : ‖(N : ℂ)^(-star c.value)‖ = (N : ℝ)^(-c.value.re) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos start]
    simp only [neg_re, star_def, conj_re]
  have strict : ‖∫ a : ℝ in (N : ℝ)..((N+1 : ℕ) : ℝ), (a : ℂ)^(-star c.value)‖ <
      ‖(N : ℂ)^(-star c.value)‖ := by
    rw [base]
    exact ((intervalIntegral.norm_integral_le_integral_norm increasing.le).trans_eq norms).trans_lt smaller
  rw [actual_coefficient_step c N positive]
  exact sub_ne_zero.mpr (fun same => (ne_of_lt strict) (congrArg norm same.symm))

private theorem seed_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (seedRaw c.value) (Icc (q/2) q) := by
  have power : ContinuousOn (powerRaw c.value) (Icc (q/2) q) := by
    intro x hx
    have positive : 0 < x := (by norm_num : 0 < q/2).trans_le hx.1
    exact ((Complex.continuousAt_ofReal_cpow_const |x| (-star c.value)
      (Or.inr (abs_pos.mpr positive.ne').ne')).comp continuous_abs.continuousAt).continuousWithinAt
  unfold seedRaw
  exact continuousOn_const.mul (power.sub continuousOn_const)

private theorem seed_endpoint_ne_zero (c : BurnolCompletedMellinCoordinate) :
    seedRaw c.value q ≠ 0 := by
  let s := star c.value
  let m := GapEuler.gapMean q c
  have exponent : s ≠ 0 := by
    intro zero
    have real := congrArg Complex.re zero
    simp only [s, star_def, conj_re, zero_re] at real
    linarith [c.rightHalf]
  have gap := GapEuler.gapMean_primitive q (by norm_num) c
  change (1-s)*m=(1/2 : ℂ)*(q : ℂ)^(-s) at gap
  have power : (q : ℂ)^(-s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have live : m ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at gap
    exact (mul_ne_zero (by norm_num : (1/2 : ℂ) ≠ 0) power) gap.symm
  have edge : seedRaw c.value q = -s*m := by
    unfold seedRaw powerRaw
    rw [abs_of_nonneg (by norm_num : 0 ≤ q)]
    change (1/2 : ℂ)*((q : ℂ)^(-s)-rawMean (powerRaw c.value)) = _
    linear_combination -gap - mean_power c
  rw [edge]
  exact mul_ne_zero (neg_ne_zero.mpr exponent) live

private theorem seed_memLp (c : BurnolCompletedMellinCoordinate) : MemLp (seedRaw c.value) 2 μ := by
  obtain ⟨bound, controls⟩ := isCompact_Icc.exists_bound_of_continuousOn (seed_continuous c)
  have measurable : Measurable (seedRaw c.value) := by
    unfold seedRaw
    exact measurable_const.mul ((actual_power_measurable c.value).sub measurable_const)
  apply MemLp.of_bound measurable.aestronglyMeasurable bound
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact controls x ⟨hx.1.le, hx.2⟩

private def collarPower (c : BurnolCompletedMellinCoordinate) : Lp ℂ 2 μ :=
  (seed_memLp c).toLp (seedRaw c.value)

private theorem collarPower_ne_zero (c : BurnolCompletedMellinCoordinate) : collarPower c ≠ 0 := by
  intro zero
  have read : (collarPower c : ℝ → ℂ) =ᵐ[μ] seedRaw c.value := (seed_memLp c).coeFn_toLp
  rw [zero] at read
  have gone := read.symm.trans (Lp.coeFn_zero ℂ 2 μ)
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at gone
  have point := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : q/2 ≠ q) gone
    (seed_continuous c) continuousOn_const
  exact seed_endpoint_ne_zero c (point ⟨by norm_num, le_rfl⟩)

local notation "restrict" => LpToLpRestrictCLM ℝ ℂ ℂ volume 2 window

/-- This covector reads the original centered power on a positive window where it is square-integrable. -/
def recoverCoefficient (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  (((‖collarPower c‖ : ℂ)^2)⁻¹) • ((innerSL ℂ (collarPower c)).comp restrict)

theorem actual_recovered_coefficient (c : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N) :
    recoverCoefficient c (difference c N) = -coefficientStep c N := by
  have face : restrict (difference c N) = (-coefficientStep c N) • collarPower c := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ window (difference c N), actual_difference_raw c N covered,
      Lp.coeFn_smul (-coefficientStep c N) (collarPower c), (seed_memLp c).coeFn_toLp]
      with x localRead raw scalar seed
    rw [localRead, raw, scalar, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun value : ℂ => -coefficientStep c N*value) seed.symm
  have normLive : ((‖collarPower c‖ : ℂ)^2) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (collarPower_ne_zero c)))
  change (((‖collarPower c‖ : ℂ)^2)⁻¹) * inner ℂ (collarPower c) (restrict (difference c N)) = _
  rw [face, inner_smul_right (collarPower c) (collarPower c), inner_self_eq_norm_sq_to_K]
  change (((‖collarPower c‖ : ℂ)^2)⁻¹) *
    (-coefficientStep c N * (‖collarPower c‖ : ℂ)^2) = -coefficientStep c N
  calc
    _ = (((‖collarPower c‖ : ℂ)^2)⁻¹ * (‖collarPower c‖ : ℂ)^2) * (-coefficientStep c N) := by ring
    _ = -coefficientStep c N := by rw [inv_mul_cancel₀ normLive, one_mul]

/-- The actual compact difference lies in the projection fibre; its own window restores the original K action. -/
theorem actual_inverse_fibre (c : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N) :
    P (difference c N) = 0 ∧ difference c N ≠ 0 ∧
      P (D (N+1) (input c)-D N (input c)) = recoverCoefficient c (difference c N) • K c := by
  have positive : 0 < N := by omega
  have projected (k : ℕ) (live : 0 < k) : P (compensated c k) = unitMean c • P ConstantDual.seed := by
    rw [compensated, map_add, map_smul, actual_finite_Pa c k live, elementary_projection, sub_add_cancel]
  have effect := actual_recovered_coefficient c N covered
  refine ⟨?_, ?_, ?_⟩
  · rw [difference, map_sub, projected (N+1) (Nat.succ_pos N), projected N positive, sub_self]
  · intro gone
    rw [gone, map_zero] at effect
    exact (actual_coefficient_step_ne_zero c N positive) (neg_eq_zero.mp effect.symm)
  · rw [actual_physical_difference c (N+1) N (Nat.succ_pos N) positive, effect, coefficientStep, neg_sub]

/-- Recover the whole next counted field from the prior field and its complete compact difference. -/
theorem actual_full_writeback (c : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N) :
    D (N+1) (input c) = D N (input c) + difference c N +
      recoverCoefficient c (difference c N) • elementarySource c := by
  rw [actual_recovered_coefficient c N covered]
  unfold difference compensated coefficientStep
  module

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
