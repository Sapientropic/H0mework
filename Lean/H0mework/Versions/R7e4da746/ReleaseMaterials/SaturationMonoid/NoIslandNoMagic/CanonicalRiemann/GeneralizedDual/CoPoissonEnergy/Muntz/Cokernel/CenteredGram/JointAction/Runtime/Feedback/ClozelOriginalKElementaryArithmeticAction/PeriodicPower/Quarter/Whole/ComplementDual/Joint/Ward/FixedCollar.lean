import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.UnitDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.ComplementFirstCell
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.BandSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalUnitMellinSource.Band
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.ComplementFirstCell
open scoped Topology InnerProductSpace
open private physical_homogeneous_price homogeneous_dilation_domain from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.UnitDual
open private character_star from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.UnitShell
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "F" => fourierL2
local notation "D" => burnolMultiplicativeDilation
local notation "h₀" => Real.log stageZeroSonineQ
local notation "r₀" => q / stageZeroSonineQ

private theorem fixed_collar_geometry :
    0 < r₀ ∧ q / 2 < r₀ ∧ r₀ < q ∧ 0 ≤ h₀ ∧
      Real.exp h₀ * r₀ = q ∧ Real.exp h₀ < 2 := by
  have square : stageZeroSonineQ ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have lower : 1 < stageZeroSonineQ := by nlinarith [stageZeroSonineQ_pos]
  have upper : stageZeroSonineQ < 2 := by nlinarith [stageZeroSonineQ_pos]
  refine ⟨div_pos (by norm_num) stageZeroSonineQ_pos, ?_, ?_, Real.log_nonneg lower.le, ?_, ?_⟩
  · rw [lt_div_iff₀ stageZeroSonineQ_pos]
    linarith
  · rw [div_lt_iff₀ stageZeroSonineQ_pos]
    linarith
  · rw [Real.exp_log stageZeroSonineQ_pos]
    field_simp
  · rwa [Real.exp_log stageZeroSonineQ_pos]

private theorem scaled_collar_power (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (positive : 0 < x) :
    (Real.exp (h₀ / 2) : ℂ) * ((Real.exp h₀ * x : ℝ) : ℂ) ^ (coordinate.value - 1) =
      fullMellinTranslationCharacter coordinate.value (-h₀) * (x : ℂ) ^ (coordinate.value - 1) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos h₀).le positive.le,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h₀)),
    ← Complex.ofReal_log (Real.exp_pos h₀).le, Real.log_exp]
  have scalar : (Real.exp (h₀ / 2) : ℂ) * Complex.exp ((h₀ : ℂ) * (coordinate.value - 1)) =
      fullMellinTranslationCharacter coordinate.value (-h₀) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    unfold fullMellinTranslationCharacter
    congr 1
    push_cast
    ring
  linear_combination (x : ℂ) ^ (coordinate.value - 1) * scalar

private theorem scaled_collar_log (x : ℝ) (positive : 0 < x) :
    bandLog (Real.exp h₀ * x) = collarLog r₀ x := by
  unfold bandLog collarLog
  rw [Real.log_mul (Real.exp_ne_zero _) positive.ne', Real.log_exp,
    Real.log_div (by norm_num : q ≠ 0) stageZeroSonineQ_pos.ne']
  push_cast
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

theorem actual_fixed_moved_unit_profile (j : Nat) (before : j < m) :
    ∀ᵐ x : ℝ ∂volume, 0 < x → x ≤ q →
      D h₀ (F (U j)) x = (Real.exp (h₀ / 2) : ℂ) * bandMean c j +
        if r₀ < x then fullMellinTranslationCharacter (c).value (-h₀) * bandCoefficient j *
          (x : ℂ) ^ ((c).value - 1) * collarLog r₀ x ^ j else 0 := by
  have quarter := OriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource.actual_fourier_quarter_power
    observation nontrivial half j before
  change burnolQuarterRestriction (F (U j)) = bandMean c j • intervalConstant q at quarter
  have gap : ∀ᵐ x : ℝ ∂μq, F (U j) x = bandMean c j := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (F (U j)),
      Lp.coeFn_smul (bandMean c j) (intervalConstant q), intervalConstant_coeFn q] with x restricted scalar constant
    change burnolQuarterRestriction (F (U j)) x = F (U j) x at restricted
    rw [quarter, scalar, Pi.smul_apply, smul_eq_mul, constant, mul_one] at restricted
    exact restricted.symm
  have gapFull := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp gap
  have scaled : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h₀ * x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := Real.exp h₀) (Real.exp_ne_zero h₀)
  filter_upwards [burnolMultiplicativeDilation_coeFn h₀ (F (U j)), scaled.ae gapFull,
    scaled.ae (actual_fourier_first_cell_power observation nontrivial half j before)] with x dilation gapRead band
  intro positive upper
  rw [dilation]
  change (Real.exp (h₀ / 2) : ℂ) * F (U j) (Real.exp h₀ * x) = _
  by_cases inside : x ≤ r₀
  · rw [if_neg (not_lt.mpr inside), gapRead ⟨by linarith [mul_pos (Real.exp_pos h₀) positive],
      by simpa only [fixed_collar_geometry.2.2.2.2.1] using
        mul_le_mul_of_nonneg_left inside (Real.exp_pos h₀).le⟩, add_zero]
  · have after : q < Real.exp h₀ * x := by
      rw [← fixed_collar_geometry.2.2.2.2.1]
      exact mul_lt_mul_of_pos_left (lt_of_not_ge inside) (Real.exp_pos h₀)
    have beforeTwo : Real.exp h₀ * x < 2 * q :=
      (mul_le_mul_of_nonneg_left upper (Real.exp_pos h₀).le).trans_lt
        (mul_lt_mul_of_pos_right fixed_collar_geometry.2.2.2.2.2 (by norm_num))
    rw [if_pos (lt_of_not_ge inside), band after beforeTwo, scaled_collar_log x positive]
    have power := scaled_collar_power c x positive
    linear_combination bandCoefficient j * collarLog r₀ x ^ j * power

omit nontrivial in
private theorem dual_product_domain (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (domain : Integrable (fun x : ℝ => star (value x) * halfPower coordinate x)) :
    Integrable (fun x : ℝ => star (value x) * dualRaw coordinate.value coordinate.belowOne x) μq := by
  have gapDomain : Integrable (fun x : ℝ => star (value x) * OriginalRieszSourceGreen.gapState coordinate x) := by
    simpa only [RCLike.inner_apply', starRingEnd_apply] using
      L2.integrable_inner (𝕜 := ℂ) value (OriginalRieszSourceGreen.gapState coordinate)
  have source : (fun x : ℝ => star (value x) * seedCut coordinate x) =ᵐ[volume]
      fun x : ℝ => star (value x) * halfPower coordinate x -
        star (value x) * OriginalRieszSourceGreen.gapState coordinate x := by
    filter_upwards [OriginalRieszSourceGreen.gapState_read coordinate] with x raw
    rw [raw]
    linear_combination star (value x) * actual_gap_seed_raw coordinate x
  have seedDomain := (domain.sub gapDomain).congr source.symm
  have indicator : (fun x : ℝ => star (value x) * seedCut coordinate x) =
      (symmetricInterval q).indicator (fun x : ℝ => star (value x) * seedRaw coordinate.value x) := by
    funext x
    by_cases inside : x ∈ symmetricInterval q
    · rw [seedCut, indicator_of_mem inside, indicator_of_mem inside]
    · rw [seedCut, indicator_of_notMem inside, indicator_of_notMem inside, mul_zero]
  rw [indicator] at seedDomain
  have seedQuarter : Integrable (fun x : ℝ => star (value x) * seedRaw coordinate.value x) μq :=
    (integrable_indicator_iff (measurableSet_symmetricInterval q)).mp seedDomain
  have corrSource : (fun x : ℝ => star (value x) * correctionRaw coordinate.value coordinate.belowOne x) =ᵐ[μq]
      fun x : ℝ => star (burnolQuarterRestriction value x) * (correction coordinate.value coordinate.belowOne : Hq) x := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
      actual_correction_raw coordinate.value coordinate.belowOne] with x restricted raw
    change burnolQuarterRestriction value x = value x at restricted
    rw [restricted, raw]
  have corrDomain : Integrable (fun x : ℝ => star (value x) * correctionRaw coordinate.value coordinate.belowOne x) μq :=
    (show Integrable (fun x : ℝ => star (burnolQuarterRestriction value x) *
      (correction coordinate.value coordinate.belowOne : Hq) x) μq from by
        simpa only [RCLike.inner_apply', starRingEnd_apply] using
          L2.integrable_inner (𝕜 := ℂ) (burnolQuarterRestriction value) (correction coordinate.value coordinate.belowOne : Hq)).congr corrSource.symm
  convert! seedQuarter.add corrDomain using 1
  funext x
  simp only [dualRaw, mul_add, Pi.add_apply]

omit nontrivial in
private theorem even_quarter_integral (f : ℝ → ℂ) (domain : Integrable f μq)
    (even : (fun x : ℝ => f (-x)) =ᵐ[μq] f) :
    (∫ x : ℝ, f x ∂μq) = 2 * ∫ x : ℝ in (0 : ℝ)..q, f x := by
  have domainOn : IntegrableOn f (symmetricInterval q) volume := domain
  have negative : IntervalIntegrable f volume (-q) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-q : ℝ) ≤ 0)).mpr
      (domainOn.mono_set (fun _ inside => ⟨inside.1, le_trans inside.2 (by norm_num)⟩))
  have positive : IntervalIntegrable f volume 0 q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ q)).mpr
      (domainOn.mono_set (fun _ inside => ⟨le_trans (by norm_num) inside.1, inside.2⟩))
  have evenFull := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp even
  have halves : (∫ x : ℝ in (-q)..(0 : ℝ), f x) = ∫ x : ℝ in (0 : ℝ)..q, f x := by
    have moved := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := q)
    rw [neg_zero] at moved
    rw [← moved]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [evenFull] with x source inside
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ q)] at inside
    exact source ⟨by linarith [inside.1], inside.2⟩
  change (∫ x : ℝ in Icc (-q) q, f x) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-q : ℝ) ≤ q),
    ← intervalIntegral.integral_add_adjacent_intervals negative positive, halves]
  ring

omit nontrivial in
private theorem star_positive_power (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x) :
    star ((x : ℂ) ^ (coordinate.value - 1)) = (x : ℂ) ^ (star coordinate.value - 1) := by
  have argument : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_ne_zero.symm
  have source := Complex.cpow_conj (x : ℂ) (coordinate.value - 1) argument
  rw [Complex.conj_ofReal] at source
  simpa only [← Complex.star_def, star_sub, star_one] using source.symm

theorem actual_fixed_unit_quarter_collar (j : Nat) (before : j < m) :
    (∫ x : ℝ, star (D h₀ (F (U j)) x) * dualRaw (c).value (c).belowOne x ∂μq) =
      2 * fullMellinTranslationCharacter (star (c).value) (-h₀) * bandCoefficient j *
        ∫ x : ℝ in r₀..q, (x : ℂ) ^ (star (c).value - 1) *
          (Real.log (x / r₀) : ℂ) ^ j * fullFloorRaw c x := by
  let Y := D h₀ (F (U j))
  let f : ℝ → ℂ := fun x => star (Y x) * dualRaw (c).value (c).belowOne x
  let gamma : ℂ := (Real.exp (h₀ / 2) : ℂ) * bandMean c j
  let kappa : ℂ := fullMellinTranslationCharacter (star (c).value) (-h₀) * bandCoefficient j
  let integrand : ℝ → ℂ := fun x => (x : ℂ) ^ (star (c).value - 1) *
    (Real.log (x / r₀) : ℂ) ^ j * fullFloorRaw c x
  let unit : BurnolPaAmbientCarrier :=
    ⟨U j, OriginalKFiniteOrderRelease.UnitPowerSource.unitPower_physical observation nontrivial half j before⟩
  let physical := evenFaceFourierEquiv q unit
  have domain : Integrable f μq := dual_product_domain c Y
    (homogeneous_dilation_domain c h₀ (physical : BurnolL2) (physical_homogeneous_price c physical).1)
  have evenY : reflectL2 Y = Y := by
    dsimp only [Y]
    rw [reflectL2_burnolMultiplicativeDilation, ← fourierL2_reflectL2_commute,
      mem_evenL2ClosedFace_iff.mp unit.property.2]
  have reflected := Lp.coeFn_compMeasurePreserving Y negMeasurePreserving
  change (reflectL2 Y : ℝ → ℂ) =ᵐ[volume] fun x => Y (-x) at reflected
  rw [evenY] at reflected
  have evenF : (fun x : ℝ => f (-x)) =ᵐ[μq] f := by
    filter_upwards [ae_restrict_of_ae reflected, ae_restrict_mem (measurableSet_symmetricInterval q)] with x reflection inside
    dsimp only [f]
    rw [← reflection, actual_dual_even (c).value (c).belowOne x inside]
  have domainOn : IntegrableOn f (symmetricInterval q) volume := domain
  have dualOn : IntegrableOn (dualRaw (c).value (c).belowOne) (symmetricInterval q) volume :=
    actual_dual_integrable (c).value (c).belowOne
  have first : IntervalIntegrable f volume 0 q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ q)).mpr
      (domainOn.mono_set (fun _ inside => ⟨by linarith [inside.1], inside.2⟩))
  have dual : IntervalIntegrable (dualRaw (c).value (c).belowOne) volume 0 q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ q)).mpr
      (dualOn.mono_set (fun _ inside => ⟨by linarith [inside.1], inside.2⟩))
  have difference : (∫ x : ℝ in (0 : ℝ)..q, f x) -
      star gamma * (∫ x : ℝ in (0 : ℝ)..q, dualRaw (c).value (c).belowOne x) =
        kappa * ∫ x : ℝ in r₀..q, integrand x := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub first (dual.const_mul _)]
    have native : (∫ x : ℝ in (0 : ℝ)..q, f x - star gamma * dualRaw (c).value (c).belowOne x) =
        ∫ x : ℝ in (0 : ℝ)..q, kappa * (Ioc r₀ q).indicator integrand x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [actual_fixed_moved_unit_profile observation nontrivial half j before] with x profile inside
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ q)] at inside
      have raw := profile inside.1 inside.2
      change Y x = gamma + (if r₀ < x then _ else 0) at raw
      have beta : star (bandCoefficient j) = bandCoefficient j := by simp [bandCoefficient]
      have logarithm : star (collarLog r₀ x) = collarLog r₀ x := Complex.conj_ofReal _
      by_cases beyond : r₀ < x
      · have onBand : x ∈ Ioc r₀ q := ⟨beyond, inside.2⟩
        have C := actual_complement_first_cell c x (fixed_collar_geometry.2.1.trans beyond) inside.2
        have logs : (Real.log (x / r₀) : ℂ) = collarLog r₀ x := by
          rw [Real.log_div inside.1.ne' fixed_collar_geometry.1.ne']
          rfl
        rw [if_pos beyond] at raw
        dsimp only [f, integrand, kappa]
        rw [indicator_of_mem onBand, raw]
        simp only [star_add, star_mul, star_pow, logarithm, star_positive_power c x inside.1, beta, character_star]
        rw [C, logs]
        ring
      · rw [if_neg beyond] at raw
        have notBand : x ∉ Ioc r₀ q := fun h => beyond h.1
        dsimp only [f]
        rw [indicator_of_notMem notBand, raw, add_zero]
        ring
    rw [native, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q), integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc]
    have intersection : Ioc r₀ q ∩ Ioc (0 : ℝ) q = Ioc r₀ q :=
      inter_eq_left.mpr (Ioc_subset_Ioc fixed_collar_geometry.1.le le_rfl)
    rw [intersection, ← intervalIntegral.integral_of_le fixed_collar_geometry.2.2.1.le]
  rw [actual_positive_dual_mean (c).value (c).belowOne, mul_zero, sub_zero] at difference
  change (∫ x : ℝ, f x ∂μq) = _
  rw [even_quarter_integral f domain evenF, difference]
  dsimp only [kappa, integrand]
  ring

theorem actual_native_unit_plus_fixed_collar_top :
    inner ℂ (U (m - 1)) (D h₀ (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native.nativeReturn c)) =
      fullMellinTranslationCharacter (star (c).value) (-h₀) *
        ((2 : ℂ) ^ m / ((m - 1).factorial : ℂ) *
          (∫ x : ℝ in r₀..q, (x : ℂ) ^ (star (c).value - 1) *
            (Real.log (x / r₀) : ℂ) ^ (m - 1) * fullFloorRaw c x) - star e) := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have coefficient : 2 * bandCoefficient (m - 1) = (2 : ℂ) ^ m / ((m - 1).factorial : ℂ) := by
    have power : (2 : ℂ) ^ m = (2 : ℂ) ^ (m - 1) * 2 := by
      calc
        _ = (2 : ℂ) ^ ((m - 1) + 1) := congrArg (fun n : Nat => (2 : ℂ) ^ n) (by omega)
        _ = _ := pow_succ _ _
    rw [bandCoefficient, power]
    ring
  rw [actual_native_unit_positive_dual_top observation nontrivial half h₀ fixed_collar_geometry.2.2.2.1,
    actual_fixed_unit_quarter_collar observation nontrivial half (m - 1) (by omega)]
  linear_combination fullMellinTranslationCharacter (star (c).value) (-h₀) *
    (∫ x : ℝ in r₀..q, (x : ℂ) ^ (star (c).value - 1) *
      (Real.log (x / r₀) : ℂ) ^ (m - 1) * fullFloorRaw c x) * coefficient

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
