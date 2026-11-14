import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward OriginalPaPhysicalGreen
open OriginalKCoefficientBFiniteAction OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open OriginalKCoupledPhysicalRFieldSource OriginalKCompactAdjointRSource OriginalKQuarterTailPhysicalSource
open scoped InnerProductSpace

open private log_return_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa
open private physical_inner from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPhysical
open private quarter_star_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRQuarterUnitSettlementSource

local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Q" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "D" => DualSource.source
local notation "P" => burnolEvenAmbientProjection
local notation "K" => burnolCompletedMellinRieszVector
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R" => fun c : BurnolCompletedMellinCoordinate => burnolDirectRightResolventCLM (barC c)
local notation "tailCoeff" => fun c N => actualCompactTailCoefficient (barC c) (difference c N)
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem compensated_even (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    reflectL2 (compensated c N) = compensated c N := by
  classical
  let raw := burnolMeanZeroFourierRaw (logBFirst c 0)
  have measured := (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative.actual_return_contDiff
    (logBFirst c 0)).continuous.measurable
  have logs : (logCount c N : ℝ → ℂ) =ᵐ[volume] compactReverseFiniteRaw raw N :=
    actual_compact_reverse_finite_raw (S (logBFirst c 0) : Hq) raw
      (burnolMeanZeroFourier_ae_raw (logBFirst c 0)) (log_return_even c) measured N
  have logEven : reflectL2 (logCount c N) = logCount c N :=
    burnolReflectL2_eq_of_even_raw _ _ logs (fun x => by
      simp only [compactReverseFiniteRaw, compactReverseSeedRaw, mul_neg, abs_neg])
  have a := actual_compensated_raw c N
  have b := negMeasurePreserving.quasiMeasurePreserving.ae a
  have l := Lp.coeFn_compMeasurePreserving (logCount c N) negMeasurePreserving
  change ∀ᵐ x ∂volume, reflectL2 (logCount c N) x = logCount c N (-x) at l
  rw [logEven] at l
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (compensated c N) negMeasurePreserving, a, b, l]
    with x reflected here opposite log
  change reflectL2 (compensated c N) x = compensated c N (-x) at reflected
  change compensated c N (-x) = _ at opposite
  have member : -x ∈ symmetricInterval q ↔ x ∈ symmetricInterval q := by
    change (-q ≤ -x ∧ -x ≤ q) ↔ (-q ≤ x ∧ x ≤ q)
    constructor <;> rintro ⟨lower, upper⟩ <;> exact ⟨by linarith, by linarith⟩
  rw [reflected, opposite, here, ← log]
  simp only [PositionCounting.raw, PositionCounting.seedRaw, mul_neg, abs_neg,
    Set.indicator_apply, member, seedRaw, powerRaw]

private theorem difference_support (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    originalPhysicalCutoff q (difference c N) = difference c N := by
  unfold difference originalPhysicalCutoff
  rw [map_sub, map_sub]
  exact congrArg₂ (· - ·) (actual_compact c (N+1) (Nat.succ_pos N)) (actual_compact c N positive)

private theorem difference_mean (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    μ (difference c N) = 0 := by
  have read (v : BurnolL2) : μ v = burnolQuarterMeanCoefficient (Q v) := by
    change (((‖intervalConstant q‖ : ℂ)^2)⁻¹) * inner ℂ (intervalConstant q) (Q v) =
      inner ℂ (intervalConstant q) (Q v) / ((‖intervalConstant q‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
    exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
  rw [difference, map_sub, read, read, actual_compensated_mean c (N+1) (Nat.succ_pos N),
    actual_compensated_mean c N positive, sub_self]

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : actualStarSource (barC c) = c := by
  cases c
  simp only [actualStarSource, OriginalPrimitiveRankBalance.conjugateCoordinate, star_star]

private theorem quarter_unit_cancellation (d : BurnolCompletedMellinCoordinate) (a : ℂ) :
    (1/2 : ℂ) * (a * (((2*q : ℝ) : ℂ) * (q : ℂ)^(-d.value))/(d.value/2-1/2)) +
      (2 : ℂ) * a * star (burnolMellinGapMoment (actualStarSource d).value) = 0 := by
  have oneNe : 1-d.value ≠ 0 := by
    intro gone
    have real := congrArg Complex.re gone
    simp only [sub_re, one_re, zero_re] at real
    linarith [d.belowOne]
  have mean : star (burnolMellinGapMoment (actualStarSource d).value) =
      (q : ℂ)^(1-d.value)/(1-d.value) := by
    change star ((q : ℂ)^(1-star d.value)/(1-star d.value)) = _
    simp only [star_div₀, quarter_star_power, star_sub, star_one, star_star]
  have power : (q : ℂ)^(1-d.value) = (q : ℂ)*(q : ℂ)^(-d.value) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num : (q : ℂ) ≠ 0), Complex.cpow_one]
  rw [mean, power, show d.value/2-1/2 = -(1-d.value)/2 by ring]
  push_cast
  field_simp [oneNe]; ring

/-- The original compact R action takes the actual mean-zero difference into its original K direction. -/
theorem actual_resolvent_projection (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    P (R c (difference c N)) = -(2*tailCoeff c N) • K c := by
  have even : reflectL2 (difference c N) = difference c N := by
    rw [difference, map_sub, compensated_even, compensated_even]
  have actual := actual_compact_projected_R_source (barC c) (difference c N)
    (difference_support c N positive) even
  change P (R c (difference c N)) = _ at actual
  rw [actual, actualCompactProjectedRField, difference_mean c N positive, sub_zero,
    quarter_unit_cancellation, zero_smul, add_zero, conjugate_twice]

private theorem original_K_resolvent_price (c d : BurnolCompletedMellinCoordinate) (N : ℕ)
    (positive : 0 < N) :
    inner ℂ (K d : BurnolL2) (R c (difference c N)) =
      -(2*tailCoeff c N) * inner ℂ (K d) (K c) := by
  rw [physical_inner (K d), actual_resolvent_projection c N positive]
  exact inner_smul_right (K d) (K c) (-(2*tailCoeff c N))

/-- The independent original K tests the next whole count with its two generated contributions. -/
theorem actual_original_K_next (c d : BurnolCompletedMellinCoordinate) (N : ℕ) (covered : 2 ≤ N) :
    inner ℂ (K d : BurnolL2) (D (N+1) (R c (input c))) =
      inner ℂ (K d : BurnolL2) (D N (R c (input c))) -
        (2*tailCoeff c N) * inner ℂ (K d) (K c) +
      recover c (R c (difference c N)) * inner ℂ (K d : BurnolL2) (R c (elementarySource c)) := by
  rw [actual_resolvent_writeback c N covered, inner_add_right, inner_add_right,
    inner_smul_right (K d : BurnolL2) (R c (elementarySource c)), original_K_resolvent_price c d N (by omega)]
  ring

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
