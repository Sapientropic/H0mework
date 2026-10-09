import H0mework.Versions.V2.Arithmetic.MobiusSource.SourceRead
import H0mework.Arithmetic.MobiusSource.MobiusReconstruction

/-!
# Actual co-Poisson replay on every finite observation window

The extracted source and its unchanged mean generate the forward co-sum.
Every radius is handled by the same finite cutoff construction, with exact
replay for actual compact source values.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators InnerProductSpace ENNReal
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "Window" => BurnolRadiusIntervalL2 4

/-- Replay every finite observation window from the actual extracted source
and the same gap mean.  Neither is supplied by a caller. -/
def burnolCoPoissonWindowReplay (radius : ℝ) :
    Ambient →L[ℂ] BurnolRadiusIntervalL2 radius :=
  (∑ m ∈ burnolCenteredMobiusCutoffFinset radius,
    (((m : ℕ) : ℂ)⁻¹) •
      ((burnolWindowScalePullback radius m).comp
        ((burnolRadiusZeroExtension 4).comp burnolMobiusWindowSourceRead))) +
    ((ContinuousLinearMap.toSpanSingleton ℂ (intervalConstant radius)).comp
      (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius))

private theorem windowFiniteSum_ae {ι : Type*} (radius : ℝ)
    (indices : Finset ι) (values : ι → BurnolRadiusIntervalL2 radius)
    (raw : ι → ℝ → ℂ)
    (read : ∀ i, (values i : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval radius)] raw i) :
    ((∑ i ∈ indices, values i : BurnolRadiusIntervalL2 radius) : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval radius)] fun x => ∑ i ∈ indices, raw i x := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using!
        (Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval radius)))
  | @insert i indices notMem previous =>
      rw [Finset.sum_insert notMem]
      simp_rw [Finset.sum_insert notMem]
      filter_upwards [Lp.coeFn_add (values i) (∑ j ∈ indices, values j),
        read i, previous] with x hadd hi hprevious
      simpa only [Pi.add_apply, hi, hprevious] using hadd

theorem burnolCoPoissonWindowReplay_compact_coeFn
    (radius : ℝ) (source : burnolCompactAnnulusSource) :
    (burnolCoPoissonWindowReplay radius (burnolCompactAdditivePhysicalState source) :
      ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval radius)] fun x =>
      (∑ m ∈ burnolCenteredMobiusCutoffFinset radius,
        (((m : ℕ) : ℂ)⁻¹) * burnolCompactAdditiveSource source (x / (m : ℕ))) +
          burnolCompactAdditiveCoSum source 0 := by
  let value := burnolCompactAdditivePhysicalState source
  let extracted := burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value)
  have termRead (m : ℕ+) :
      ((((m : ℕ) : ℂ)⁻¹ • burnolWindowScalePullback radius m extracted :
        BurnolRadiusIntervalL2 radius) : ℝ → ℂ) =ᵐ[
          volume.restrict (symmetricInterval radius)] fun x =>
            (((m : ℕ) : ℂ)⁻¹) *
              burnolCompactAdditiveSource source (x / (m : ℕ)) := by
    have nonzero : (((m : ℕ) : ℝ)⁻¹) ≠ 0 :=
      inv_ne_zero (by exact_mod_cast m.ne_zero)
    have qmp := Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := (((m : ℕ) : ℝ)⁻¹)) nonzero
    have pulled : (fun x => extracted (x / (m : ℕ))) =ᵐ[volume]
        fun x => burnolCompactAdditiveSource source (x / (m : ℕ)) := by
      simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm, extracted, value] using!
        qmp.ae (burnolMobiusSourceExtension_compact_coeFn source)
    filter_upwards [Lp.coeFn_smul (((m : ℕ) : ℂ)⁻¹)
        (burnolWindowScalePullback radius m extracted),
      burnolWindowScalePullback_coeFn radius m extracted,
      ae_restrict_of_ae (s := symmetricInterval radius) pulled]
      with x hsmul hscale hsource
    simpa only [Pi.smul_apply, smul_eq_mul, hscale, hsource] using hsmul
  have sumRead := windowFiniteSum_ae radius (burnolCenteredMobiusCutoffFinset radius)
    (fun m => (((m : ℕ) : ℂ)⁻¹) • burnolWindowScalePullback radius m extracted)
    (fun m x => (((m : ℕ) : ℂ)⁻¹) *
      burnolCompactAdditiveSource source (x / (m : ℕ))) termRead
  let sumValue : BurnolRadiusIntervalL2 radius :=
    ∑ m ∈ burnolCenteredMobiusCutoffFinset radius,
      (((m : ℕ) : ℂ)⁻¹) • burnolWindowScalePullback radius m extracted
  have replayEq : burnolCoPoissonWindowReplay radius value =
      sumValue + burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value •
        intervalConstant radius := by
    simp only [burnolCoPoissonWindowReplay, sum_apply, smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      sumValue, extracted]
  rw [show burnolCompactAdditivePhysicalState source = value by rfl, replayEq]
  filter_upwards [Lp.coeFn_add sumValue
    (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value • intervalConstant radius),
    Lp.coeFn_smul (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value)
      (intervalConstant radius),
    sumRead, intervalConstant_coeFn radius] with x hadd hsmul hsum hconstant
  rw [hadd]
  change sumValue x +
    (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value •
      intervalConstant radius : BurnolRadiusIntervalL2 radius) x = _
  rw [hsmul]
  change sumValue x + burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value *
    intervalConstant radius x = _
  rw [hsum, hconstant, mul_one]
  congr 1
  exact burnolCompactGapCoefficient source


theorem burnolCompactCoSum_windowFinite (radius : ℝ)
    (source : burnolCompactAnnulusSource) (x : ℝ) (inside : |x| ≤ radius) :
    (∑ m ∈ burnolCenteredMobiusCutoffFinset radius,
      (((m : ℕ) : ℂ)⁻¹) * burnolCompactAdditiveSource source (x / (m : ℕ))) +
        burnolCompactAdditiveCoSum source 0 = burnolCompactAdditiveCoSum source x := by
  have quarterGap : ∀ {t : ℝ}, |t| ≤ (1 / 4 : ℝ) →
      burnolCompactAdditiveCoSum source t = burnolCompactAdditiveCoSum source 0 := by
    intro t small
    rw [burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source small,
      burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source
        (t := 0) (by norm_num)]
  have reconstruction := burnolCenteredMobiusInverse_exactReconstruction
    (burnolCompactAdditiveCoSum source) quarterGap x
  simp_rw [burnolCompactCenteredMobiusInverse_roundtrip] at reconstruction
  have finite : (∑' m : ℕ+, (((m : ℕ) : ℂ)⁻¹) *
      burnolCompactAdditiveSource source (x / (m : ℕ))) =
      ∑ m ∈ burnolCenteredMobiusCutoffFinset radius, (((m : ℕ) : ℂ)⁻¹) *
        burnolCompactAdditiveSource source (x / (m : ℕ)) := by
    apply tsum_eq_sum
    intro m notMem
    have large : burnolCenteredMobiusCutoff radius ≤ (m : ℕ) :=
      Nat.le_of_not_gt (by simpa using notMem)
    have scaleBound : 4 * |radius| ≤ ((m : ℕ) : ℝ) :=
      (Nat.le_ceil (4 * |radius|)).trans (by exact_mod_cast large)
    have positive : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.property
    have small : |x / ((m : ℕ) : ℝ)| ≤ (1 / 4 : ℝ) := by
      rw [abs_div, abs_of_pos positive]
      apply (div_le_iff₀ positive).mpr
      nlinarith [le_abs_self radius]
    rw [burnolCompactAdditiveSource_zero_of_abs_le_quarter source small, mul_zero]
  rw [finite] at reconstruction
  rw [reconstruction, sub_add_cancel]

theorem burnolCoPoissonWindowReplay_compact_eq (radius : ℝ)
    (source : burnolCompactAnnulusSource) :
    burnolCoPoissonWindowReplay radius (burnolCompactAdditivePhysicalState source) =
      burnolRadiusRestriction radius (burnolCompactAdditiveL2 source) := by
  apply Lp.ext
  filter_upwards [burnolCoPoissonWindowReplay_compact_coeFn radius source,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius)
      (burnolCompactAdditiveL2 source),
    ae_restrict_of_ae (s := symmetricInterval radius)
      (burnolCompactAdditiveL2_coeFn source),
    ae_restrict_mem (measurableSet_symmetricInterval radius)]
    with x hgenerated hrestricted hraw hx
  rw [hgenerated]
  rw [show burnolRadiusRestriction radius (burnolCompactAdditiveL2 source) x =
      burnolCompactAdditiveL2 source x from hrestricted, hraw]
  exact burnolCompactCoSum_windowFinite radius source x
    (abs_le.mpr (by simpa [symmetricInterval] using hx))

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
