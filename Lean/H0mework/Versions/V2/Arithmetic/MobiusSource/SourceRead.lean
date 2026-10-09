import H0mework.Versions.V2.Arithmetic.MobiusSource.WindowOperator
import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusClosedRange

/-!
# The finite Hilbert read recovers the actual compact co-Poisson source

The existing centred Möbius roundtrip is consumed by the concrete Hilbert
map. Its gap mean is recovered from the same value, and the extracted source
has the inner gap on every admitted ambient input.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators InnerProductSpace ENNReal
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "Window" => BurnolRadiusIntervalL2 4

theorem burnolCompactGapCoefficient (source : burnolCompactAnnulusSource) :
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
        (burnolCompactAdditivePhysicalState source) =
      burnolCompactAdditiveCoSum source 0 := by
  apply burnolConstantGapCoefficient_eq _ (by norm_num [burnolUnscaledCommonGapRadius])
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (burnolCompactAdditiveCoSum source 0)
      (intervalConstant burnolUnscaledCommonGapRadius),
    intervalConstant_coeFn burnolUnscaledCommonGapRadius,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval burnolUnscaledCommonGapRadius)
      (burnolCompactAdditiveL2 source),
    ae_restrict_of_ae (burnolCompactAdditiveL2_coeFn source),
    ae_restrict_mem (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)]
    with x hsmul hconstant hrestrict hsource hx
  rw [hsmul]
  change burnolCompactAdditiveCoSum source 0 *
    intervalConstant burnolUnscaledCommonGapRadius x = _
  rw [hconstant, mul_one]
  change _ = restrictToInterval burnolUnscaledCommonGapRadius
    (burnolCompactAdditiveL2 source) x
  rw [show restrictToInterval burnolUnscaledCommonGapRadius
    (burnolCompactAdditiveL2 source) x = burnolCompactAdditiveL2 source x
      from hrestrict, hsource]
  have inside : |x| ≤ (1 / 4 : ℝ) :=
    abs_le.mpr (by simpa [symmetricInterval, burnolUnscaledCommonGapRadius] using hx)
  rw [burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source inside,
    burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source
      (t := 0) (by norm_num)]

theorem burnolMobiusFixedWindow_sum (raw : ℝ → ℂ)
    (quarterGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = raw 0)
    (x : ℝ) (inside : |x| ≤ 4) :
    burnolCenteredMobiusInverse raw x =
      ∑ m ∈ burnolCenteredMobiusCutoffFinset 4,
        burnolCenteredMobiusSummand raw x m := by
  change (∑' m : ℕ+, burnolCenteredMobiusSummand raw x m) = _
  apply tsum_eq_sum
  intro m notMem
  apply burnolCenteredMobiusSummand_eq_zero_of_cutoff_le raw quarterGap x m
  have large : burnolCenteredMobiusCutoff 4 ≤ (m : ℕ) :=
    Nat.le_of_not_gt (by simpa using notMem)
  apply le_trans ?_ large
  apply Nat.ceil_mono
  change 4 * |x| ≤ 4 * |(4 : ℝ)|
  norm_num
  linarith

theorem burnolMobiusWindowSourceRead_compact_source (source : burnolCompactAnnulusSource) :
    (burnolMobiusWindowSourceRead (burnolCompactAdditivePhysicalState source) :
      ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval 4)]
        burnolCompactAdditiveSource source := by
  have sourceReads : ∀ᵐ x : ℝ ∂volume, ∀ m : ℕ+,
      burnolCompactAdditiveL2 source (x / (m : ℕ)) =
        burnolCompactAdditiveCoSum source (x / (m : ℕ)) := by
    apply ae_all_iff.mpr
    intro m
    have nonzero : (((m : ℕ) : ℝ)⁻¹) ≠ 0 := by
      exact inv_ne_zero (by exact_mod_cast m.ne_zero)
    have qmp := Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := (((m : ℕ) : ℝ)⁻¹)) nonzero
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      qmp.ae (burnolCompactAdditiveL2_coeFn source)
  filter_upwards [burnolMobiusWindowSourceRead_coeFn
      (burnolCompactAdditivePhysicalState source),
    ae_restrict_of_ae (s := symmetricInterval 4) sourceReads,
    ae_restrict_mem (measurableSet_symmetricInterval (4 : ℝ))]
    with x generated sourceRead hx
  rw [generated, burnolCompactGapCoefficient]
  have sumRead :
      (∑ m ∈ burnolCenteredMobiusCutoffFinset 4,
        ((ArithmeticFunction.moebius (m : ℕ) : ℂ) * ((m : ℕ) : ℂ)⁻¹) *
          ((burnolCompactAdditivePhysicalState source : BurnolL2) (x / (m : ℕ)) -
            burnolCompactAdditiveCoSum source 0)) =
        ∑ m ∈ burnolCenteredMobiusCutoffFinset 4,
          burnolCenteredMobiusSummand (burnolCompactAdditiveCoSum source) x m := by
    apply Finset.sum_congr rfl
    intro m hm
    change ((ArithmeticFunction.moebius (m : ℕ) : ℂ) * ((m : ℕ) : ℂ)⁻¹) *
      (burnolCompactAdditiveL2 source (x / (m : ℕ)) -
        burnolCompactAdditiveCoSum source 0) = _
    rw [sourceRead m]
    unfold burnolCenteredMobiusSummand
    ring
  rw [sumRead, ← burnolMobiusFixedWindow_sum]
  · exact burnolCompactCenteredMobiusInverse_roundtrip source x
  · intro t small
    rw [burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source small,
      burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source
        (t := 0) (by norm_num)]
  · exact abs_le.mpr (by simpa [symmetricInterval] using hx)


theorem burnolAmbientGap_ae (value : Ambient) :
    (value : BurnolL2) =ᵐ[volume.restrict
      (symmetricInterval burnolUnscaledCommonGapRadius)]
        fun _ => burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
  obtain ⟨coefficient, sourceGap⟩ :=
    mem_locallyConstantFace_iff_exists.mp value.2.1.1
  have mean := burnolConstantGapCoefficient_eq burnolUnscaledCommonGapRadius
    (by norm_num [burnolUnscaledCommonGapRadius]) value coefficient sourceGap
  rw [mean]
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval burnolUnscaledCommonGapRadius) (value : BurnolL2),
    intervalConstant_coeFn burnolUnscaledCommonGapRadius,
    Lp.coeFn_smul coefficient (intervalConstant burnolUnscaledCommonGapRadius)]
    with x hrestrict hconstant hsmul
  calc
    (value : BurnolL2) x = restrictToInterval burnolUnscaledCommonGapRadius
        (value : BurnolL2) x := hrestrict.symm
    _ = (coefficient • intervalConstant burnolUnscaledCommonGapRadius) x := by
      rw [sourceGap]
    _ = coefficient * intervalConstant burnolUnscaledCommonGapRadius x := hsmul
    _ = coefficient := by rw [hconstant, mul_one]

theorem burnolMobiusWindowSourceRead_innerGap (value : Ambient) :
    (burnolMobiusWindowSourceRead value : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval burnolUnscaledCommonGapRadius)] fun _ => 0 := by
  have gapGlobal := (ae_restrict_iff'
    (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)).mp
      (burnolAmbientGap_ae value)
  have scaled : ∀ᵐ x : ℝ ∂volume, ∀ m : ℕ+,
      x / ((m : ℕ) : ℝ) ∈ symmetricInterval burnolUnscaledCommonGapRadius →
        (value : BurnolL2) (x / (m : ℕ)) =
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
    apply ae_all_iff.mpr
    intro m
    have nonzero : (((m : ℕ) : ℝ)⁻¹) ≠ 0 :=
      inv_ne_zero (by exact_mod_cast m.ne_zero)
    have qmp := Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := (((m : ℕ) : ℝ)⁻¹)) nonzero
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using qmp.ae gapGlobal
  have readGlobal := (ae_restrict_iff'
    (measurableSet_symmetricInterval (4 : ℝ))).mp
      (burnolMobiusWindowSourceRead_coeFn value)
  filter_upwards [ae_restrict_of_ae scaled, ae_restrict_of_ae readGlobal,
    ae_restrict_mem (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)]
    with x hscaled hread hx
  have absSmall : |x| ≤ (1 / 4 : ℝ) :=
    abs_le.mpr (by simpa [symmetricInterval, burnolUnscaledCommonGapRadius] using hx)
  have outer : x ∈ symmetricInterval 4 := by
    have bound := abs_le.mp absSmall
    simp only [symmetricInterval, mem_Icc]
    constructor <;> linarith
  rw [hread outer]
  apply Finset.sum_eq_zero
  intro m hm
  have positive : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.property
  have atLeastOne : (1 : ℝ) ≤ (m : ℕ) := by exact_mod_cast m.property
  have inside : x / ((m : ℕ) : ℝ) ∈ symmetricInterval burnolUnscaledCommonGapRadius := by
    have bound : |x / ((m : ℕ) : ℝ)| ≤ (1 / 4 : ℝ) := by
      rw [abs_div, abs_of_pos positive]
      apply (div_le_iff₀ positive).mpr
      nlinarith
    simpa [symmetricInterval, burnolUnscaledCommonGapRadius] using abs_le.mp bound
  rw [hscaled m inside, sub_self, mul_zero]

theorem burnolMobiusSourceExtension_compact_coeFn (source : burnolCompactAnnulusSource) :
    (burnolRadiusZeroExtension 4
      (burnolMobiusWindowSourceRead (burnolCompactAdditivePhysicalState source)) :
        ℝ → ℂ) =ᵐ[volume] burnolCompactAdditiveSource source := by
  have sourceRead := (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
    (burnolMobiusWindowSourceRead_compact_source source)
  filter_upwards [burnolRadiusZeroExtension_coe
    (burnolMobiusWindowSourceRead (burnolCompactAdditivePhysicalState source)),
    sourceRead] with x hext hsource
  rw [hext]
  by_cases inside : x ∈ symmetricInterval 4
  · rw [Set.indicator_of_mem inside]
    exact hsource inside
  · rw [Set.indicator_of_notMem inside]
    symm
    apply burnolCompactAdditiveSource_zero_of_four_le_abs
    have outside : ¬ |x| ≤ 4 := by
      intro bound
      exact inside (abs_le.mp bound)
    exact (lt_of_not_ge outside).le

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
