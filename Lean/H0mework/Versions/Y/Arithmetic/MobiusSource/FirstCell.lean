import H0mework.Versions.Y.Arithmetic.MobiusSource.SourceRead
import H0mework.Arithmetic.SonineProjection.MeanZeroBlock
import H0mework.Versions.Y.Arithmetic.RiemannDivision.DirectRightResolvent

/-! The actual Möbius source on its first cell, including its same gap mean. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "q" => (1 / 4 : ℝ)

/-- On the first source cell every nonunit divisor lands in the original
quarter gap.  The actual finite Möbius read is therefore value minus its mean. -/
theorem burnolMobiusSource_firstCell (value : Ambient) :
    (burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value) : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 2 : ℝ))] fun x =>
        (value : BurnolL2) x -
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
  have gapGlobal := (ae_restrict_iff'
    (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)).mp
      (burnolAmbientGap_ae value)
  have scaled : ∀ᵐ x : ℝ ∂volume, ∀ m : ℕ+,
      x / ((m : ℕ) : ℝ) ∈ symmetricInterval burnolUnscaledCommonGapRadius →
        (value : BurnolL2) (x / (m : ℕ)) =
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
    apply ae_all_iff.mpr
    intro m
    have qmp := Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := (((m : ℕ) : ℝ)⁻¹))
        (inv_ne_zero (by exact_mod_cast m.ne_zero))
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using qmp.ae gapGlobal
  have readGlobal := (ae_restrict_iff' (measurableSet_symmetricInterval (4 : ℝ))).mp
    (burnolMobiusWindowSourceRead_coeFn value)
  filter_upwards [ae_restrict_of_ae scaled, ae_restrict_of_ae readGlobal,
    ae_restrict_of_ae (burnolRadiusZeroExtension_coe (burnolMobiusWindowSourceRead value)),
    ae_restrict_mem (measurableSet_symmetricInterval (1 / 2 : ℝ))]
    with x hscaled hread hext hx
  have halfBound : |x| ≤ (1 / 2 : ℝ) := abs_le.mpr (by
    simpa [symmetricInterval] using hx)
  have inWindow : x ∈ symmetricInterval 4 := by
    have bound := abs_le.mp halfBound
    simp only [symmetricInterval, mem_Icc]
    constructor <;> linarith
  rw [hext, Set.indicator_of_mem inWindow, hread inWindow]
  have oneMem : (1 : ℕ+) ∈ burnolCenteredMobiusCutoffFinset 4 := by
    norm_num [burnolCenteredMobiusCutoff]
  rw [Finset.sum_eq_single (1 : ℕ+)]
  · simp
  · intro m hm notOne
    have twoLe : (2 : ℝ) ≤ (m : ℕ) := by
      have notOneNat : (m : ℕ) ≠ 1 := by
        intro equality
        exact notOne (PNat.coe_injective equality)
      have twoNat : 2 ≤ (m : ℕ) :=
        lt_of_le_of_ne (show 1 ≤ (m : ℕ) from m.property) (Ne.symm notOneNat)
      exact_mod_cast twoNat
    have positive : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.property
    have small : x / ((m : ℕ) : ℝ) ∈ symmetricInterval burnolUnscaledCommonGapRadius := by
      have bound : |x / ((m : ℕ) : ℝ)| ≤ q := by
        rw [abs_div, abs_of_pos positive]
        apply (div_le_iff₀ positive).mpr
        nlinarith
      simpa [symmetricInterval, burnolUnscaledCommonGapRadius] using abs_le.mp bound
    rw [hscaled m small, sub_self, mul_zero]
  · intro missing
    exact False.elim (missing oneMem)


theorem burnolMobiusSourceDilation_quarterRead (shift : ℝ)
    (small : shift ≤ Real.log 2) (value : Ambient) :
    let source := burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value)
    burnolQuarterRestriction (burnolMultiplicativeDilation shift source) =
      burnolQuarterRestriction (burnolMultiplicativeDilation shift (value : BurnolL2)) -
        ((Real.exp (shift / 2) : ℂ) *
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value) •
            intervalConstant q := by
  dsimp only
  let source := burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value)
  let mean := burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value
  let weight : ℂ := Real.exp (shift / 2)
  let sourceMoved := burnolMultiplicativeDilation shift source
  let valueMoved := burnolMultiplicativeDilation shift (value : BurnolL2)
  have sourceGlobal := (ae_restrict_iff'
    (measurableSet_symmetricInterval (1 / 2 : ℝ))).mp
      (burnolMobiusSource_firstCell value)
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  have scaleLe : Real.exp shift ≤ 2 := by
    exact (Real.exp_le_exp.mpr small).trans_eq (Real.exp_log (by norm_num))
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) sourceMoved,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) valueMoved,
    Lp.coeFn_sub (burnolQuarterRestriction valueMoved)
      ((weight * mean) • intervalConstant q),
    Lp.coeFn_smul (weight * mean) (intervalConstant q),
    intervalConstant_coeFn q,
    ae_restrict_of_ae (s := symmetricInterval q)
      (burnolMultiplicativeDilation_coeFn shift source),
    ae_restrict_of_ae (s := symmetricInterval q)
      (burnolMultiplicativeDilation_coeFn shift (value : BurnolL2)),
    ae_restrict_of_ae (s := symmetricInterval q) (qmp.ae sourceGlobal),
    ae_restrict_mem (measurableSet_symmetricInterval q)]
    with x hsourceRead hvalueRead hsub hsmul hconstant hsourceAction hvalueAction hsource hx
  have imageInside : Real.exp shift * x ∈ symmetricInterval (1 / 2 : ℝ) := by
    have localBound : |x| ≤ q := abs_le.mpr (by simpa [symmetricInterval] using hx)
    have bound : |Real.exp shift * x| ≤ (1 / 2 : ℝ) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos shift)]
      nlinarith [abs_nonneg x, Real.exp_pos shift]
    simpa [symmetricInterval] using abs_le.mp bound
  change burnolQuarterRestriction sourceMoved x =
    (burnolQuarterRestriction valueMoved - (weight * mean) • intervalConstant q :
      BurnolQuarterIntervalL2) x
  rw [hsub]
  change burnolQuarterRestriction sourceMoved x =
    burnolQuarterRestriction valueMoved x -
      ((weight * mean) • intervalConstant q : BurnolQuarterIntervalL2) x
  rw [show burnolQuarterRestriction sourceMoved x = sourceMoved x from hsourceRead,
    show burnolQuarterRestriction valueMoved x = valueMoved x from hvalueRead, hsmul]
  change sourceMoved x = valueMoved x - (weight * mean) * intervalConstant q x
  rw [hconstant, mul_one]
  rw [show sourceMoved x = burnolL2RawNormalizedDilation shift source x from hsourceAction,
    show valueMoved x = burnolL2RawNormalizedDilation shift (value : BurnolL2) x
      from hvalueAction]
  unfold burnolL2RawNormalizedDilation
  change weight * source (Real.exp shift * x) =
    weight * (value : BurnolL2) (Real.exp shift * x) - weight * mean
  have sourceEq : source (Real.exp shift * x) =
      (value : BurnolL2) (Real.exp shift * x) - mean := hsource imageInside
  rw [sourceEq]
  ring


theorem burnolMobiusSourceDilation_meanZero (shift : ℝ)
    (small : shift ≤ Real.log 2) (value : Ambient) :
    let source := burnolRadiusZeroExtension 4 (burnolMobiusWindowSourceRead value)
    burnolQuarterMeanZeroProjection
      (burnolQuarterRestriction (burnolMultiplicativeDilation shift source)) =
    burnolQuarterMeanZeroProjection
      (burnolQuarterRestriction (burnolMultiplicativeDilation shift (value : BurnolL2))) := by
  dsimp only
  rw [burnolMobiusSourceDilation_quarterRead shift small value, map_sub]
  have constantZero : burnolQuarterMeanZeroProjection
      (((Real.exp (shift / 2) : ℂ) *
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value) •
          intervalConstant q) = 0 := by
    apply (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
    exact (intervalConstantLine q).smul_mem _
      (Submodule.mem_span_singleton_self _)
  rw [constantZero, sub_zero]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
