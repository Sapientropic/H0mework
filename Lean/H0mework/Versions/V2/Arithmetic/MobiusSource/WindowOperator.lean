import H0mework.Arithmetic.MobiusSource.MobiusFiniteCutoff
import H0mework.Versions.V2.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusActualBridge

/-!
# Finite Möbius source extraction on the actual Hilbert carrier

The quarter gap fixes the finite divisor read on the radius-four window.
Actual dilation and the same continuous gap mean generate the map; no point
representative or inverse certificate is supplied.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators InnerProductSpace ENNReal
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "Window" => BurnolRadiusIntervalL2 4

/-- Unnormalized scale pullback, obtained from the actual unitary dilation. -/
def burnolWindowScalePullback (radius : ℝ) (m : ℕ+) :
    BurnolL2 →L[ℂ] BurnolRadiusIntervalL2 radius :=
  (Real.exp (Real.log (m : ℕ) / 2) : ℂ) •
    ((burnolRadiusRestriction radius).comp
      (burnolMultiplicativeDilation (-Real.log (m : ℕ))).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Actual finite-scale pullback, with the source-owned gap constant retained. -/
def burnolMobiusWindowPullback (m : ℕ+) : Ambient →L[ℂ] Window :=
  ((burnolWindowScalePullback 4 m).comp
    (Submodule.subtypeL (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)) -
    ((ContinuousLinearMap.toSpanSingleton ℂ (intervalConstant 4)).comp
      (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius))

/-- The fixed finite Möbius sum and its source-owned gap subtraction. -/
def burnolMobiusWindowSourceRead : Ambient →L[ℂ] Window :=
  ∑ m ∈ burnolCenteredMobiusCutoffFinset 4,
    ((ArithmeticFunction.moebius (m : ℕ) : ℂ) * ((m : ℕ) : ℂ)⁻¹) •
      burnolMobiusWindowPullback m

theorem burnolWindowScalePullback_coeFn (radius : ℝ) (m : ℕ+) (value : BurnolL2) :
    (burnolWindowScalePullback radius m value : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval radius)] fun x => value (x / (m : ℕ)) := by
  let weight : ℂ := Real.exp (Real.log (m : ℕ) / 2)
  let dilated := burnolMultiplicativeDilation (-Real.log (m : ℕ)) value
  let restricted := burnolRadiusRestriction radius dilated
  change ((weight • restricted : BurnolRadiusIntervalL2 radius) : ℝ → ℂ) =ᵐ[_] _
  filter_upwards [Lp.coeFn_smul weight restricted,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) dilated,
    ae_restrict_of_ae (s := symmetricInterval radius)
      (burnolMultiplicativeDilation_coeFn (-Real.log (m : ℕ)) value)]
    with x hscale hrestrict hdilation
  rw [hscale]
  change weight * burnolRadiusRestriction radius dilated x = _
  rw [show burnolRadiusRestriction radius dilated x = dilated x from hrestrict,
    show dilated x = burnolL2RawNormalizedDilation (-Real.log (m : ℕ)) value x
      from hdilation]
  have positive : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.property
  unfold burnolL2RawNormalizedDilation
  rw [Real.exp_neg, Real.exp_log positive]
  dsimp only [weight]
  rw [← mul_assoc]
  have cancel : (Real.exp (Real.log (m : ℕ) / 2) : ℂ) *
      (Real.exp (-Real.log (m : ℕ) / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add,
      show Real.log (m : ℕ) / 2 + -Real.log (m : ℕ) / 2 = 0 by ring,
      Real.exp_zero, Complex.ofReal_one]
  rw [cancel, one_mul]
  congr 1
  simp [div_eq_mul_inv, mul_comm]

theorem burnolMobiusWindowPullback_coeFn (m : ℕ+) (value : Ambient) :
    (burnolMobiusWindowPullback m value : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval 4)]
      fun x => (value : BurnolL2) (x / (m : ℕ)) -
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
  let weight : ℂ := Real.exp (Real.log (m : ℕ) / 2)
  let dilated := burnolMultiplicativeDilation (-Real.log (m : ℕ)) (value : BurnolL2)
  let restricted := burnolRadiusRestriction 4 dilated
  let mean := burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value
  change ((weight • restricted - mean • intervalConstant 4 : Window) : ℝ → ℂ) =ᵐ[
    volume.restrict (symmetricInterval 4)] _
  filter_upwards [Lp.coeFn_sub (weight • restricted) (mean • intervalConstant 4),
    Lp.coeFn_smul weight restricted, Lp.coeFn_smul mean (intervalConstant 4),
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval 4) dilated,
    ae_restrict_of_ae (s := symmetricInterval 4)
      (burnolMultiplicativeDilation_coeFn (-Real.log (m : ℕ)) (value : BurnolL2)),
    intervalConstant_coeFn 4] with x hsub hscale hmean hrestrict hdilation hconstant
  rw [hsub]
  change (weight • restricted : Window) x - (mean • intervalConstant 4 : Window) x = _
  rw [hscale, hmean]
  change weight * restricted x - mean * intervalConstant 4 x = _
  rw [hconstant, mul_one]
  change weight * burnolRadiusRestriction 4 dilated x - mean = _
  rw [show burnolRadiusRestriction 4 dilated x = dilated x from hrestrict]
  rw [show dilated x = burnolL2RawNormalizedDilation (-Real.log (m : ℕ))
    (value : BurnolL2) x from hdilation]
  have positive : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.property
  unfold burnolL2RawNormalizedDilation
  have scale : Real.exp (-Real.log (m : ℕ)) = ((m : ℕ) : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log positive]
  rw [scale]
  dsimp only [weight]
  rw [← mul_assoc]
  have cancel : (Real.exp (Real.log (m : ℕ) / 2) : ℂ) *
      (Real.exp (-Real.log (m : ℕ) / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add,
      show Real.log (m : ℕ) / 2 + -Real.log (m : ℕ) / 2 = 0 by ring,
      Real.exp_zero, Complex.ofReal_one]
  rw [cancel, one_mul]
  congr 2
  simp [div_eq_mul_inv, mul_comm]

theorem burnolMobiusWindowSourceRead_coeFn (value : Ambient) :
    (burnolMobiusWindowSourceRead value : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval 4)] fun x =>
      ∑ m ∈ burnolCenteredMobiusCutoffFinset 4,
        ((ArithmeticFunction.moebius (m : ℕ) : ℂ) * ((m : ℕ) : ℂ)⁻¹) *
          ((value : BurnolL2) (x / (m : ℕ)) -
            burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value) := by
  let coefficient (m : ℕ+) : ℂ :=
    (ArithmeticFunction.moebius (m : ℕ) : ℂ) * ((m : ℕ) : ℂ)⁻¹
  have finiteRead (indices : Finset ℕ+) :
      ((∑ m ∈ indices, coefficient m • burnolMobiusWindowPullback m value : Window) :
        ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval 4)] fun x =>
          ∑ m ∈ indices, coefficient m *
            ((value : BurnolL2) (x / (m : ℕ)) -
              burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value) := by
    induction indices using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using!
          (Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval 4)))
    | @insert m indices notMem previous =>
        rw [Finset.sum_insert notMem]
        simp_rw [Finset.sum_insert notMem]
        filter_upwards [Lp.coeFn_add
          (coefficient m • burnolMobiusWindowPullback m value)
          (∑ n ∈ indices, coefficient n • burnolMobiusWindowPullback n value),
          Lp.coeFn_smul (coefficient m) (burnolMobiusWindowPullback m value),
          burnolMobiusWindowPullback_coeFn m value, previous]
          with x hadd hsmul hpull hprevious
        rw [hadd]
        change (coefficient m • burnolMobiusWindowPullback m value : Window) x +
          (∑ n ∈ indices, coefficient n • burnolMobiusWindowPullback n value : Window) x = _
        rw [hsmul]
        change coefficient m * burnolMobiusWindowPullback m value x + _ = _
        rw [hpull, hprevious]
  simpa only [burnolMobiusWindowSourceRead, sum_apply,
    smul_apply, coefficient] using
    finiteRead (burnolCenteredMobiusCutoffFinset 4)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
