import H0mework.Physics.GaugeSource.ReducedEntropyDescent

/-!
# Coefficient-computed safe step for the reduced P286 entropy

The reduced compact relative action is already an exact quartic with first
coefficient `-defect`.  This module performs only the final real-algebra
calculation.  The step is computed from the current defect and the absolute
values of the three current tail coefficients; no sign, Hessian, coercivity,
descent, future-state, or stationarity premise is accepted.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286SourceNativeReducedEntropySafeStep

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugePointwiseEquation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineHolonomicField
open StageNineP286JointYangMillsGradientFlowRegularity
open StageNineP286SourceNativeReducedEntropyDescent

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Pure quartic safe-step algebra -/

def p286QuarticTailBudget (second third fourth : ℝ) : ℝ :=
  |second| + |third| + |fourth|

def p286QuarticNegativeDefectSafeStep
    (defect second third fourth : ℝ) : ℝ :=
  defect /
    (2 * (1 + defect + p286QuarticTailBudget second third fourth))

theorem p286QuarticNegativeDefectSafeStep_strict
    (defect second third fourth : ℝ)
    (defectPositive : 0 < defect) :
    let step :=
      p286QuarticNegativeDefectSafeStep defect second third fourth
    step * (-defect) + step ^ 2 * second + step ^ 3 * third +
        step ^ 4 * fourth < 0 := by
  dsimp only
  let tail := p286QuarticTailBudget second third fourth
  let denominator : ℝ := 2 * (1 + defect + tail)
  let step : ℝ := defect / denominator
  change step * (-defect) + step ^ 2 * second + step ^ 3 * third +
      step ^ 4 * fourth < 0
  have secondAbsNonnegative : 0 ≤ |second| := abs_nonneg second
  have thirdAbsNonnegative : 0 ≤ |third| := abs_nonneg third
  have fourthAbsNonnegative : 0 ≤ |fourth| := abs_nonneg fourth
  have tailNonnegative : 0 ≤ tail := by
    dsimp [tail, p286QuarticTailBudget]
    positivity
  have denominatorPositive : 0 < denominator := by
    dsimp [denominator]
    positivity
  have denominatorNonzero : denominator ≠ 0 := ne_of_gt denominatorPositive
  have stepPositive : 0 < step := div_pos defectPositive denominatorPositive
  have stepNonnegative : 0 ≤ step := stepPositive.le
  have stepDenominator : step * denominator = defect := by
    dsimp [step]
    exact div_mul_cancel₀ defect denominatorNonzero
  have defect_lt_denominator : defect < denominator := by
    dsimp [denominator]
    nlinarith
  have step_lt_one : step < 1 := by
    dsimp [step]
    exact (div_lt_one denominatorPositive).2 defect_lt_denominator
  have step_le_one : step ≤ 1 := step_lt_one.le
  have stepCube_le_stepSquare : step ^ 3 ≤ step ^ 2 := by
    have productNonnegative : 0 ≤ step ^ 2 * (1 - step) :=
      mul_nonneg (sq_nonneg step) (sub_nonneg.mpr step_le_one)
    nlinarith
  have stepSquare_le_one : step ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg stepNonnegative (sub_nonneg.mpr step_le_one)]
  have stepFourth_le_stepSquare : step ^ 4 ≤ step ^ 2 := by
    have productNonnegative : 0 ≤ step ^ 2 * (1 - step ^ 2) :=
      mul_nonneg (sq_nonneg step) (sub_nonneg.mpr stepSquare_le_one)
    nlinarith
  have secondTermBound : step ^ 2 * second ≤ step ^ 2 * |second| :=
    mul_le_mul_of_nonneg_left (le_abs_self second) (sq_nonneg step)
  have thirdTermAbs : step ^ 3 * third ≤ step ^ 3 * |third| :=
    mul_le_mul_of_nonneg_left (le_abs_self third) (by positivity)
  have thirdPowerBound : step ^ 3 * |third| ≤ step ^ 2 * |third| :=
    mul_le_mul_of_nonneg_right stepCube_le_stepSquare thirdAbsNonnegative
  have thirdTermBound : step ^ 3 * third ≤ step ^ 2 * |third| :=
    thirdTermAbs.trans thirdPowerBound
  have fourthTermAbs : step ^ 4 * fourth ≤ step ^ 4 * |fourth| :=
    mul_le_mul_of_nonneg_left (le_abs_self fourth) (by positivity)
  have fourthPowerBound : step ^ 4 * |fourth| ≤ step ^ 2 * |fourth| :=
    mul_le_mul_of_nonneg_right stepFourth_le_stepSquare fourthAbsNonnegative
  have fourthTermBound : step ^ 4 * fourth ≤ step ^ 2 * |fourth| :=
    fourthTermAbs.trans fourthPowerBound
  have tailBound :
      step ^ 2 * second + step ^ 3 * third + step ^ 4 * fourth ≤
        step ^ 2 * tail := by
    dsimp [tail, p286QuarticTailBudget]
    nlinarith
  have twiceStepTail_lt_defect : 2 * step * tail < defect := by
    dsimp [denominator] at stepDenominator
    nlinarith
  have twiceSquareTail_lt_stepDefect :
      2 * (step ^ 2 * tail) < step * defect := by
    have scaled :=
      mul_lt_mul_of_pos_left twiceStepTail_lt_defect stepPositive
    nlinarith
  nlinarith

theorem p286QuarticNegativeDefectSafeStep_nonpositive
    (defect second third fourth : ℝ)
    (defectNonnegative : 0 ≤ defect) :
    let step :=
      p286QuarticNegativeDefectSafeStep defect second third fourth
    step * (-defect) + step ^ 2 * second + step ^ 3 * third +
        step ^ 4 * fourth ≤ 0 := by
  by_cases defectZero : defect = 0
  · simp [defectZero, p286QuarticNegativeDefectSafeStep]
  · exact
      (p286QuarticNegativeDefectSafeStep_strict defect second third fourth
        (lt_of_le_of_ne defectNonnegative (Ne.symm defectZero))).le

/-! ## Source-computed reduced joint next -/

def p286ReducedEntropyStepSize
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) : ℝ :=
  p286QuarticNegativeDefectSafeStep
    (p286ReducedEntropyDefect source current)
    (p286ReducedEntropySecondCoefficient source current smooth nondegenerate)
    (p286ReducedEntropyThirdCoefficient source current smooth nondegenerate)
    (p286ReducedEntropyFourthCoefficient source current smooth nondegenerate)

/-- Generated finite state: exact compact connection step, curvature
recomputation, and exact constitutive auxiliary recomputation. -/
def p286ReducedEntropyNext
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    StageNineHolonomicConfiguration :=
  p286ReducedEntropyJointPath source current smooth nondegenerate
    (p286ReducedEntropyStepSize source current smooth nondegenerate)

theorem p286ReducedEntropyNext_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (p286ReducedEntropyNext source current smooth nondegenerate
      ).Nondegenerate := by
  exact formNativeP286GaugeConstitutiveReadout_nondegenerate source
    (p286ReducedEntropyRawPath source current smooth nondegenerate
      (p286ReducedEntropyStepSize source current smooth nondegenerate))
    (p286ReducedEntropyRawPath_nondegenerate source current smooth
      nondegenerate
      (p286ReducedEntropyStepSize source current smooth nondegenerate))

theorem p286ReducedEntropyNext_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (p286ReducedEntropyNext source current smooth nondegenerate).Smooth := by
  exact formNativeP286GaugeConstitutiveReadout_smooth source
    (p286ReducedEntropyRawPath source current smooth nondegenerate
      (p286ReducedEntropyStepSize source current smooth nondegenerate))
    (p286ReducedEntropyRawPath_smooth source current smooth nondegenerate
      (p286ReducedEntropyStepSize source current smooth nondegenerate))
    (p286ReducedEntropyRawPath_nondegenerate source current smooth
      nondegenerate
      (p286ReducedEntropyStepSize source current smooth nondegenerate))

theorem p286ReducedEntropyNext_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source
      (p286ReducedEntropyNext source current smooth nondegenerate) := by
  exact formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation source
    (p286ReducedEntropyRawPath source current smooth nondegenerate
      (p286ReducedEntropyStepSize source current smooth nondegenerate))
    (p286ReducedEntropyRawPath_nondegenerate source current smooth
      nondegenerate
      (p286ReducedEntropyStepSize source current smooth nondegenerate))

theorem p286ReducedEntropy_relativeAction_nonpositive
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    p286ReducedEntropyRelativeAction source current smooth nondegenerate
        (p286ReducedEntropyStepSize source current smooth nondegenerate) ≤ 0 := by
  rw [p286ReducedEntropyRelativeAction_quartic source current smooth
    nondegenerate]
  rw [p286ReducedEntropyFirstCoefficient_eq_neg_defect]
  exact p286QuarticNegativeDefectSafeStep_nonpositive
    (p286ReducedEntropyDefect source current)
    (p286ReducedEntropySecondCoefficient source current smooth nondegenerate)
    (p286ReducedEntropyThirdCoefficient source current smooth nondegenerate)
    (p286ReducedEntropyFourthCoefficient source current smooth nondegenerate)
    (p286ReducedEntropyDefect_nonnegative source current)

theorem p286ReducedEntropy_relativeAction_strict
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (defectPositive : 0 < p286ReducedEntropyDefect source current) :
    p286ReducedEntropyRelativeAction source current smooth nondegenerate
        (p286ReducedEntropyStepSize source current smooth nondegenerate) < 0 := by
  rw [p286ReducedEntropyRelativeAction_quartic source current smooth
    nondegenerate]
  rw [p286ReducedEntropyFirstCoefficient_eq_neg_defect]
  exact p286QuarticNegativeDefectSafeStep_strict
    (p286ReducedEntropyDefect source current)
    (p286ReducedEntropySecondCoefficient source current smooth nondegenerate)
    (p286ReducedEntropyThirdCoefficient source current smooth nondegenerate)
    (p286ReducedEntropyFourthCoefficient source current smooth nondegenerate)
    defectPositive

theorem p286ReducedEntropy_relativeAction_strict_of_origin_euler_ne_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (originNonzero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0
        (p286ReducedEntropyBase source current) 0 ≠ 0) :
    p286ReducedEntropyRelativeAction source current smooth nondegenerate
        (p286ReducedEntropyStepSize source current smooth nondegenerate) < 0 :=
  p286ReducedEntropy_relativeAction_strict source current smooth nondegenerate
    (p286ReducedEntropyDefect_pos_of_origin_euler_ne_zero source current smooth
      nondegenerate originNonzero)

theorem p286ReducedEntropyNext_ne_base_of_defect_pos
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (defectPositive : 0 < p286ReducedEntropyDefect source current) :
    p286ReducedEntropyNext source current smooth nondegenerate ≠
      p286ReducedEntropyBase source current := by
  intro nextEq
  have strict := p286ReducedEntropy_relativeAction_strict source current smooth
    nondegenerate defectPositive
  have relativeZero :
      p286ReducedEntropyRelativeAction source current smooth nondegenerate
          (p286ReducedEntropyStepSize source current smooth nondegenerate) =
        0 := by
    unfold p286ReducedEntropyNext at nextEq
    unfold p286ReducedEntropyRelativeAction
    rw [nextEq]
    simp
  exact (ne_of_lt strict) relativeZero

end
end StageNineP286SourceNativeReducedEntropySafeStep
end PhysicsCore
end SaturationMonoid
