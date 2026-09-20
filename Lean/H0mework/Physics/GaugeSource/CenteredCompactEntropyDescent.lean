import H0mework.Physics.GaugeSource.CompactEntropyDescent
import H0mework.Physics.SafeCauchy.FixedClassicalCandidateFamily
import H0mework.Physics.SafeCauchy.FixedP286JointYangMillsOperation

/-!
# Jointly conservative centered P286 entropy windows

The fixed origin window gives a genuine finite action descent, but one window
cannot detect a residual supported elsewhere.  This module translates the
same source-owned unit bump through every spacetime point.  No center is
selected by a scheduler: the whole centered family is the observable, and it
is jointly conservative.

```text
current + center
  -> translated unit material window
  -> compact negative action gradient
  -> exact local defect

all centered defects vanish
  <-> the complete P286 connection Euler field vanishes.
```

Thus the entropy family detects the all-point normal form without smuggling a
target field or assuming stationarity.  A runtime may activate a particular
center only when that center is supplied by an actual source occurrence.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286SourceNativeCenteredCompactEntropyDescent

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeClassicalWorldCandidateFamily
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeP286JointYangMillsOperation
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeMotherAction
open StageNineFormNativeP286GaugeConnectionIntegratedVariation
open StageNineFormNativeP286GaugeConnectionLocalVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugePointwiseEquation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286JointYangMillsGradientFlow
open StageNineP286JointYangMillsGradientFlowRegularity
open StageNineP286SourceNativeCompactEntropyDescent
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance centeredCompactEntropyP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective

local instance centeredCompactEntropyP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Translated canonical material window -/

/-- The unique translate of the already fixed unit compact bump to `center`.
The center is an observation index, not a supplied solution coordinate. -/
def p286CenteredCompactScalarWindow
    (center point : BasePoint) : ℝ :=
  nonzeroCompactScalarVariation (point - center)

theorem p286CenteredCompactScalarWindow_contDiff
    (center : BasePoint) :
    ContDiff ℝ ∞ (p286CenteredCompactScalarWindow center) := by
  exact nonzeroCompactScalarVariation.smooth.comp
    (contDiff_id.sub contDiff_const)

theorem p286CenteredCompactScalarWindow_hasCompactSupport
    (center : BasePoint) :
    HasCompactSupport (p286CenteredCompactScalarWindow center) := by
  change HasCompactSupport
    (nonzeroCompactScalarVariation ∘ (Homeomorph.subRight center : BasePoint ≃ₜ BasePoint))
  exact nonzeroCompactScalarVariation.compactSupport.comp_homeomorph
    (Homeomorph.subRight center)

theorem p286CenteredCompactScalarWindow_nonnegative
    (center point : BasePoint) :
    0 ≤ p286CenteredCompactScalarWindow center point :=
  unitCompactBump.nonneg

@[simp] theorem p286CenteredCompactScalarWindow_center
    (center : BasePoint) :
    p286CenteredCompactScalarWindow center center = 1 := by
  change unitCompactBump (center - center) = 1
  rw [sub_self]
  apply unitCompactBump.one_of_mem_closedBall
  exact Metric.mem_closedBall_self unitCompactBump.rIn_pos.le

/-! ## Centered compact negative gradient and defect -/

def p286CenteredCompactNegativeGradient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (center : BasePoint) :
    BasePoint → P286GaugeOneForm :=
  fun point =>
    (-p286CenteredCompactScalarWindow center point) •
      p286JointYangMillsActionGradient source current point

theorem p286CenteredCompactNegativeGradient_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    ContDiff ℝ ∞
      (p286CenteredCompactNegativeGradient source current center) := by
  exact (p286CenteredCompactScalarWindow_contDiff center).neg.smul
    (p286JointYangMillsActionGradient_contDiff source current smooth
      nondegenerate)

theorem p286CenteredCompactNegativeGradient_hasCompactSupport
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (center : BasePoint) :
    HasCompactSupport
      (p286CenteredCompactNegativeGradient source current center) := by
  have windowCompact :=
    p286CenteredCompactScalarWindow_hasCompactSupport center
  rw [hasCompactSupport_iff_eventuallyEq] at windowCompact ⊢
  filter_upwards [windowCompact] with point windowZero
  simp [p286CenteredCompactNegativeGradient, windowZero]

def p286CenteredCompactNegativeGradientVariation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    CompactlySupportedSmoothVariation P286GaugeOneForm where
  toFun := p286CenteredCompactNegativeGradient source current center
  smooth := p286CenteredCompactNegativeGradient_contDiff source current smooth
    nondegenerate center
  compactSupport :=
    p286CenteredCompactNegativeGradient_hasCompactSupport source current center

/-- The action defect visible in the translated compact material window. -/
def p286CenteredCompactActionDefect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (center : BasePoint) : ℝ :=
  ∫ point : BasePoint,
    p286CenteredCompactScalarWindow center point *
      p286JointYangMillsActionDefect source current point

theorem p286CenteredCompactActionDefect_nonnegative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (center : BasePoint) :
    0 ≤ p286CenteredCompactActionDefect source current center := by
  unfold p286CenteredCompactActionDefect
  apply integral_nonneg
  intro point
  exact mul_nonneg
    (p286CenteredCompactScalarWindow_nonnegative center point)
    (p286JointYangMillsActionDefect_nonnegative source current point)

theorem p286CenteredCompactActionDefect_pos_of_center_euler_ne_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (centerNonzero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current center ≠
        0) :
    0 < p286CenteredCompactActionDefect source current center := by
  let integrand := fun point : BasePoint =>
    p286CenteredCompactScalarWindow center point *
      p286JointYangMillsActionDefect source current point
  have integrandContinuous : Continuous integrand :=
    (p286CenteredCompactScalarWindow_contDiff center).continuous.mul
      (p286JointYangMillsActionDefect_continuous source current smooth
        nondegenerate)
  have integrandCompact : HasCompactSupport integrand :=
    (p286CenteredCompactScalarWindow_hasCompactSupport center).mul_right
  have integrandNonnegative : 0 ≤ integrand := by
    intro point
    exact mul_nonneg
      (p286CenteredCompactScalarWindow_nonnegative center point)
      (p286JointYangMillsActionDefect_nonnegative source current point)
  have centerDefectPositive :
      0 < p286JointYangMillsActionDefect source current center := by
    have defectNonnegative :=
      p286JointYangMillsActionDefect_nonnegative source current center
    have defectNonzero :
        p286JointYangMillsActionDefect source current center ≠ 0 := by
      intro defectZero
      exact centerNonzero
        ((p286JointYangMillsActionDefect_eq_zero_iff source current center).mp
          defectZero)
    exact lt_of_le_of_ne defectNonnegative defectNonzero.symm
  have integrandCenterNonzero : integrand center ≠ 0 := by
    simp [integrand, centerDefectPositive.ne']
  exact integrandContinuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    integrandCompact integrandNonnegative integrandCenterNonzero

/-! ## Exact finite descent in every translated window -/

def p286CenteredCompactNegativeGradientFirstCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  ∫ point : BasePoint,
    holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
      current
      (p286CenteredCompactNegativeGradientVariation source current smooth
        nondegenerate center)
      point

theorem p286CenteredCompactNegativeGradientFirstCoefficient_eq_neg_defect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    p286CenteredCompactNegativeGradientFirstCoefficient source current smooth
        nondegenerate center =
      -p286CenteredCompactActionDefect source current center := by
  rw [p286CenteredCompactNegativeGradientFirstCoefficient,
    holonomicFormNativeP286GaugeConnectionFirstVariation_integral_eq_w13
      source current smooth nondegenerate
      (p286CenteredCompactNegativeGradientVariation source current smooth
        nondegenerate center)]
  rw [show (fun point : BasePoint =>
      p286GaugeOneFormThreeFormWedgeCoefficient
        (p286CenteredCompactNegativeGradientVariation source current smooth
          nondegenerate center point)
        (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point)) =
      fun point =>
        -(p286CenteredCompactScalarWindow center point *
          p286JointYangMillsActionDefect source current point) by
    funext point
    change
      p286GaugeOneFormThreeFormWedgeCoefficient
          ((-p286CenteredCompactScalarWindow center point) •
            p286JointYangMillsActionGradient source current point)
          (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point) =
        _
    rw [p286GaugeOneFormThreeFormWedgeCoefficient_smul_left,
      p286JointYangMillsActionGradient_pairing_euler]
    ring]
  rw [integral_neg]
  rfl

def p286CenteredCompactNegativeGradientSecondCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  ∫ point : BasePoint,
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0
      current
      (p286CenteredCompactNegativeGradientVariation source current smooth
        nondegenerate center)
      point

/-- The safe parameter is computed from the current translated defect and
the exact quadratic second coefficient. -/
def p286CenteredCompactNegativeGradientStepSize
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  p286CenteredCompactActionDefect source current center /
    (2 * (1 +
      |p286CenteredCompactNegativeGradientSecondCoefficient source current
        smooth nondegenerate center|))

/-- Primitive connection stage generated in the selected material window. -/
def p286CenteredCompactNegativeGradientNext
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate current
    (p286CenteredCompactNegativeGradientVariation source current smooth
      nondegenerate center)
    (p286CenteredCompactNegativeGradientStepSize source current smooth
      nondegenerate center)

theorem p286CenteredCompactNegativeGradientNext_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    (p286CenteredCompactNegativeGradientNext source current smooth
      nondegenerate center).Smooth := by
  exact varyP286GaugeConnectionCoordinate_smooth_of_contDiff current smooth
    (p286CenteredCompactNegativeGradientVariation source current smooth
      nondegenerate center)
    (p286CenteredCompactNegativeGradientVariation source current smooth
      nondegenerate center).smooth
    (p286CenteredCompactNegativeGradientStepSize source current smooth
      nondegenerate center)

theorem p286CenteredCompactNegativeGradientNext_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    (p286CenteredCompactNegativeGradientNext source current smooth
      nondegenerate center).Nondegenerate := by
  intro point
  change Matrix.det (current.coframe point) ≠ 0
  exact nondegenerate point

theorem p286CenteredCompactNegativeGradient_relativeAction_nonpositive
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    p286CompactConnectionRelativeAction source current
        (p286CenteredCompactNegativeGradientVariation source current smooth
          nondegenerate center)
        (p286CenteredCompactNegativeGradientStepSize source current smooth
          nondegenerate center) ≤ 0 := by
  rw [p286CompactConnectionRelativeAction_quadratic source current smooth
    nondegenerate]
  change
    p286CenteredCompactNegativeGradientStepSize source current smooth
          nondegenerate center *
        p286CenteredCompactNegativeGradientFirstCoefficient source current
          smooth nondegenerate center +
      p286CenteredCompactNegativeGradientStepSize source current smooth
            nondegenerate center ^ 2 *
        p286CenteredCompactNegativeGradientSecondCoefficient source current
          smooth nondegenerate center ≤ 0
  rw [p286CenteredCompactNegativeGradientFirstCoefficient_eq_neg_defect]
  unfold p286CenteredCompactNegativeGradientStepSize
  exact p286QuadraticNegativeDefectSafeStep_nonpositive
    (p286CenteredCompactActionDefect source current center)
    (p286CenteredCompactNegativeGradientSecondCoefficient source current
      smooth nondegenerate center)
    (p286CenteredCompactActionDefect_nonnegative source current center)

theorem p286CenteredCompactNegativeGradient_relativeAction_strict
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (defectPositive :
      0 < p286CenteredCompactActionDefect source current center) :
    p286CompactConnectionRelativeAction source current
        (p286CenteredCompactNegativeGradientVariation source current smooth
          nondegenerate center)
        (p286CenteredCompactNegativeGradientStepSize source current smooth
          nondegenerate center) < 0 := by
  rw [p286CompactConnectionRelativeAction_quadratic source current smooth
    nondegenerate]
  change
    p286CenteredCompactNegativeGradientStepSize source current smooth
          nondegenerate center *
        p286CenteredCompactNegativeGradientFirstCoefficient source current
          smooth nondegenerate center +
      p286CenteredCompactNegativeGradientStepSize source current smooth
            nondegenerate center ^ 2 *
        p286CenteredCompactNegativeGradientSecondCoefficient source current
          smooth nondegenerate center < 0
  rw [p286CenteredCompactNegativeGradientFirstCoefficient_eq_neg_defect]
  unfold p286CenteredCompactNegativeGradientStepSize
  exact p286QuadraticNegativeDefectSafeStep_strict
    (p286CenteredCompactActionDefect source current center)
    (p286CenteredCompactNegativeGradientSecondCoefficient source current
      smooth nondegenerate center) defectPositive

theorem
    p286CenteredCompactNegativeGradient_relativeAction_strict_of_center_euler_ne_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (centerNonzero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current center ≠
        0) :
    p286CompactConnectionRelativeAction source current
        (p286CenteredCompactNegativeGradientVariation source current smooth
          nondegenerate center)
        (p286CenteredCompactNegativeGradientStepSize source current smooth
          nondegenerate center) < 0 :=
  p286CenteredCompactNegativeGradient_relativeAction_strict source current
    smooth nondegenerate center
    (p286CenteredCompactActionDefect_pos_of_center_euler_ne_zero source current
      smooth nondegenerate center centerNonzero)

/-! ## Dependency-ordered A/F/B completion -/

/-- After the strictly controlled primitive A-stage, curvature is recomputed
from the changed connection and the constitutive B-stage is installed. -/
def p286CenteredCompactJointYangMillsNext
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout source
    (p286CenteredCompactNegativeGradientNext source current smooth
      nondegenerate center)

theorem p286CenteredCompactJointYangMillsNext_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    (p286CenteredCompactJointYangMillsNext source current smooth nondegenerate
      center).Smooth := by
  exact formNativeP286GaugeConstitutiveReadout_smooth source _
    (p286CenteredCompactNegativeGradientNext_smooth source current smooth
      nondegenerate center)
    (p286CenteredCompactNegativeGradientNext_nondegenerate source current
      smooth nondegenerate center)

theorem p286CenteredCompactJointYangMillsNext_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    (p286CenteredCompactJointYangMillsNext source current smooth nondegenerate
      center).Nondegenerate := by
  exact formNativeP286GaugeConstitutiveReadout_nondegenerate source _
    (p286CenteredCompactNegativeGradientNext_nondegenerate source current
      smooth nondegenerate center)

theorem p286CenteredCompactJointYangMillsNext_auxiliaryPointwiseEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source
      (p286CenteredCompactJointYangMillsNext source current smooth
        nondegenerate center) := by
  exact formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation
    source _
    (p286CenteredCompactNegativeGradientNext_nondegenerate source current
      smooth nondegenerate center)

/-- A nonzero connection residual at the activated center forces an actual
changed joint next.  The proof uses the strict primitive relative-action law,
so this is generated progress rather than inequality bookkeeping. -/
theorem p286CenteredCompactJointYangMillsNext_ne_self_of_center_euler_ne_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (centerNonzero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current center ≠
        0) :
    p286CenteredCompactJointYangMillsNext source current smooth nondegenerate
        center ≠
      current := by
  intro jointFixed
  have connectionEq :
      (p286CenteredCompactNegativeGradientNext source current smooth
          nondegenerate center).gaugeConnection = current.gaugeConnection := by
    have projected :=
      congrArg StageNineHolonomicConfiguration.gaugeConnection jointFixed
    change
      (p286CenteredCompactNegativeGradientNext source current smooth
          nondegenerate center).gaugeConnection = current.gaugeConnection
        at projected
    exact projected
  have primitiveFixed :
      p286CenteredCompactNegativeGradientNext source current smooth
          nondegenerate center =
        current := by
    apply StageNineHolonomicConfiguration.ext <;> try rfl
    exact connectionEq
  have relativeActionZero :
      p286CompactConnectionRelativeAction source current
          (p286CenteredCompactNegativeGradientVariation source current smooth
            nondegenerate center)
          (p286CenteredCompactNegativeGradientStepSize source current smooth
            nondegenerate center) = 0 := by
    unfold p286CompactConnectionRelativeAction
    change
      (∫ point : BasePoint,
        sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
            (toContinuumPointField
              (p286CenteredCompactNegativeGradientNext source current smooth
                nondegenerate center) point) -
          sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
            (toContinuumPointField current point)) = 0
    rw [primitiveFixed]
    simp
  exact
    (ne_of_lt
      (p286CenteredCompactNegativeGradient_relativeAction_strict_of_center_euler_ne_zero
        source current smooth nondegenerate center centerNonzero))
      relativeActionZero

/-- If the algebraic row is not settled, constitutive recomputation changes
the current for every centered activation. -/
theorem p286CenteredCompactJointYangMillsNext_ne_self_of_not_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (auxiliaryNot :
      ¬ FormNativeP286GaugeAuxiliaryPointwiseEquation source current)
    (center : BasePoint) :
    p286CenteredCompactJointYangMillsNext source current smooth nondegenerate
        center ≠
      current := by
  intro fixed
  have nextAuxiliary :=
    p286CenteredCompactJointYangMillsNext_auxiliaryPointwiseEquation source
      current smooth nondegenerate center
  rw [fixed] at nextAuxiliary
  exact auxiliaryNot nextAuxiliary

/-! ## Joint conservativity -/

/-- No all-point residual can hide from the translated material windows.
This is the exact entropy/defect rigidity law for the complete connection
Euler field. -/
theorem p286CenteredCompactActionDefect_all_zero_iff_eulerThreeForm_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (∀ center : BasePoint,
        p286CenteredCompactActionDefect source current center = 0) ↔
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current = 0 := by
  constructor
  · intro allZero
    funext point
    by_contra pointNonzero
    have positive :=
      p286CenteredCompactActionDefect_pos_of_center_euler_ne_zero source
        current smooth nondegenerate point pointNonzero
    exact (ne_of_gt positive) (allZero point)
  · intro eulerZero center
    unfold p286CenteredCompactActionDefect
    have eachZero : ∀ point : BasePoint,
        p286JointYangMillsActionDefect source current point = 0 := by
      intro point
      exact
        (p286JointYangMillsActionDefect_eq_zero_iff source current point).2
          (congrFun eulerZero point)
    simp_rw [eachZero]
    simp

theorem p286CenteredCompactActionDefect_all_zero_iff_connectionPointwiseEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (∀ center : BasePoint,
        p286CenteredCompactActionDefect source current center = 0) ↔
      FormNativeP286GaugeConnectionPointwiseEquation source current :=
  (p286CenteredCompactActionDefect_all_zero_iff_eulerThreeForm_zero source
    current smooth nondegenerate).trans
      (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_pointwiseEquation
        source current)

/-- Normal-form theorem for the finite centered dynamics.  Every centered
next is the current exactly when the current satisfies both P286 master rows.
The backward implication uses strict relative-action descent to rule out a
hidden residual in any translated window. -/
theorem p286CenteredCompactJointYangMillsNext_all_eq_self_iff_masterEquations
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (∀ center : BasePoint,
        p286CenteredCompactJointYangMillsNext source current smooth
            nondegenerate center =
          current) ↔
      FormNativeP286GaugeAuxiliaryPointwiseEquation source current ∧
        FormNativeP286GaugeConnectionPointwiseEquation source current := by
  constructor
  · intro allFixed
    have auxiliaryNext :=
      p286CenteredCompactJointYangMillsNext_auxiliaryPointwiseEquation source
        current smooth nondegenerate 0
    have auxiliary :
        FormNativeP286GaugeAuxiliaryPointwiseEquation source current := by
      rw [allFixed 0] at auxiliaryNext
      exact auxiliaryNext
    have allDefectsZero : ∀ center : BasePoint,
        p286CenteredCompactActionDefect source current center = 0 := by
      intro center
      by_contra defectNonzero
      have defectPositive :
          0 < p286CenteredCompactActionDefect source current center :=
        lt_of_le_of_ne
          (p286CenteredCompactActionDefect_nonnegative source current center)
          (Ne.symm defectNonzero)
      have strict :=
        p286CenteredCompactNegativeGradient_relativeAction_strict source
          current smooth nondegenerate center defectPositive
      have jointFixed := allFixed center
      have connectionEq :
          (p286CenteredCompactNegativeGradientNext source current smooth
              nondegenerate center).gaugeConnection =
            current.gaugeConnection := by
        have projected :=
          congrArg StageNineHolonomicConfiguration.gaugeConnection jointFixed
        change
          (p286CenteredCompactNegativeGradientNext source current smooth
              nondegenerate center).gaugeConnection =
            current.gaugeConnection at projected
        exact projected
      have primitiveFixed :
          p286CenteredCompactNegativeGradientNext source current smooth
              nondegenerate center =
            current := by
        apply StageNineHolonomicConfiguration.ext <;> try rfl
        exact connectionEq
      have relativeActionZero :
          p286CompactConnectionRelativeAction source current
              (p286CenteredCompactNegativeGradientVariation source current
                smooth nondegenerate center)
              (p286CenteredCompactNegativeGradientStepSize source current
                smooth nondegenerate center) = 0 := by
        unfold p286CompactConnectionRelativeAction
        change
          (∫ point : BasePoint,
            sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
                (toContinuumPointField
                  (p286CenteredCompactNegativeGradientNext source current
                    smooth nondegenerate center) point) -
              sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
                (toContinuumPointField current point)) = 0
        rw [primitiveFixed]
        simp
      exact (ne_of_lt strict) relativeActionZero
    exact
      ⟨auxiliary,
        (p286CenteredCompactActionDefect_all_zero_iff_connectionPointwiseEquation
          source current smooth nondegenerate).1 allDefectsZero⟩
  · rintro ⟨auxiliary, connection⟩ center
    have eulerZero :
        holonomicFormNativeP286GaugeEulerThreeForm source 0 current = 0 :=
      (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_pointwiseEquation
        source current).2 connection
    have defectZero :
        p286CenteredCompactActionDefect source current center = 0 :=
      (p286CenteredCompactActionDefect_all_zero_iff_eulerThreeForm_zero source
        current smooth nondegenerate).2 eulerZero center
    have stepZero :
        p286CenteredCompactNegativeGradientStepSize source current smooth
            nondegenerate center = 0 := by
      unfold p286CenteredCompactNegativeGradientStepSize
      rw [defectZero]
      simp
    unfold p286CenteredCompactJointYangMillsNext
      p286CenteredCompactNegativeGradientNext
    rw [stepZero, varyP286GaugeConnectionCoordinate_zero]
    exact
      (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout source
        current nondegenerate).1 auxiliary |>.symm

/-! ## Exact SafeFinal entropy rigidity -/

private abbrev SafeSource : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev SafeFinal : StageNineHolonomicConfiguration :=
  SafeFinalClassicalWorldCandidateActual

/-- The translated entropy family is jointly conservative on the exact
configuration carried by the first-gravity root occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeFinalP286CenteredCompactActionDefect_all_zero_iff_connectionPointwiseEquation :
    (∀ center : BasePoint,
        p286CenteredCompactActionDefect SafeSource SafeFinal center = 0) ↔
      FormNativeP286GaugeConnectionPointwiseEquation SafeSource SafeFinal :=
  p286CenteredCompactActionDefect_all_zero_iff_connectionPointwiseEquation
    SafeSource SafeFinal safeFinalClassicalWorldCandidateActual_smooth
    safeFinalClassicalWorldCandidateActual_nondegenerate

/-- Entropy characterization of the exact SafeFinal P286 normal form.  The
generated global A/F/B step is fixed exactly when the algebraic row is
settled and every translated material window sees zero connection defect. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeFinalP286JointYangMillsEulerStep_eq_self_iff_auxiliary_and_centeredEntropy_zero :
    p286JointYangMillsEulerStep SafeSource SafeFinal = SafeFinal ↔
      FormNativeP286GaugeAuxiliaryPointwiseEquation SafeSource SafeFinal ∧
        ∀ center : BasePoint,
          p286CenteredCompactActionDefect SafeSource SafeFinal center = 0 := by
  rw [p286JointYangMillsEulerStep_eq_self_iff_masterEquations SafeSource
    SafeFinal safeFinalClassicalWorldCandidateActual_nondegenerate]
  exact and_congr Iff.rfl
    fixedP506L0CartanECConstraintCauchySafeFinalP286CenteredCompactActionDefect_all_zero_iff_connectionPointwiseEquation.symm

/-- Exact total-lock form: the entire centered finite-descent family is fixed
precisely when the two authoritative P286 residual rows of the root-owned
SafeFinal occurrence are settled. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeFinalP286CenteredCompactJointYangMillsNext_all_eq_self_iff_p286ResidualRows_zero :
    (∀ center : BasePoint,
        p286CenteredCompactJointYangMillsNext SafeSource SafeFinal
            safeFinalClassicalWorldCandidateActual_smooth
            safeFinalClassicalWorldCandidateActual_nondegenerate center =
          SafeFinal) ↔
      ∀ point : BasePoint,
        (diracDualFormNativePointwiseJointResidual SafeSource SafeFinal point
            ).p286GaugeAuxiliary = 0 ∧
          (diracDualFormNativePointwiseJointResidual SafeSource SafeFinal point
            ).p286GaugeConnection = 0 := by
  exact
    (p286CenteredCompactJointYangMillsNext_all_eq_self_iff_masterEquations
      SafeSource SafeFinal safeFinalClassicalWorldCandidateActual_smooth
      safeFinalClassicalWorldCandidateActual_nondegenerate).trans
      ((p286JointYangMillsEulerStep_eq_self_iff_masterEquations SafeSource
        SafeFinal safeFinalClassicalWorldCandidateActual_nondegenerate).symm.trans
        fixedP506L0CartanECConstraintCauchySafeFinalP286GlobalYangMillsEulerActual_eq_safeFinal_iff_p286ResidualRows_zero)

end
end StageNineP286SourceNativeCenteredCompactEntropyDescent
end PhysicsCore
end SaturationMonoid
