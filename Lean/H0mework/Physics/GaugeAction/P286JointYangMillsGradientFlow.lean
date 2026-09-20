import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerCore

/-!
# Source-native joint P286 Yang--Mills gradient flow

The complete P286 connection Euler three-form already is the pointwise
mother-action covector.  Two existing finite-dimensional equivalences turn it
canonically into a P286 connection one-form:

```text
Euler three-form
  -> W13 action dual
  -> positive P286 pairing gradient.
```

This module uses that generated gradient as an actual global connection
update and then recomputes curvature and the constitutive auxiliary.  No
residual, support coordinate, desired connection, target zero, step selector,
or stationarity receipt is accepted by the constructor.  The unit negative
Euler step is fixed by the action-coordinate grammar.

The main theorem says that, on a nondegenerate current, fixed points of this
joint A/F/B evolution are exactly the simultaneous P286 auxiliary and
connection pointwise equations.  Thus the dynamics has no dormant B-only
mouth: its canonical states are precisely the Yang--Mills states.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286JointYangMillsGradientFlow

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugePointwiseEquation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance jointYangMillsFlowP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective

local instance jointYangMillsFlowP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Generated action gradient and exact defect -/

/-- Pointwise connection gradient obtained from the complete mother-action
covector by the canonical W13 and positive-pairing equivalences. -/
def p286JointYangMillsActionGradient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeOneForm :=
  p286GaugeOneFormPairingEquiv.symm
    (p286GaugeThreeFormWedgeLinearDual
      (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point))

/-- Finite pointwise squared defect of the action gradient. -/
def p286JointYangMillsActionDefect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : ℝ :=
  ∑ direction : LorentzianIndex,
    p286CoordinateLiePairing
      (p286JointYangMillsActionGradient source current point direction)
      (p286JointYangMillsActionGradient source current point direction)

theorem p286JointYangMillsActionGradient_eq_zero_iff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286JointYangMillsActionGradient source current point = 0 ↔
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current point = 0 := by
  unfold p286JointYangMillsActionGradient
  constructor
  · intro gradientZero
    have dualZero :
        p286GaugeThreeFormWedgeLinearDual
            (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point) =
          0 := by
      apply p286GaugeOneFormPairingEquiv.symm.injective
      simpa using gradientZero
    exact
      (p286GaugeThreeFormWedgeLinearDual_eq_zero_iff
        (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point)).mp
        dualZero
  · intro eulerZero
    rw [eulerZero]
    change p286GaugeOneFormPairingEquiv.symm
        (p286GaugeThreeFormWedgeLinearDual 0) = 0
    have dualZero : p286GaugeThreeFormWedgeLinearDual 0 = 0 :=
      (p286GaugeThreeFormWedgeLinearDual_eq_zero_iff 0).mpr rfl
    rw [dualZero, map_zero]

theorem p286JointYangMillsActionDefect_nonnegative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    0 ≤ p286JointYangMillsActionDefect source current point := by
  unfold p286JointYangMillsActionDefect
  apply Finset.sum_nonneg
  intro direction _
  exact p286CoordinateLiePairing_self_nonnegative _

theorem p286JointYangMillsActionDefect_eq_zero_iff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286JointYangMillsActionDefect source current point = 0 ↔
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current point = 0 := by
  rw [← p286JointYangMillsActionGradient_eq_zero_iff source current point]
  constructor
  · intro defectZero
    have eachZero : ∀ direction ∈ (Finset.univ : Finset LorentzianIndex),
        p286CoordinateLiePairing
            (p286JointYangMillsActionGradient source current point direction)
            (p286JointYangMillsActionGradient source current point direction) =
          0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun direction _ => p286CoordinateLiePairing_self_nonnegative
          (p286JointYangMillsActionGradient source current point direction))).mp
        defectZero
    funext direction
    exact
      (p286CoordinateLiePairing_self_eq_zero_iff
        (p286JointYangMillsActionGradient source current point direction)).mp
        (eachZero direction (Finset.mem_univ _))
  · intro gradientZero
    unfold p286JointYangMillsActionDefect
    rw [gradientZero]
    simp

/-! ## Exact infinitesimal dissipation identity -/

/-- The action covector evaluated on its pairing gradient is exactly the
finite positive defect. -/
theorem p286JointYangMillsActionGradient_pairing_euler
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (p286JointYangMillsActionGradient source current point)
        (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point) =
      p286JointYangMillsActionDefect source current point := by
  unfold p286JointYangMillsActionGradient
    p286JointYangMillsActionDefect
  change
    p286GaugeThreeFormWedgeLinearDual
          (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point)
          (p286GaugeOneFormPairingEquiv.symm
            (p286GaugeThreeFormWedgeLinearDual
              (holonomicFormNativeP286GaugeEulerThreeForm source 0 current
                point))) = _
  rw [← p286GaugeOneFormPairingEquiv.apply_symm_apply
    (p286GaugeThreeFormWedgeLinearDual
      (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point))]
  rw [p286GaugeOneFormPairingEquiv_apply,
    p286GaugeOneFormPairingDual_apply]
  simp only [← p286GaugeOneFormPairingEquiv_apply,
    LinearEquiv.symm_apply_apply]
  rfl

/-- Exact pointwise dissipation: the action covector on the generated
negative-gradient direction is minus the nonnegative defect. -/
theorem p286JointYangMillsNegativeGradient_pairing_euler
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (-p286JointYangMillsActionGradient source current point)
        (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point) =
      -p286JointYangMillsActionDefect source current point := by
  rw [show -p286JointYangMillsActionGradient source current point =
      (-1 : ℝ) • p286JointYangMillsActionGradient source current point by
    simp]
  rw [p286GaugeOneFormThreeFormWedgeCoefficient_smul_left,
    p286JointYangMillsActionGradient_pairing_euler]
  ring

/-- Dissipation rigidity: the generated direction has zero action rate
exactly at a Yang--Mills state. -/
theorem p286JointYangMillsNegativeGradient_pairing_euler_eq_zero_iff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286GaugeOneFormThreeFormWedgeCoefficient
          (-p286JointYangMillsActionGradient source current point)
          (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point) =
        0 ↔
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current point = 0 := by
  rw [p286JointYangMillsNegativeGradient_pairing_euler,
    neg_eq_zero,
    p286JointYangMillsActionDefect_eq_zero_iff]

/-- Away from the canonical state the infinitesimal action rate is strictly
negative.  This is an exact local law, not yet a finite-step descent theorem.
-/
theorem p286JointYangMillsNegativeGradient_pairing_euler_strict
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nonzero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0 current point ≠ 0) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (-p286JointYangMillsActionGradient source current point)
        (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point) <
      0 := by
  rw [p286JointYangMillsNegativeGradient_pairing_euler]
  apply neg_lt_zero.mpr
  have nonnegative :=
    p286JointYangMillsActionDefect_nonnegative source current point
  have defectNonzero :
      p286JointYangMillsActionDefect source current point ≠ 0 := by
    intro defectZero
    exact nonzero
      ((p286JointYangMillsActionDefect_eq_zero_iff source current point).mp
        defectZero)
  exact lt_of_le_of_ne nonnegative defectNonzero.symm

/-! ## Canonical all-point A/F/B evolution -/

/-- Negative action-gradient Euler step on the primitive connection. -/
def p286JointYangMillsConnectionEulerStep
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate current
    (fun point => -p286JointYangMillsActionGradient source current point) 1

/-- Joint source-native step: update A, recompute F(A), then install the exact
constitutive B(A). -/
def p286JointYangMillsEulerStep
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout source
    (p286JointYangMillsConnectionEulerStep source current)

@[simp] theorem p286JointYangMillsEulerStep_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (p286JointYangMillsEulerStep source current).coframe = current.coframe :=
  rfl

theorem p286JointYangMillsEulerStep_connectionCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        (p286JointYangMillsEulerStep source current) point =
      holonomicP286GaugeConnectionCoordinate current point -
        p286JointYangMillsActionGradient source current point := by
  change
    holonomicP286GaugeConnectionCoordinate
        (p286JointYangMillsConnectionEulerStep source current) point = _
  rw [p286JointYangMillsConnectionEulerStep,
    holonomicP286GaugeConnectionCoordinate_vary]
  simp [sub_eq_add_neg]

private theorem p286JointYangMillsConnectionEulerStep_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (p286JointYangMillsConnectionEulerStep source current).Nondegenerate := by
  intro point
  change Matrix.det (current.coframe point) ≠ 0
  exact nondegenerate point

/-- Every generated next state is globally on the algebraic auxiliary shell.
-/
theorem p286JointYangMillsEulerStep_auxiliaryPointwiseEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source
      (p286JointYangMillsEulerStep source current) := by
  exact formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation
    source (p286JointYangMillsConnectionEulerStep source current)
    (p286JointYangMillsConnectionEulerStep_nondegenerate source current
      nondegenerate)

theorem p286JointYangMillsEulerStep_gaugeConnection_eq_iff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (p286JointYangMillsEulerStep source current).gaugeConnection =
        current.gaugeConnection ↔
      FormNativeP286GaugeConnectionPointwiseEquation source current := by
  constructor
  · intro connectionEq point
    apply
      (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current
        source 0 current point).mp
    apply
      (p286JointYangMillsActionGradient_eq_zero_iff source current point).mp
    have coordinateEq :
        holonomicP286GaugeConnectionCoordinate
            (p286JointYangMillsEulerStep source current) point =
          holonomicP286GaugeConnectionCoordinate current point := by
      funext direction
      exact congrArg p286CoordinateEquiv
        (congrFun (congrFun connectionEq point) direction)
    rw [p286JointYangMillsEulerStep_connectionCoordinate] at coordinateEq
    exact sub_eq_self.mp coordinateEq
  · intro connectionEquation
    funext point direction
    apply p286CoordinateEquiv.injective
    have eulerZero :=
      (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current
        source 0 current point).mpr (connectionEquation point)
    have gradientZero :=
      (p286JointYangMillsActionGradient_eq_zero_iff source current point).mpr
        eulerZero
    have coordinateEq :=
      p286JointYangMillsEulerStep_connectionCoordinate source current point
    rw [gradientZero, sub_zero] at coordinateEq
    exact congrFun coordinateEq direction

/-- Fixed points of the generated all-point A/F/B dynamics are exactly the
simultaneous P286 master equations. -/
theorem p286JointYangMillsEulerStep_eq_self_iff_masterEquations
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    p286JointYangMillsEulerStep source current = current ↔
      FormNativeP286GaugeAuxiliaryPointwiseEquation source current ∧
        FormNativeP286GaugeConnectionPointwiseEquation source current := by
  constructor
  · intro fixed
    have generatedAuxiliary :
        FormNativeP286GaugeAuxiliaryPointwiseEquation source
          (p286JointYangMillsEulerStep source current) :=
      p286JointYangMillsEulerStep_auxiliaryPointwiseEquation source current
        nondegenerate
    have connectionEq :
        (p286JointYangMillsEulerStep source current).gaugeConnection =
          current.gaugeConnection :=
      congrArg StageNineHolonomicConfiguration.gaugeConnection fixed
    exact
      ⟨fixed ▸ generatedAuxiliary,
        (p286JointYangMillsEulerStep_gaugeConnection_eq_iff source current).mp
          connectionEq⟩
  · rintro ⟨auxiliaryEquation, connectionEquation⟩
    have connectionEq :
        (p286JointYangMillsEulerStep source current).gaugeConnection =
          current.gaugeConnection :=
      (p286JointYangMillsEulerStep_gaugeConnection_eq_iff source current).mpr
        connectionEquation
    have connectionStepEq :
        p286JointYangMillsConnectionEulerStep source current = current := by
      apply StageNineHolonomicConfiguration.ext <;> try rfl
      exact connectionEq
    rw [p286JointYangMillsEulerStep, connectionStepEq]
    exact
      (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout source
        current nondegenerate).mp auxiliaryEquation |>.symm

end
end StageNineP286JointYangMillsGradientFlow
end PhysicsCore
end SaturationMonoid
