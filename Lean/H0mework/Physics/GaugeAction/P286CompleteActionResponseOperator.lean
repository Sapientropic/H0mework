import H0mework.Physics.GaugeAction.CurrentP286CompleteActionResponseOperator
import H0mework.Physics.Constitutive.P286GaugeGeometricFirstVariation

/-!
# Form-native complete P286 action-response operator

The authoritative form-native connection equation is

```text
D_A B = J_charged.
```

This module solves that equation forward at the canonical contact.  The
source and current first generate the required exterior-derivative target

```text
dB = J_charged - [A,B],
```

and the fixed `3+1` coordinate grammar lifts the resulting three-form to one
canonical auxiliary first jet.  The three spatial contributions to the
`123` component use the unique equal-axis coefficient already generated from
`card (Fin 3)`.

The constructor accepts no residual, support coordinate, sign choice,
candidate derivative, target three-form, branch, equation witness, or
zero-fiber certificate.  Re-substitution below is producer soundness for the
same mother-action equation that generated the write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286CompleteActionResponseOperator

open ProofFreeRicherAnholonomicSource
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Canonical right inverse of the exterior first-jet map -/

/-- The action-required pure exterior-derivative channel at the current
canonical contact.  This is a direct rearrangement of `D_A B = J_charged`,
not a read of the joint residual carrier. -/
def formNativeCurrentP286RequiredExteriorDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : P286GaugeThreeForm :=
  formNativePhysicalChargedGaugeCurrentThreeForm source 0 0
      (toContinuumPointField current 0) -
    pointwiseP286GaugeTwoFormConnectionExteriorAction
      (holonomicP286GaugeConnectionCoordinate current 0)
      (holonomicP286GaugeAuxiliaryCoordinate current 0)

/-- Canonical `3+1` first jet of a P286 two-form whose exterior derivative is
the supplied three-form.  The time row carries the `012`, `013`, and `023`
coordinates; the `123` coordinate is distributed equally over the three
spatial axes. -/
def formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
    (target : P286GaugeThreeForm)
    (direction : LorentzianIndex) : P286GaugeTwoForm :=
  ![
    ![0, 0, 0, target 2, -target 1, target 0],
    ![0, 0, 0, canonicalP286EqualAxisCoefficient • target 3, 0, 0],
    ![0, 0, 0, 0, canonicalP286EqualAxisCoefficient • target 3, 0],
    ![0, 0, 0, 0, 0, canonicalP286EqualAxisCoefficient • target 3]
  ] direction

/-- The canonical derivative above is a right inverse of the literal
exterior-derivative map. -/
theorem
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_canonical
    (target : P286GaugeThreeForm) :
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
        (formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm target) =
      target := by
  funext triple
  fin_cases triple <;>
    simp [pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      orderedP286GaugeTwoFormComponent, threeFormFirst, threeFormSecond,
      threeFormThird, orientedLorentzBivectorBasisCoefficient, pairFirst,
      pairSecond, canonicalP286EqualAxisCoefficient_eq_one_third,
      Fin.sum_univ_six];
    module

/-- Linear spacetime realization of the canonical first jet. -/
def formNativeP286CanonicalAuxiliaryIncrement
    (target : P286GaugeThreeForm) : BasePoint →L[ℝ] P286GaugeTwoForm :=
  ∑ direction : LorentzianIndex,
    (localBaseCoordinate direction).smulRight
      (formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm target direction)

/-! ## Source/current-only action write -/

def formNativeCurrentP286CompleteResponseAuxiliaryCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  currentP286OriginAuxiliaryCoordinate current +
    formNativeP286CanonicalAuxiliaryIncrement
      (formNativeCurrentP286RequiredExteriorDerivative source current) point

def formNativeCurrentP286CompleteResponseAuxiliaryField
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    BasePoint → Fin 6 → P286LieBlockData :=
  fun point pair =>
    p286CoordinateEquiv.symm
      (formNativeCurrentP286CompleteResponseAuxiliaryCoordinate source current
        point pair)

/-- Canonical-contact form-native P286 action write.  Only the auxiliary
first jet changes; its value at the contact is retained. -/
def formNativeCurrentP286CompleteActionResponseOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    gaugeAuxiliary :=
      formNativeCurrentP286CompleteResponseAuxiliaryField source current }

@[simp] theorem
    formNativeCurrentP286CompleteActionResponseOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).coframe = current.coframe :=
  rfl

@[simp] theorem
    formNativeCurrentP286CompleteActionResponseOperator_gravityConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).gravityConnection = current.gravityConnection :=
  rfl

@[simp] theorem
    formNativeCurrentP286CompleteActionResponseOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).gravityAuxiliary = current.gravityAuxiliary :=
  rfl

@[simp] theorem
    formNativeCurrentP286CompleteActionResponseOperator_multiplier
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).gravitySimplicityMultiplier = current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem
    formNativeCurrentP286CompleteActionResponseOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem
    formNativeCurrentP286CompleteActionResponseOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).scalar = current.scalar :=
  rfl

@[simp] theorem
    formNativeCurrentP286CompleteActionResponseOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).matter = current.matter :=
  rfl

@[simp] theorem
    formNativeCurrentP286CompleteActionResponseOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).conjugateMatter = current.conjugateMatter :=
  rfl

theorem formNativeCurrentP286CompleteResponseAuxiliaryCoordinate_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    formNativeCurrentP286CompleteResponseAuxiliaryCoordinate source current 0 =
      currentP286OriginAuxiliaryCoordinate current := by
  simp [formNativeCurrentP286CompleteResponseAuxiliaryCoordinate]

theorem formNativeCurrentP286CompleteResponseAuxiliaryField_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    formNativeCurrentP286CompleteResponseAuxiliaryField source current 0 =
      current.gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  simp [formNativeCurrentP286CompleteResponseAuxiliaryField,
    formNativeCurrentP286CompleteResponseAuxiliaryCoordinate_origin,
    currentP286OriginAuxiliaryCoordinate]

theorem
    formNativeCurrentP286CompleteActionResponseOperator_gaugeAuxiliary_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).gaugeAuxiliary 0 = current.gaugeAuxiliary 0 :=
  formNativeCurrentP286CompleteResponseAuxiliaryField_origin source current

theorem
    formNativeCurrentP286CompleteActionResponseOperator_auxiliaryCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (formNativeCurrentP286CompleteActionResponseOperator source current)
        point =
      formNativeCurrentP286CompleteResponseAuxiliaryCoordinate source current
        point := by
  funext pair
  exact p286CoordinateEquiv.apply_symm_apply _

theorem formNativeCurrentP286CompleteActionResponseOperator_pointField_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    toContinuumPointField
        (formNativeCurrentP286CompleteActionResponseOperator source current) 0 =
      toContinuumPointField current 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact
      formNativeCurrentP286CompleteActionResponseOperator_gaugeAuxiliary_origin
        source current
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## Actual first jet and action equation -/

theorem
    formNativeCurrentP286CompleteActionResponseOperator_auxiliaryDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        (formNativeCurrentP286CompleteActionResponseOperator source current)
        point direction =
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
        (formNativeCurrentP286RequiredExteriorDerivative source current)
        direction := by
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate
        (formNativeCurrentP286CompleteActionResponseOperator source current) =
      fun point =>
        currentP286OriginAuxiliaryCoordinate current +
          formNativeP286CanonicalAuxiliaryIncrement
            (formNativeCurrentP286RequiredExteriorDerivative source current)
            point by
      funext point
      exact
        formNativeCurrentP286CompleteActionResponseOperator_auxiliaryCoordinate
          source current point]
  rw [fderiv_const_add]
  rw [(formNativeP286CanonicalAuxiliaryIncrement
    (formNativeCurrentP286RequiredExteriorDerivative source current)
    ).hasFDerivAt.fderiv]
  fin_cases direction <;>
    simp [formNativeP286CanonicalAuxiliaryIncrement,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      localBaseCoordinate, coordinateDirection, Fin.sum_univ_four]

theorem
    formNativeCurrentP286CompleteActionResponseOperator_auxiliaryDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        (formNativeCurrentP286CompleteActionResponseOperator source current)
        0 direction =
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
        (formNativeCurrentP286RequiredExteriorDerivative source current)
        direction :=
  formNativeCurrentP286CompleteActionResponseOperator_auxiliaryDerivative
    source current 0 direction

theorem
    formNativeCurrentP286CompleteActionResponseOperator_exteriorDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (formNativeCurrentP286CompleteActionResponseOperator source current)
        point =
      formNativeCurrentP286RequiredExteriorDerivative source current := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [show
    p286GaugeAuxiliaryDirectionalDerivative
        (formNativeCurrentP286CompleteActionResponseOperator source current)
        point =
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
        (formNativeCurrentP286RequiredExteriorDerivative source current) by
      funext direction
      exact
        formNativeCurrentP286CompleteActionResponseOperator_auxiliaryDerivative
          source current point direction]
  exact
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_canonical _

theorem
    formNativeCurrentP286CompleteActionResponseOperator_exteriorDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (formNativeCurrentP286CompleteActionResponseOperator source current) 0 =
      formNativeCurrentP286RequiredExteriorDerivative source current :=
  formNativeCurrentP286CompleteActionResponseOperator_exteriorDerivative
    source current 0

/-- Producer soundness for the authoritative form-native P286 connection
equation on the same output actual. -/
theorem
    formNativeCurrentP286CompleteActionResponseOperator_connectionEquation_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicFormNativeP286GaugeEulerThreeForm source 0
        (formNativeCurrentP286CompleteActionResponseOperator source current) 0 =
      0 := by
  rw [holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current]
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    formNativeCurrentP286CompleteActionResponseOperator_exteriorDerivative_origin]
  rw [formNativeCurrentP286CompleteActionResponseOperator_pointField_origin]
  rw [show
    holonomicP286GaugeConnectionCoordinate
        (formNativeCurrentP286CompleteActionResponseOperator source current) 0 =
      holonomicP286GaugeConnectionCoordinate current 0 by rfl]
  rw [formNativeCurrentP286CompleteActionResponseOperator_auxiliaryCoordinate,
    formNativeCurrentP286CompleteResponseAuxiliaryCoordinate_origin]
  change
    formNativeCurrentP286RequiredExteriorDerivative source current +
        pointwiseP286GaugeTwoFormConnectionExteriorAction
          (holonomicP286GaugeConnectionCoordinate current 0)
          (holonomicP286GaugeAuxiliaryCoordinate current 0) =
      formNativePhysicalChargedGaugeCurrentThreeForm source 0 0
        (toContinuumPointField current 0)
  unfold formNativeCurrentP286RequiredExteriorDerivative
  abel

/-! ## Regularity and faithful carrier transport -/

theorem formNativeCurrentP286CompleteResponseAuxiliaryCoordinate_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun point : BasePoint =>
      formNativeCurrentP286CompleteResponseAuxiliaryCoordinate source current
        point pair := by
  have summandSmooth (direction : LorentzianIndex) :
      ContDiff ℝ ∞ fun point : BasePoint =>
        point direction •
          formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
            (formNativeCurrentP286RequiredExteriorDerivative source current)
            direction pair := by
    simpa only [localBaseCoordinate_apply] using
      ((localBaseCoordinate direction).contDiff.smul_const
        (formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
          (formNativeCurrentP286RequiredExteriorDerivative source current)
          direction pair))
  have incrementSmooth : ContDiff ℝ ∞ fun point : BasePoint =>
      ∑ direction : LorentzianIndex,
        point direction •
          formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
            (formNativeCurrentP286RequiredExteriorDerivative source current)
            direction pair := by
    apply ContDiff.sum
    intro direction _
    exact summandSmooth direction
  change ContDiff ℝ ∞ fun point : BasePoint =>
    currentP286OriginAuxiliaryCoordinate current pair +
      ∑ direction : LorentzianIndex,
        point direction •
          formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
            (formNativeCurrentP286RequiredExteriorDerivative source current)
            direction pair
  exact contDiff_const.add incrementSmooth

theorem formNativeCurrentP286CompleteActionResponseOperator_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).Smooth := by
  rcases smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, _gaugeAuxiliary, scalar, matter, conjugate⟩
  refine ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
    gaugeConnection, ?_, scalar, matter, conjugate⟩
  intro pair
  change ContDiff ℝ ∞ fun point : BasePoint =>
    p286CoordinateEquiv
      (formNativeCurrentP286CompleteResponseAuxiliaryField source current
        point pair)
  rw [show
    (fun point : BasePoint =>
      p286CoordinateEquiv
        (formNativeCurrentP286CompleteResponseAuxiliaryField source current
          point pair)) =
      fun point =>
        formNativeCurrentP286CompleteResponseAuxiliaryCoordinate source current
          point pair by
      funext point
      exact p286CoordinateEquiv.apply_symm_apply _]
  exact formNativeCurrentP286CompleteResponseAuxiliaryCoordinate_contDiff
    source current pair

theorem formNativeCurrentP286CompleteActionResponseOperator_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (formNativeCurrentP286CompleteActionResponseOperator source current
      ).Nondegenerate := by
  intro point
  exact nondegenerate point

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286CompleteActionResponseOperator
