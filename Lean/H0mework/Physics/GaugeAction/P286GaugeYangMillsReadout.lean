import H0mework.Physics.Constitutive.P286GaugeConstitutiveElimination
import H0mework.Physics.Gauge.GaugeAuxiliaryIntegratedVariation
import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryVariation
import H0mework.Physics.GaugeAction.P286GaugePointwiseEquation

/-!
# Conditional form-native P286 Yang--Mills readout

This module substitutes the exact three-block auxiliary solution into the
already action-generated P286 connection equation.  The substitution is made
as one whole-field readout: only the primitive auxiliary field is replaced,
while the live coframe, primitive connection, curvature, charged fields, and
their exact source lineage are retained.

Consequently the Yang--Mills left-hand side differentiates the complete field

```text
x |-> K_(e(x))^-1 (F_A(x)).
```

It is not rewritten as `K_e^-1 (D_A F)`: such a rewrite would discard the
spatial variation of the live coframe Hodge.  The readout is branch-free and
adds no coupling or solution receipt.  Its equivalence with the two first-order
equations is conditional producer consistency, not a stationary-world
producer or an independent Cauchy constraint.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeYangMillsReadout

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugePointwiseEquation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/-! ## Branch-free whole-field substitution -/

/-- Whole-configuration readout obtained by replacing only the P286 auxiliary
field by the exact inverse-constitutive image of the actual curvature.  This
is not a source producer or a field-equation receipt. -/
def formNativeP286GaugeConstitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration where
  coframe := configuration.coframe
  gravityConnection := configuration.gravityConnection
  gravityAuxiliary := configuration.gravityAuxiliary
  gravitySimplicityMultiplier := configuration.gravitySimplicityMultiplier
  gaugeConnection := configuration.gaugeConnection
  gaugeAuxiliary := fun point =>
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings source)
      (configuration.coframe point)
      (holonomicGaugeCurvature configuration point)
  scalar := configuration.scalar
  matter := configuration.matter
  conjugateMatter := configuration.conjugateMatter

@[simp] theorem formNativeP286GaugeConstitutiveReadout_coframe
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (formNativeP286GaugeConstitutiveReadout source configuration).coframe =
      configuration.coframe := rfl

@[simp] theorem formNativeP286GaugeConstitutiveReadout_gravityConnection
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (formNativeP286GaugeConstitutiveReadout source
      configuration).gravityConnection = configuration.gravityConnection := rfl

@[simp] theorem formNativeP286GaugeConstitutiveReadout_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (formNativeP286GaugeConstitutiveReadout source
      configuration).gravityAuxiliary = configuration.gravityAuxiliary := rfl

@[simp] theorem formNativeP286GaugeConstitutiveReadout_gravitySimplicityMultiplier
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (formNativeP286GaugeConstitutiveReadout source
      configuration).gravitySimplicityMultiplier =
        configuration.gravitySimplicityMultiplier := rfl

@[simp] theorem holonomicGravityCurvature_formNativeP286GaugeConstitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (formNativeP286GaugeConstitutiveReadout source configuration) =
      holonomicGravityCurvature configuration := rfl

/-- The P286 constitutive refresh changes only the P286 auxiliary field, so
the complete algebraic gravity-auxiliary Euler residual is preserved at each
point. -/
@[simp] theorem
    formNativeGravityAuxiliaryEulerResidual_formNativeP286GaugeConstitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField
          (formNativeP286GaugeConstitutiveReadout source configuration) point) =
      formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField configuration point) :=
  rfl

@[simp] theorem formNativeP286GaugeConstitutiveReadout_gaugeConnection
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (formNativeP286GaugeConstitutiveReadout source
      configuration).gaugeConnection = configuration.gaugeConnection := rfl

@[simp] theorem formNativeP286GaugeConstitutiveReadout_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (formNativeP286GaugeConstitutiveReadout source
        configuration).gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (configuration.coframe point)
        (holonomicGaugeCurvature configuration point) := rfl

@[simp] theorem holonomicGaugeCurvature_formNativeP286GaugeConstitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGaugeCurvature
        (formNativeP286GaugeConstitutiveReadout source configuration) =
      holonomicGaugeCurvature configuration := rfl

theorem toContinuumPointField_formNativeP286GaugeConstitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    toContinuumPointField
        (formNativeP286GaugeConstitutiveReadout source configuration) point =
      withFormNativeP286GaugeAuxiliary
        (toContinuumPointField configuration point)
        (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          (configuration.coframe point)
          (holonomicGaugeCurvature configuration point)) :=
  rfl

@[simp] theorem
    formNativePhysicalChargedGaugeCurrentThreeForm_withP286Auxiliary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (auxiliary : FormNativeP286GaugeTwoForm) :
    formNativePhysicalChargedGaugeCurrentThreeForm source chart point
        (withFormNativeP286GaugeAuxiliary field auxiliary) =
      formNativePhysicalChargedGaugeCurrentThreeForm source chart point
        field :=
  rfl

@[simp] theorem
    formNativePhysicalChargedGaugeCurrentThreeForm_constitutiveReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    formNativePhysicalChargedGaugeCurrentThreeForm source 0 point
        (toContinuumPointField
          (formNativeP286GaugeConstitutiveReadout source configuration) point) =
      formNativePhysicalChargedGaugeCurrentThreeForm source 0 point
        (toContinuumPointField configuration point) := by
  rw [toContinuumPointField_formNativeP286GaugeConstitutiveReadout]
  exact
    formNativePhysicalChargedGaugeCurrentThreeForm_withP286Auxiliary
      source 0 point (toContinuumPointField configuration point) _

theorem formNativeP286GaugeConstitutiveReadout_nondegenerate
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (formNativeP286GaugeConstitutiveReadout source
      configuration).Nondegenerate :=
  nondegenerate

/-! ## Exact auxiliary shell and fixed points -/

theorem formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source
      (formNativeP286GaugeConstitutiveReadout source configuration) := by
  intro point
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField
        (formNativeP286GaugeConstitutiveReadout source configuration) point)
      (nondegenerate point)).2
  rfl

theorem formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source configuration ↔
      configuration =
        formNativeP286GaugeConstitutiveReadout source configuration := by
  constructor
  · intro equation
    apply StageNineHolonomicConfiguration.ext <;> try rfl
    funext point
    exact
      (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
        (sourceGeneratedUnifiedCouplings source)
        (toContinuumPointField configuration point)
        (nondegenerate point)).1 (equation point)
  · intro fixed
    exact fixed.symm ▸
      formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation source
        configuration nondegenerate

/-! ## Conditional second-order readout -/

/-- The Yang--Mills equation obtained by evaluating the already generated
connection equation on the complete inverse-constitutive auxiliary field.
The covariant derivative therefore sees the full `x |-> K_(e(x))^-1 F_A(x)`
field, including live-coframe variation. -/
def FormNativeP286GaugeYangMillsPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  FormNativeP286GaugeConnectionPointwiseEquation source
    (formNativeP286GaugeConstitutiveReadout source configuration)

theorem formNativeP286GaugeYangMillsPointwiseEquation_iff_wholeField
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    FormNativeP286GaugeYangMillsPointwiseEquation source configuration ↔
      ∀ point : BasePoint,
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
            (formNativeP286GaugeConstitutiveReadout source configuration)
            point =
          formNativePhysicalChargedGaugeCurrentThreeForm source 0 point
            (toContinuumPointField configuration point) := by
  unfold FormNativeP286GaugeYangMillsPointwiseEquation
    FormNativeP286GaugeConnectionPointwiseEquation
  constructor <;> intro equation point
  · simpa using equation point
  · simpa using equation point

theorem
    formNativeP286GaugeConnectionPointwiseEquation_iff_yangMills_of_auxiliary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (auxiliaryEquation :
      FormNativeP286GaugeAuxiliaryPointwiseEquation source configuration) :
    FormNativeP286GaugeConnectionPointwiseEquation source configuration ↔
      FormNativeP286GaugeYangMillsPointwiseEquation source configuration := by
  have fixed : configuration =
      formNativeP286GaugeConstitutiveReadout source configuration :=
    (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout source
      configuration nondegenerate).1 auxiliaryEquation
  constructor
  · intro connectionEquation
    exact fixed ▸ connectionEquation
  · intro yangMillsEquation
    exact fixed.symm ▸ yangMillsEquation

/-- The two active first-order pointwise equations are exactly a fixed-point
algebraic elimination plus the whole-field Yang--Mills readout. -/
theorem formNativeP286GaugeMasterPointwiseEquations_iff_eliminated_yangMills
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (FormNativeP286GaugeAuxiliaryPointwiseEquation source configuration ∧
        FormNativeP286GaugeConnectionPointwiseEquation source configuration) ↔
      (configuration =
          formNativeP286GaugeConstitutiveReadout source configuration ∧
        FormNativeP286GaugeYangMillsPointwiseEquation source configuration) := by
  constructor
  · rintro ⟨auxiliaryEquation, connectionEquation⟩
    have fixed : configuration =
        formNativeP286GaugeConstitutiveReadout source configuration :=
      (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout source
        configuration nondegenerate).1 auxiliaryEquation
    exact ⟨fixed, fixed ▸ connectionEquation⟩
  · rintro ⟨fixed, yangMillsEquation⟩
    have auxiliaryEquation :
        FormNativeP286GaugeAuxiliaryPointwiseEquation source configuration :=
      (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout source
        configuration nondegenerate).2 fixed
    exact ⟨auxiliaryEquation, fixed.symm ▸ yangMillsEquation⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeYangMillsReadout
