import H0mework.Physics.CoframeJets.StateDependentCartanCoframeFirstJetLocalActualLift
import H0mework.Physics.Exterior.IIPlusFieldVariation

/-!
# S9-C3h105: actual Cartan tangent-simplicity response

C3h103 already lets the source/action path generate the quadratic coframe
history `U` and then defines its gravity auxiliary field by
`B := II⁺(U)`.  This module differentiates that same actual history forward:

```text
source/action
→ actual Lorentz time jet
→ Cartan coframe acceleration
→ actual quadratic coframe path U
→ B := II⁺(U)
→ Ḃ = D II⁺(U)[U̇]
→ nonzero B̈ readout.
```

The generic native-coordinate theorem differentiates the quadratic
`coframeWedge` polynomial directly, so it does not need the old Euclidean
`TetradVector` derivative interface or any inverse conversion.  The positive
path is globally nondegenerate, satisfies tangent simplicity in all
thirty-six bivector coordinates, and has the strict response
`B̈(0) (3,0) = -1`.

This is an action-owned response/acceptance checkpoint for an already
generated actual `U`, not a new endpoint producer.  No residual coordinate,
endpoint, preimage, right inverse, supplied certificate, source knob, or
branch receipt enters the construction.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCartanTangentSimplicityResponse

open ProofFreeRicherAnholonomicSource
open PointwiseDiracSpinConnectionLift
open StageNineCanonicalCauchyState
open StageNineCartanActionCoframeSecondJetLocalActualLift
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineScalarActionSecondJetLocalActualLift
open StageNineStateDependentCartanCoframeFirstJetLocalActualLift
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

def positiveCartanCoframeAccelerationNormalForm :
    LorentzianCoframe :=
  Matrix.diagonal ![0, 1, 1, 1]

theorem positiveActionGeneratedCartanCoframeAcceleration_eq_normalForm :
    positiveActionGeneratedCartanCoframeAcceleration =
      positiveCartanCoframeAccelerationNormalForm := by
  ext internal coordinate
  fin_cases internal <;> fin_cases coordinate <;>
    simp [positiveActionGeneratedCartanCoframeAcceleration,
      positiveActionGeneratedCartanSpatialCoframeAcceleration,
      positiveActionGeneratedLorentzConnectionTimeJet,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      actionGeneratedLorentzLocalConnectionJet,
      actionGeneratedLorentzSpatialConnectionVelocity,
      actionGeneratedGravityCurvature,
      cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate,
      cauchyLoweredLorentzConnectionBracketCoordinate,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm,
      actionGeneratedGravityAuxiliary,
      gravityInternalDualEquiv, gravityInternalDualLinear,
      physicalIIPlusBivector, internalBivectorDual, coframeWedge,
      lorentzianCoframeHodge,
      temporalSpatialPair, pairFirst, pairSecond,
      minkowskiInternalSign, canonicalLorentzianTimeDirection,
      positiveCartanCoframeAccelerationNormalForm,
      Matrix.one_apply, Fin.sum_univ_six]

def positiveCartanRadialScale (point : BasePoint) : ℝ :=
  1 + scalarQuadraticTimeCoefficient point

def positiveCartanCoframeNormalForm
    (point : BasePoint) : LorentzianCoframe :=
  Matrix.diagonal
    ![1, positiveCartanRadialScale point,
      positiveCartanRadialScale point,
      positiveCartanRadialScale point]

theorem positiveActionGeneratedCartanCoframeField_eq_normalForm
    (point : BasePoint) :
    positiveActionGeneratedCartanCoframeField point =
      positiveCartanCoframeNormalForm point := by
  rw [positiveActionGeneratedCartanCoframeField,
    positiveActionGeneratedCartanCoframeAcceleration_eq_normalForm]
  ext internal coordinate
  fin_cases internal <;> fin_cases coordinate <;>
    simp [positivePathFirstJointLocalActualLift_coframe,
      positiveCartanCoframeAccelerationNormalForm,
      positiveCartanCoframeNormalForm, positiveCartanRadialScale]

theorem positiveCartanRadialScale_pos (point : BasePoint) :
    0 < positiveCartanRadialScale point := by
  unfold positiveCartanRadialScale scalarQuadraticTimeCoefficient
  nlinarith [sq_nonneg
    (localBaseCoordinate canonicalLorentzianTimeDirection point)]

theorem positiveActionGeneratedCartanCoframeField_det
    (point : BasePoint) :
    Matrix.det (positiveActionGeneratedCartanCoframeField point) =
      positiveCartanRadialScale point ^ 3 := by
  rw [positiveActionGeneratedCartanCoframeField_eq_normalForm]
  simp [positiveCartanCoframeNormalForm, Matrix.det_diagonal,
    Fin.prod_univ_succ]
  ring

theorem positiveActionGeneratedCartanJointLocalActualLift_nondegenerate :
    positiveActionGeneratedCartanJointLocalActualLift.Nondegenerate := by
  intro point
  rw [show
    positiveActionGeneratedCartanJointLocalActualLift.coframe point =
      positiveActionGeneratedCartanCoframeField point by rfl,
    positiveActionGeneratedCartanCoframeField_det]
  exact pow_ne_zero 3 (ne_of_gt (positiveCartanRadialScale_pos point))

theorem positiveActionGeneratedCartanCoframeField_component_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      positiveActionGeneratedCartanCoframeField point internal coordinate := by
  unfold positiveActionGeneratedCartanCoframeField
  rw [positivePathFirstJointLocalActualLift_coframe]
  unfold scalarQuadraticTimeCoefficient
  fun_prop

theorem positiveActionGeneratedCartanCoframeField_timeTangent
    (point : BasePoint) :
    coframeFieldDirectionalTangent
        positiveActionGeneratedCartanCoframeField point
        canonicalLorentzianTimeDirection =
      point canonicalLorentzianTimeDirection •
        positiveActionGeneratedCartanCoframeAcceleration := by
  ext internal coordinate
  unfold coframeFieldDirectionalTangent
  rw [positiveActionGeneratedCartanCoframeField_timeDerivative]
  rfl

/-- Forward tangent simplicity along the already-generated C3h103 path. -/
theorem
    positiveActionGeneratedCartanGravityAuxiliaryField_timeDerivative
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    fieldDirectionalDerivative
        (fun candidate =>
          positiveActionGeneratedCartanGravityAuxiliaryField candidate
            internalPair spacetimePair)
        point canonicalLorentzianTimeDirection =
      physicalIIPlusCoframeTangent
          (positiveActionGeneratedCartanCoframeField point)
          (point canonicalLorentzianTimeDirection •
            positiveActionGeneratedCartanCoframeAcceleration)
        internalPair spacetimePair := by
  unfold positiveActionGeneratedCartanGravityAuxiliaryField
  rw [physicalIIPlusBivector_fieldDirectionalDerivative
    positiveActionGeneratedCartanCoframeField
    positiveActionGeneratedCartanCoframeField_component_contDiff]
  rw [positiveActionGeneratedCartanCoframeField_timeTangent]

theorem positiveCartanRadialScale_contDiff :
    ContDiff ℝ ∞ positiveCartanRadialScale := by
  unfold positiveCartanRadialScale scalarQuadraticTimeCoefficient
  fun_prop

theorem positiveCartanRadialScale_timeDerivative
    (point : BasePoint) :
    fieldDirectionalDerivative positiveCartanRadialScale point
        canonicalLorentzianTimeDirection =
      point canonicalLorentzianTimeDirection := by
  unfold positiveCartanRadialScale fieldDirectionalDerivative
  rw [((scalarQuadraticTimeCoefficient_hasFDerivAt point).const_add 1).fderiv]
  simp [coordinateDirection]
  ring

theorem
    positiveActionGeneratedCartanGravityAuxiliaryField_component_3_0
    (point : BasePoint) :
    positiveActionGeneratedCartanGravityAuxiliaryField point 3 0 =
      -positiveCartanRadialScale point := by
  unfold positiveActionGeneratedCartanGravityAuxiliaryField
  rw [positiveActionGeneratedCartanCoframeField_eq_normalForm]
  simp [physicalIIPlusBivector, internalBivectorDual,
    lorentzianCoframeHodge, coframeWedge, pairFirst, pairSecond,
    positiveCartanCoframeNormalForm]

theorem
    positiveActionGeneratedCartanGravityAuxiliaryField_component_3_0_timeDerivative
    (point : BasePoint) :
    fieldDirectionalDerivative
        (fun candidate =>
          positiveActionGeneratedCartanGravityAuxiliaryField
            candidate 3 0)
        point canonicalLorentzianTimeDirection =
      -point canonicalLorentzianTimeDirection := by
  rw [show
    (fun candidate =>
      positiveActionGeneratedCartanGravityAuxiliaryField
        candidate 3 0) =
      fun candidate => -positiveCartanRadialScale candidate by
    funext candidate
    exact
      positiveActionGeneratedCartanGravityAuxiliaryField_component_3_0
        candidate]
  rw [fieldDirectionalDerivative_neg_of_contDiff
    positiveCartanRadialScale positiveCartanRadialScale_contDiff]
  rw [positiveCartanRadialScale_timeDerivative]

theorem
    positiveActionGeneratedCartanGravityAuxiliaryField_component_3_0_secondTime_origin :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            (fun candidate =>
              positiveActionGeneratedCartanGravityAuxiliaryField
                candidate 3 0)
            point canonicalLorentzianTimeDirection)
        0 canonicalLorentzianTimeDirection =
      -1 := by
  rw [show
    (fun point =>
      fieldDirectionalDerivative
        (fun candidate =>
          positiveActionGeneratedCartanGravityAuxiliaryField
            candidate 3 0)
        point canonicalLorentzianTimeDirection) =
      fun point => -point canonicalLorentzianTimeDirection by
    funext point
    exact
      positiveActionGeneratedCartanGravityAuxiliaryField_component_3_0_timeDerivative
        point]
  rw [show
    (fun point : BasePoint =>
      -point canonicalLorentzianTimeDirection) =
      fun point =>
        -(localBaseCoordinate canonicalLorentzianTimeDirection point) by
    rfl]
  change
    fieldDirectionalDerivative
        (-((localBaseCoordinate canonicalLorentzianTimeDirection :
          BasePoint →L[ℝ] ℝ) : BasePoint → ℝ))
        0 canonicalLorentzianTimeDirection = -1
  unfold fieldDirectionalDerivative
  rw [(localBaseCoordinate canonicalLorentzianTimeDirection
    |>.hasFDerivAt.neg.fderiv)]
  simp [coordinateDirection]

/-- C3h105 packages only downstream properties of the actual path already
generated in C3h103.  In particular, the action-generated second-jet law
remains the provenance owner; tangent simplicity is an acceptance readout. -/
structure PositiveActionCartanTangentSimplicityResponseLaw
    (actual : StageNineHolonomicConfiguration) : Prop where
  actionGeneratedSecondJet :
    PositiveActionCartanSecondJetLocalActualLaw actual
  nondegenerate :
    actual.Nondegenerate
  coframeTimeTangent :
    ∀ point,
      coframeFieldDirectionalTangent actual.coframe point
          canonicalLorentzianTimeDirection =
        point canonicalLorentzianTimeDirection •
          positiveActionGeneratedCartanCoframeAcceleration
  tangentSimplicity :
    ∀ point internalPair spacetimePair,
      fieldDirectionalDerivative
          (fun candidate =>
            actual.gravityAuxiliary candidate internalPair spacetimePair)
          point canonicalLorentzianTimeDirection =
        physicalIIPlusCoframeTangent
            (actual.coframe point)
            (coframeFieldDirectionalTangent actual.coframe point
              canonicalLorentzianTimeDirection)
          internalPair spacetimePair
  strictSecondResponse :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            (fun candidate =>
              actual.gravityAuxiliary candidate 3 0)
            point canonicalLorentzianTimeDirection)
        0 canonicalLorentzianTimeDirection =
      -1

theorem
    positiveActionGeneratedCartanTangentSimplicityResponse_realizes_C3h105 :
    PositiveActionCartanTangentSimplicityResponseLaw
      positiveActionGeneratedCartanJointLocalActualLift := by
  refine
    { actionGeneratedSecondJet :=
        positiveActionGeneratedCartanJointLocalActualLift_realizes_C3h103,
      nondegenerate :=
        positiveActionGeneratedCartanJointLocalActualLift_nondegenerate,
      coframeTimeTangent :=
        positiveActionGeneratedCartanCoframeField_timeTangent,
      tangentSimplicity := ?_,
      strictSecondResponse :=
        positiveActionGeneratedCartanGravityAuxiliaryField_component_3_0_secondTime_origin }
  intro point internalPair spacetimePair
  change
    fieldDirectionalDerivative
        (fun candidate =>
          positiveActionGeneratedCartanGravityAuxiliaryField candidate
            internalPair spacetimePair)
        point canonicalLorentzianTimeDirection =
      physicalIIPlusCoframeTangent
          (positiveActionGeneratedCartanCoframeField point)
          (coframeFieldDirectionalTangent
            positiveActionGeneratedCartanCoframeField point
            canonicalLorentzianTimeDirection)
        internalPair spacetimePair
  rw [positiveActionGeneratedCartanCoframeField_timeTangent]
  exact
    positiveActionGeneratedCartanGravityAuxiliaryField_timeDerivative
      point internalPair spacetimePair

end

end
  SaturationMonoid.PhysicsCore.StageNineCartanTangentSimplicityResponse
