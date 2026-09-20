import H0mework.Physics.FixedJoint.FixedConstitutiveFirstJet

/-!
# Fixed P506/L0 constitutive-successor residual section

This module computes the carrier-level normal form of the residual read from
the already source/action-generated constitutive successor.  On the
nondegenerate coframe domain, the three algebraic action channels vanish
together; the remaining six coordinates are read from that same actual and
the same action occurrence.

This is a diagnostic/acceptance module.  Neither this normal form, its
support, nor the negative of any coordinate is a write producer.  A later
successor must still be generated forward by the existing same-source action
operator before this section may be used as a consistency regression.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSectionResidual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveFirstJet
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeScalarVariation
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-- Complete pointwise normal form of the constitutive successor residual.
The first three coordinates are the jointly settled algebraic action
channels.  The other six are literal readouts from the same generated
successor, not transported values from a predecessor. -/
def fixedP506FormNativeConstitutiveJointActionSuccessorResidualSectionNormalForm
    (point : BasePoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { gravityMultiplier := 0
    gravityAuxiliary := 0
    p286GaugeAuxiliary := 0
    lorentzConnection :=
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeConstitutiveJointActionSuccessor point
    p286GaugeConnection :=
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeConstitutiveJointActionSuccessor point
    scalar := fun direction =>
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction point
    matter := fun direction =>
      diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction point
    conjugateMatter := fun direction =>
      diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction point
    coframe :=
      diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource
        point
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor point) }

/-- On every nondegenerate point of the generated actual, all three
algebraic action channels reduce to zero in one carrier equality. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection_normalForm
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
        (FixedP506FormNativeConstitutiveJointActionSuccessor.coframe point) ≠
        0) :
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection point =
      fixedP506FormNativeConstitutiveJointActionSuccessorResidualSectionNormalForm
        point := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        point
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
        point
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zero
        point nondegenerate
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The generated time-zero slice lies entirely in the nondegenerate domain,
so its complete residual section has the three-channel normal form without
an extra premise. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorResidualSectionNormalForm
        (canonicalCauchySlicePoint 0 space) := by
  apply
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection_normalForm
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
  norm_num

/-! ## Literal P286 connection readout on the generated slice -/

/-- The P286 connection residual with the already generated constitutive
first jet substituted.  This is a readout of the current action occurrence;
the expression is not a prescription for another write. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionZeroSliceNormalForm
    (space : StageNineSpatialPoint) : P286GaugeThreeForm :=
  let point := canonicalCauchySlicePoint 0 space
  pointwiseP286GaugeTwoFormExteriorCovariantDerivative
      (holonomicP286GaugeConnectionCoordinate
        FixedP506FormNativeConstitutiveJointActionSuccessor point)
      (fixedP506FormNativeConstitutiveAuxiliaryCoordinate point)
      (fun direction =>
        fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection direction)) +
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField
        FixedP506FormNativeConstitutiveJointActionSuccessor point)

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).p286GaugeConnection =
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionZeroSliceNormalForm
        space := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionZeroSliceNormalForm
        space
  unfold holonomicFormNativeP286GaugeEulerThreeForm
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionZeroSliceNormalForm
  have derivativeEquality :
      p286GaugeAuxiliaryDirectionalDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (canonicalCauchySlicePoint 0 space) =
        fun direction =>
          fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
            (coordinateDirection direction) := by
    funext direction
    exact
      fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryDirectionalDerivative_zeroSlice
        space direction
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryCoordinate,
    derivativeEquality]

/-- Complete time-zero carrier normal form after substituting the actual
constitutive first jet into the P286 connection channel.  The other five
differential channels remain literal same-actual readouts. -/
def
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeConstitutiveJointActionSuccessorResidualSectionNormalForm
      (canonicalCauchySlicePoint 0 space) with
    p286GaugeConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionZeroSliceNormalForm
        space }

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection_zeroSlice_completeNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeConstitutiveJointActionSuccessorResidualZeroSliceNormalForm
        space := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
        _
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zeroSlice
        space
  · rfl
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_zeroSlice_normalForm
        space
  · rfl
  · rfl
  · rfl
  · rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSectionResidual
