import H0mework.Physics.RepairedAction.ActionSpatialSectionFullResidualNormalForm
import H0mework.Physics.RepairedAction.ActionSpatialSectionRecenterActionJetNaturality

/-!
# Matching-contact residual normal form of the repaired spatial section

The whole action-jet comparison already separates the assembled section into
one gravity-curvature seam and the literal residual of its matching
source/action-generated contact.  This module restores that contact residual
as one carrier from the existing section normal form.

No residual coordinate, support branch, or zero-fiber witness enters an
action write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterContactResidualNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveDifferentialSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualNormalForm
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionGaugeScalarNormalForm
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterActionJetNaturality
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

/-- Explicit whole contact carrier.  Five channels are already zero; the
remaining Lorentz, P286, scalar, and coframe channels retain their exact
mother-action normal forms. -/
def recenteredContactJointResidualFullNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  let point := canonicalCauchySlicePoint 0 space
  { gravityMultiplier := 0
    gravityAuxiliary := 0
    p286GaugeAuxiliary := 0
    lorentzConnection :=
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeJointActionSolvedSuccessor point
    p286GaugeConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessorP286ConnectionExplicitZeroSliceNormalForm
        space
    scalar :=
      fixedP506FormNativeConstitutiveJointActionSuccessorScalarZeroSliceNormalForm
        space
    matter := 0
    conjugateMatter := 0
    coframe :=
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeResidualZeroSliceNormalForm
        space }

private theorem restoreGravityAuxiliaryZero
    (contact normal : DiracDualFormNativePointwiseJointResidualCarrier)
    (seam : PhysicalBivector)
    (contactZero : contact.gravityAuxiliary = 0)
    (classified : { contact with gravityAuxiliary := seam } = normal) :
    contact = { normal with gravityAuxiliary := 0 } := by
  subst normal
  cases contact
  cases contactZero
  rfl

private theorem recenteredContactGravityAuxiliaryResidual_zero
    (space : StageNineSpatialPoint) :
    (recenteredContactJointResidualAtMatchingOccurrence space
      ).gravityAuxiliary = 0 := by
  change
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField (recenteredContactActual space) 0) = 0
  exact congrFun
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_auxiliaryEquation
      positiveSmoothUnifiedSource
      (spatiallyRecenterHolonomicConfiguration
        FixedP506FormNativeJointActionSolvedSuccessor space))
    0

/-- The matching global occurrence label is not an extra action input.  The
whole contact residual is exactly the authoritative pointwise residual of the
same source/action-generated contact at its own origin. -/
theorem recenteredContactJointResidualAtMatchingOccurrence_eq_contactOrigin
    (space : StageNineSpatialPoint) :
    recenteredContactJointResidualAtMatchingOccurrence space =
      diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (recenteredContactActual space) 0 := by
  unfold recenteredContactJointResidualAtMatchingOccurrence
  rw [diracDualFormNativeJointResidualOfActionJet_point_independent
    positiveSmoothUnifiedSource (canonicalCauchySlicePoint 0 space) 0
    (recenteredContactActionJet space)]
  simpa only [recenteredContactActionJet] using
    (diracDualFormNativePointwiseJointResidual_eq_actionJetReadout
      positiveSmoothUnifiedSource (recenteredContactActual space) 0).symm

/-- Whole matching-contact residual normal form.  The theorem recovers all
nine coordinates at once; it does not reopen field-local repair routes. -/
theorem recenteredContactJointResidualAtMatchingOccurrence_eq_fullNormalForm
    (space : StageNineSpatialPoint) :
    recenteredContactJointResidualAtMatchingOccurrence space =
      recenteredContactJointResidualFullNormalForm space := by
  have classified :
      { recenteredContactJointResidualAtMatchingOccurrence space with
        gravityAuxiliary :=
          recenteredContactGravityCurvatureAssemblySeam space } =
        fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm
          space := by
    have sectionToContact :=
      (sectionJointResidual_eq_recenteredContactWithGravitySeam space).trans
        (recenteredContactJointResidualWithGravitySeam_classification space)
    have sectionToNormal :=
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_zeroSlice_fullNormalForm
        space
    change
      diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor
          (canonicalCauchySlicePoint 0 space) = _ at sectionToNormal
    exact sectionToContact.symm.trans sectionToNormal
  have restored := restoreGravityAuxiliaryZero
    (recenteredContactJointResidualAtMatchingOccurrence space)
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm
      space)
    (recenteredContactGravityCurvatureAssemblySeam space)
    (recenteredContactGravityAuxiliaryResidual_zero space)
    classified
  simpa [recenteredContactJointResidualFullNormalForm,
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm,
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm,
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFourChannelResidualZeroSliceNormalForm]
    using restored

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterContactResidualNormalForm
