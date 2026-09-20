import H0mework.Physics.JointVariation.FullOccurrenceContactOperator
import H0mework.Physics.ConstrainedCauchy.ConnectionJetReadout

/-!
# Source-generated profiles of the complete joint action

This module packages the action data generated at one spacetime occurrence by
the existing Cartan restart and dependency-ordered M/S/P/E producers.  The
public constructor consumes only one source, one current, and the occurrence
at which that current is canonically recentered.

The bundle records the generated matter velocities, scalar acceleration,
P286 auxiliary data, and the complete Einstein--Cartan connection jet.  It is
not a global field lift: downstream writers must continue to consume the
original `(source,current)` and generate their own section.  No residual,
assembly seam, support branch, candidate profile, or zero-fiber receipt is an
input here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Typed action profile -/

/-- The source/action data generated at one complete-joint contact.

The eight coordinates retain the exact dependency order of the existing
writers.  In particular, the adjoint velocity is read after the primal matter
write, the scalar acceleration after the repaired constitutive write, the
P286 data after the scalar write, and the gravity data from the pre-EC current.
-/
structure CompleteJointGeneratedProfiles where
  matterVelocity : DiracExteriorMatterCarrier
  adjointVelocity : Module.Dual ℂ DiracExteriorMatterCarrier
  scalarAcceleration : ScalarCoordinateCarrier
  p286AuxiliaryOrigin : P286GaugeTwoForm
  p286RequiredExteriorDerivative : P286GaugeThreeForm
  gravityConnectionOrigin : PointwiseLorentzSpinConnection
  gravityCurvatureTarget : PhysicalBivector
  gravityLoweredConnectionFirstJet :
    LorentzianIndex → LorentzianIndex → Fin 6 → ℝ

/-! ## Source/current-only constructor -/

/-- The current on which the complete-joint profile is generated at one
spacetime occurrence.  Full recentering and the Cartan reaction restart are
both recomputed from the supplied `(source,current)`; neither is supplied as
a profile field. -/
def completeJointGeneratedProfileRestartCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
    (fullyRecenterHolonomicConfiguration current contact)

/-- Extract the exact M/S/P/E action data from one current.  In the public
occurrence constructor below that current is the action-generated Cartan
restart; this dependency helper itself makes no stronger provenance claim and
does not accept target profiles.
-/
def completeJointGeneratedProfilesFromCurrent
    (source : SmoothUnifiedSource)
    (restartCurrent : StageNineHolonomicConfiguration) :
    CompleteJointGeneratedProfiles where
  matterVelocity :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
      restartCurrent 0
  adjointVelocity :=
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
        restartCurrent)
      0
  scalarAcceleration :=
    genericDiracDualScalarGeneratedAcceleration source
      (completeJointRepairedConstitutiveCurrent source restartCurrent)
  p286AuxiliaryOrigin :=
    currentP286OriginAuxiliaryCoordinate
      (completeJointScalarSecondJetCurrent source restartCurrent)
  p286RequiredExteriorDerivative :=
    formNativeCurrentP286RequiredExteriorDerivative source
      (completeJointScalarSecondJetCurrent source restartCurrent)
  gravityConnectionOrigin :=
    sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin source
      (completeJointPreECCurrent source restartCurrent)
  gravityCurvatureTarget :=
    sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget source
      (completeJointPreECCurrent source restartCurrent)
  gravityLoweredConnectionFirstJet :=
    sourceActionGeneratedDiracDualECFullCauchyLoweredConnectionFirstJet source
      (completeJointPreECCurrent source restartCurrent)

/-- The complete generated profile at one physical occurrence.  The contact
only selects the canonical recentering of the supplied current; every response
coordinate is then generated by the existing action operators. -/
def sourceActionGeneratedDiracDualCompleteJointProfiles
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : CompleteJointGeneratedProfiles :=
  completeJointGeneratedProfilesFromCurrent source
    (completeJointGeneratedProfileRestartCurrent source current contact)

/-! ## Exact field readouts -/

@[simp] theorem sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles source current contact
      ).matterVelocity =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (completeJointGeneratedProfileRestartCurrent source current contact)
        0 :=
  rfl

@[simp] theorem sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles source current contact
      ).adjointVelocity =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (completeJointGeneratedProfileRestartCurrent source current contact))
        0 :=
  rfl

@[simp] theorem sourceActionGeneratedDiracDualCompleteJointProfiles_scalarAcceleration
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles source current contact
      ).scalarAcceleration =
      genericDiracDualScalarGeneratedAcceleration source
        (completeJointRepairedConstitutiveCurrent source
          (completeJointGeneratedProfileRestartCurrent source current
            contact)) :=
  rfl

@[simp] theorem sourceActionGeneratedDiracDualCompleteJointProfiles_p286AuxiliaryOrigin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles source current contact
      ).p286AuxiliaryOrigin =
      currentP286OriginAuxiliaryCoordinate
        (completeJointScalarSecondJetCurrent source
          (completeJointGeneratedProfileRestartCurrent source current
            contact)) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointProfiles_p286RequiredExteriorDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles source current contact
      ).p286RequiredExteriorDerivative =
      formNativeCurrentP286RequiredExteriorDerivative source
        (completeJointScalarSecondJetCurrent source
          (completeJointGeneratedProfileRestartCurrent source current
            contact)) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointProfiles_gravityConnectionOrigin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles source current contact
      ).gravityConnectionOrigin =
      sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin source
        (completeJointPreECCurrent source
          (completeJointGeneratedProfileRestartCurrent source current
            contact)) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointProfiles_gravityCurvatureTarget
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles source current contact
      ).gravityCurvatureTarget =
      sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget source
        (completeJointPreECCurrent source
          (completeJointGeneratedProfileRestartCurrent source current
            contact)) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointProfiles_gravityLoweredConnectionFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles source current contact
      ).gravityLoweredConnectionFirstJet =
      sourceActionGeneratedDiracDualECFullCauchyLoweredConnectionFirstJet source
        (completeJointPreECCurrent source
          (completeJointGeneratedProfileRestartCurrent source current
            contact)) :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
