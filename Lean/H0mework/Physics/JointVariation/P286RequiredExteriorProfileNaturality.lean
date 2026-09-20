import H0mework.Physics.JointVariation.P286TemporalDevelopmentOperator
import H0mework.Physics.DualVariation.PointwiseActionJetCarrier
import H0mework.Physics.DualVariation.RecenteredScalarSecondJetActionResponse
import H0mework.Physics.GaugeAction.P286RequiredExteriorActionDataCongruence
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Complete-joint P286 required-profile naturality

At one occurrence, the complete-joint profile producer first fully recenters
the supplied current and then applies the existing Cartan, repaired
matter/constitutive, and scalar second-jet action writes.  If the supplied
current's P286 auxiliary already equals the source-generated constitutive
readout at that occurrence, those writes preserve every action datum consumed
by the required exterior profile.

The main theorem transports the generated profile to the direct action read
on the fully recentered current.  It is an action-read naturality theorem, not
a producer: the constitutive equality is an explicit property of the supplied
current and is neither stored in the source nor used to construct a new field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality

open ProofFreeRicherAnholonomicSource
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286RequiredExteriorActionDataCongruence
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGaugeCurvatureTransport
open StageNineMatterVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarActionSecondJetLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance p286RequiredProfileNaturalityModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286RequiredProfileNaturalityCoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Direct pointwise action read -/

/-- Direct required exterior derivative read at one occurrence of the
original current:

```text
J_charged(source, current, contact) - [A, B](current, contact).
```

This definition contains no recentered current, residual coordinate, or
response.  It is a pointwise read of the source-owned action and the supplied
current's primitive action data in the normalized zero chart. -/
def pointwiseDirectP286RequiredExteriorDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : P286GaugeThreeForm :=
  formNativePhysicalChargedGaugeCurrentThreeForm source 0 contact
      (toContinuumPointField current contact) -
    pointwiseP286GaugeTwoFormConnectionExteriorAction
      (holonomicP286GaugeConnectionCoordinate current contact)
      (holonomicP286GaugeAuxiliaryCoordinate current contact)

private abbrev RecenteredCurrent
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration current contact

private abbrev RestartedCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
    (RecenteredCurrent current contact)

private abbrev RepairedCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointRepairedConstitutiveCurrent source
    (RestartedCurrent source current contact)

private abbrev ProfileAcceleration
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : ScalarCoordinateCarrier :=
  genericDiracDualScalarGeneratedAcceleration source
    (RepairedCurrent source current contact)

private abbrev ProfileCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointScalarSecondJetCurrent source
    (RestartedCurrent source current contact)

private theorem repairedCurrent_scalar_eq_recentered
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (RepairedCurrent source current contact).scalar =
      (RecenteredCurrent current contact).scalar := by
  rfl

private theorem repairedCurrent_gaugeConnection_eq_recentered
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (RepairedCurrent source current contact).gaugeConnection =
      (RecenteredCurrent current contact).gaugeConnection := by
  rfl

private theorem profileCurrent_scalar_eq_recentered_add
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (ProfileCurrent source current contact).scalar =
      fun point =>
        (RecenteredCurrent current contact).scalar point +
          scalarQuadraticTimeCorrection
            (ProfileAcceleration source current contact) point := by
  rfl

private theorem profileCurrent_gaugeConnection_eq_recentered
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (ProfileCurrent source current contact).gaugeConnection =
      (RecenteredCurrent current contact).gaugeConnection := by
  rfl

private theorem profileCurrent_scalar_origin_eq_recentered
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (ProfileCurrent source current contact).scalar 0 =
      (RecenteredCurrent current contact).scalar 0 := by
  rw [profileCurrent_scalar_eq_recentered_add]
  simp

private theorem profileCurrent_scalarCovariantDerivative_origin_eq_recentered
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicScalarCovariantDerivative
        (ProfileCurrent source current contact) 0 =
      holonomicScalarCovariantDerivative
        (RecenteredCurrent current contact) 0 := by
  by_cases baseDifferentiable :
      DifferentiableAt ℝ
        (RecenteredCurrent current contact).scalar 0
  · have repairedDifferentiable :
        DifferentiableAt ℝ
          (RepairedCurrent source current contact).scalar 0 := by
      rw [repairedCurrent_scalar_eq_recentered]
      exact baseDifferentiable
    have generated :=
      holonomicScalarCovariantDerivative_installScalarQuadraticTimeCorrection_origin
        (RepairedCurrent source current contact)
        (ProfileAcceleration source current contact)
        repairedDifferentiable
    have generatedEq :
        holonomicScalarCovariantDerivative
            (ProfileCurrent source current contact) 0 =
          holonomicScalarCovariantDerivative
            (RepairedCurrent source current contact) 0 := by
      simpa [ProfileCurrent, completeJointScalarSecondJetCurrent,
        genericDiracDualScalarSecondJetActionResponse,
        installScalarQuadraticTimeCorrection] using generated
    refine generatedEq.trans ?_
    funext direction
    unfold holonomicScalarCovariantDerivative
    rw [repairedCurrent_scalar_eq_recentered,
      repairedCurrent_gaugeConnection_eq_recentered]
  · have correctionDifferentiable :
        DifferentiableAt ℝ
          (scalarQuadraticTimeCorrection
            (ProfileAcceleration source current contact)) 0 :=
      ((scalarQuadraticTimeCoefficient_hasFDerivAt (0 : BasePoint)
        ).smul_const
          (ProfileAcceleration source current contact)).differentiableAt
    have generatedNotDifferentiable :
        ¬ DifferentiableAt ℝ
            (ProfileCurrent source current contact).scalar 0 := by
      intro generatedDifferentiable
      have recovered :
          DifferentiableAt ℝ
            (fun point =>
              (ProfileCurrent source current contact).scalar point -
                scalarQuadraticTimeCorrection
                  (ProfileAcceleration source current contact) point)
            0 :=
        generatedDifferentiable.sub correctionDifferentiable
      have recoveredEq :
          (fun point =>
            (ProfileCurrent source current contact).scalar point -
              scalarQuadraticTimeCorrection
                (ProfileAcceleration source current contact) point) =
            (RecenteredCurrent current contact).scalar := by
        funext point
        rw [profileCurrent_scalar_eq_recentered_add]
        module
      rw [recoveredEq] at recovered
      exact baseDifferentiable recovered
    funext direction
    unfold holonomicScalarCovariantDerivative fieldDirectionalDerivative
    rw [fderiv_zero_of_not_differentiableAt generatedNotDifferentiable,
      fderiv_zero_of_not_differentiableAt baseDifferentiable]
    rw [profileCurrent_gaugeConnection_eq_recentered,
      profileCurrent_scalar_origin_eq_recentered]

private theorem fullyRecenter_gaugeCurvature_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicGaugeCurvature
        (RecenteredCurrent current contact) 0 =
      holonomicGaugeCurvature current contact := by
  have derivativeEq
      (derivativeDirection formDirection : LorentzianIndex) :
      p286ConnectionDerivative
          (RecenteredCurrent current contact) 0
          derivativeDirection formDirection =
        p286ConnectionDerivative current contact derivativeDirection
          formDirection := by
    unfold p286ConnectionDerivative
    apply congrArg p286CoordinateEquiv.symm
    change
      fieldDirectionalDerivative
          ((fun point =>
            holonomicP286GaugeConnectionCoordinate current point
              formDirection) ∘
            canonicalSpacetimeContactTranslation contact)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeConnectionCoordinate current point
              formDirection)
          contact derivativeDirection
    simpa using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun point =>
          holonomicP286GaugeConnectionCoordinate current point formDirection)
        contact 0 derivativeDirection
  funext pair
  unfold holonomicGaugeCurvature
  rw [derivativeEq, derivativeEq]
  simp [RecenteredCurrent, fullyRecenterHolonomicConfiguration]

private theorem fullyRecenter_scalarCovariantDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicScalarCovariantDerivative
        (RecenteredCurrent current contact) 0 =
      holonomicScalarCovariantDerivative current contact := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  change
    fieldDirectionalDerivative
          (current.scalar ∘ canonicalSpacetimeContactTranslation contact)
          0 direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection
              (canonicalSpacetimeContactTranslation contact 0) direction))
          (current.scalar
            (canonicalSpacetimeContactTranslation contact 0)) =
      fieldDirectionalDerivative current.scalar contact direction +
        scalarMotherLieAction
          (p286LieBlockEmbed (current.gaugeConnection contact direction))
          (current.scalar contact)
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  simp

private theorem fullyRecenter_physicalChargedGaugeCurrent_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    formNativePhysicalChargedGaugeCurrentThreeForm source 0 0
        (toContinuumPointField (RecenteredCurrent current contact) 0) =
      formNativePhysicalChargedGaugeCurrentThreeForm source 0 contact
        (toContinuumPointField current contact) := by
  apply congrArg Neg.neg
  rw [formNativeChargedGaugeThreeForm_zeroChart_point_independent source
    0 contact
    (toContinuumPointField (RecenteredCurrent current contact) 0)]
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  change
    formNativeChargedGaugeFirstCoefficient source 0 contact
        (toContinuumPointField
          (RecenteredCurrent current contact) 0) direction =
      formNativeChargedGaugeFirstCoefficient source 0 contact
        (toContinuumPointField current contact) direction
  unfold formNativeChargedGaugeFirstCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
    matterGaugeKineticSum
    pointwiseScalarP286GaugeConnectionVariation
    pointwiseMatterP286GaugeConnectionVariation
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [fullyRecenterHolonomicConfiguration_coframe_origin,
    fullyRecenterHolonomicConfiguration_scalar_origin,
    fullyRecenter_scalarCovariantDerivative_origin,
    fullyRecenterHolonomicConfiguration_matter_origin,
    fullyRecenterHolonomicConfiguration_conjugateMatter_origin]

/-- The origin action read of a fully recentered current is exactly the direct
required exterior derivative read on the original current at the selected
occurrence.  This is total recentering naturality: it holds for every current,
without a smoothness or differentiability premise. -/
theorem
    formNativeCurrentP286RequiredExteriorDerivative_fullyRecenter_eq_pointwiseDirect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    formNativeCurrentP286RequiredExteriorDerivative source
        (fullyRecenterHolonomicConfiguration current contact) =
      pointwiseDirectP286RequiredExteriorDerivative source current contact := by
  unfold formNativeCurrentP286RequiredExteriorDerivative
    pointwiseDirectP286RequiredExteriorDerivative
  rw [fullyRecenter_physicalChargedGaugeCurrent_origin]
  congr 2
  · unfold holonomicP286GaugeConnectionCoordinate
    rw [fullyRecenterHolonomicConfiguration_gaugeConnection_origin]
  · unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [fullyRecenterHolonomicConfiguration_gaugeAuxiliary_origin]

private theorem profileCurrent_gaugeAuxiliary_origin_eq_recentered
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (constitutiveAt :
      diracDualFormNativeConstitutiveAuxiliaryField source current contact =
        current.gaugeAuxiliary contact) :
    holonomicP286GaugeAuxiliaryCoordinate
        (ProfileCurrent source current contact) 0 =
      holonomicP286GaugeAuxiliaryCoordinate
        (RecenteredCurrent current contact) 0 := by
  have recenteredConstitutive :
      diracDualFormNativeConstitutiveAuxiliaryField source
          (RecenteredCurrent current contact) 0 =
        (RecenteredCurrent current contact).gaugeAuxiliary 0 := by
    unfold diracDualFormNativeConstitutiveAuxiliaryField
    rw [fullyRecenterHolonomicConfiguration_coframe_origin,
      fullyRecenter_gaugeCurvature_origin current contact,
      fullyRecenterHolonomicConfiguration_gaugeAuxiliary_origin]
    exact constitutiveAt
  funext pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
  unfold ProfileCurrent completeJointScalarSecondJetCurrent
  rw [genericDiracDualScalarSecondJetActionResponse_gaugeAuxiliary]
  unfold completeJointRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
  change
    p286CoordinateEquiv
        (diracDualFormNativeConstitutiveAuxiliaryField source
          (RestartedCurrent source current contact) 0 pair) =
      p286CoordinateEquiv
        ((RecenteredCurrent current contact).gaugeAuxiliary 0 pair)
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  rw [holonomicGaugeCurvature_eq_of_connection_eq
    (RestartedCurrent source current contact)
    (RecenteredCurrent current contact)
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
      source (RecenteredCurrent current contact)) 0]
  exact congrArg p286CoordinateEquiv
    (congrFun recenteredConstitutive pair)

/-- Transport the complete-joint P286 required exterior profile to the direct
action read on the same current's fully recentered occurrence.

The constitutive premise states that the supplied current is already in the
live P286 constitutive image at `contact`.  It is consumed only to show that
the repaired constitutive write preserves the auxiliary datum read by the
profile; this theorem does not generate or install that datum.  No smoothness
or differentiability receipt is required: recentering uses Lean's total
Fréchet derivative, and the scalar quadratic write preserves the origin first
jet in both its differentiable and non-differentiable branches. -/
theorem
    completeJointP286RequiredExteriorProfile_eq_fullyRecenter_of_constitutiveAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (constitutiveAt :
      diracDualFormNativeConstitutiveAuxiliaryField source current contact =
        current.gaugeAuxiliary contact) :
    completeJointP286RequiredExteriorProfile source current contact =
      formNativeCurrentP286RequiredExteriorDerivative source
        (fullyRecenterHolonomicConfiguration current contact) := by
  rw [completeJointP286RequiredExteriorProfile,
    sourceActionGeneratedDiracDualCompleteJointProfiles_p286RequiredExteriorDerivative]
  apply
    formNativeCurrentP286RequiredExteriorDerivative_eq_of_originActionData_eq
  · rfl
  · rfl
  · exact
      profileCurrent_gaugeAuxiliary_origin_eq_recentered
        source current contact constitutiveAt
  · simp [completeJointScalarSecondJetCurrent,
      completeJointRepairedConstitutiveCurrent,
      completeJointGeneratedProfileRestartCurrent]
  · exact
      profileCurrent_scalarCovariantDerivative_origin_eq_recentered
        source current contact
  · unfold completeJointScalarSecondJetCurrent
    rw [genericDiracDualScalarSecondJetActionResponse_matter]
    unfold completeJointRepairedConstitutiveCurrent
      diracDualFormNativeRepairedConstitutiveWrittenCurrent
      diracDualFormNativeRepairedMatterWrittenCurrent
      actionGeneratedDiracDualRepairedMatterJointResponseActual
    rw [
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter,
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]
    rfl
  · unfold completeJointScalarSecondJetCurrent
    rw [genericDiracDualScalarSecondJetActionResponse_conjugateMatter]
    unfold completeJointRepairedConstitutiveCurrent
      diracDualFormNativeRepairedConstitutiveWrittenCurrent
      diracDualFormNativeRepairedMatterWrittenCurrent
      actionGeneratedDiracDualRepairedMatterJointResponseActual
    rw [
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]
    rfl

/-- Direct pointwise corollary of complete-joint profile naturality.  Under
the live constitutive equality at the selected occurrence, the generated
profile reads exactly `J_charged - [A,B]` from the original current there.
This remains an action readout, not a field producer. -/
theorem
    completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (constitutiveAt :
      diracDualFormNativeConstitutiveAuxiliaryField source current contact =
        current.gaugeAuxiliary contact) :
    completeJointP286RequiredExteriorProfile source current contact =
      pointwiseDirectP286RequiredExteriorDerivative source current contact := by
  rw [
    completeJointP286RequiredExteriorProfile_eq_fullyRecenter_of_constitutiveAt
      source current contact constitutiveAt,
    formNativeCurrentP286RequiredExteriorDerivative_fullyRecenter_eq_pointwiseDirect]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
