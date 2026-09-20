import H0mework.Realization.Reflexive.StatefulRead
import H0mework.Physics.JointVariation.ResponseOperator

/-!
# Local origin acceptance for the complete joint response

The complete joint operator is already a source/current-only producer.  This
module supplies its fixed-contact acceptance mouths without requiring a
globally smooth arbitrary current.  The matter hypotheses below are exactly
the local differentiability needed to read the two affine time writes, while
the Lorentz theorem uses only the produced coframe jet and the already
source-generated Cartan connection at the common contact.

No Euler residual, support coordinate, target derivative, branch, or
zero-fiber witness is accepted by the operator or by these readouts.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionResponseOperatorOriginAcceptance

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCartanTangentSimplicityResponse
open StageNineCartanTorsionThreeFormCoordinates
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineCoframeFirstJet
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineIIPlusRestriction
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation
open StageNineScalarVariation

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Typed four-leg dependency trace -/

/-- The four action-owned writes used by the complete local product. -/
inductive CompleteJointLocalLeg where
  | M
  | S
  | P
  | E
  deriving DecidableEq

/-- Apply one native action leg to the current supplied to that leg. -/
def CompleteJointLocalLeg.write
    (leg : CompleteJointLocalLeg)
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  match leg with
  | .M => completeJointRepairedConstitutiveCurrent source current
  | .S => genericDiracDualScalarSecondJetActionResponse source current
  | .P => formNativeCurrentP286CompleteActionResponseOperator source current
  | .E => sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      source current

/-- One typed action event: read the entire joint residual of the supplied
current at the fixed source/contact, then apply this leg's native write. -/
def CompleteJointLocalLeg.event
    (leg : CompleteJointLocalLeg)
    (source : SmoothUnifiedSource)
    (point : BasePoint) :
    ReflexiveQuery StageNineHolonomicConfiguration
      DiracDualFormNativePointwiseJointResidualCarrier where
  read := fun current =>
    diracDualFormNativePointwiseJointResidual source current point
  write := leg.write source

/-- The downstream read of the native write.  This is an event readout, not
an endpoint constructor. -/
def CompleteJointLocalLeg.readAfterWrite
    (leg : CompleteJointLocalLeg)
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (current : StageNineHolonomicConfiguration) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  (leg.event source point).read ((leg.event source point).write current)

theorem CompleteJointLocalLeg.readAfterWrite_eq
    (leg : CompleteJointLocalLeg)
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (current : StageNineHolonomicConfiguration) :
    leg.readAfterWrite source point current =
      diracDualFormNativePointwiseJointResidual source
        (leg.write source current) point :=
  rfl

/-- Five canonical contacts of the dependency-ordered write. -/
inductive CompleteJointLocalTrace where
  | C0
  | C1
  | C2
  | C3
  | C4
  deriving DecidableEq

/-- The trace is computed only from `(source,current)` and the four native
writes.  It accepts no supplied intermediate or output configuration. -/
def completeJointLocalTrace
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    CompleteJointLocalTrace → StageNineHolonomicConfiguration
  | .C0 => current
  | .C1 => CompleteJointLocalLeg.write .M source current
  | .C2 => CompleteJointLocalLeg.write .S source
      (CompleteJointLocalLeg.write .M source current)
  | .C3 => CompleteJointLocalLeg.write .P source
      (CompleteJointLocalLeg.write .S source
        (CompleteJointLocalLeg.write .M source current))
  | .C4 => CompleteJointLocalLeg.write .E source
      (CompleteJointLocalLeg.write .P source
        (CompleteJointLocalLeg.write .S source
          (CompleteJointLocalLeg.write .M source current)))

@[simp] theorem completeJointLocalTrace_C1
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    completeJointLocalTrace source current .C1 =
      completeJointRepairedConstitutiveCurrent source current :=
  rfl

@[simp] theorem completeJointLocalTrace_C2
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    completeJointLocalTrace source current .C2 =
      completeJointScalarSecondJetCurrent source current :=
  rfl

@[simp] theorem completeJointLocalTrace_C3
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    completeJointLocalTrace source current .C3 =
      completeJointPreECCurrent source current :=
  rfl

@[simp] theorem completeJointLocalTrace_C4
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    completeJointLocalTrace source current .C4 =
      sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current :=
  rfl

/-- The two later legs retain the whole scalar field written at `C2`. -/
theorem completeJointLocalTrace_C4_scalar_eq_C2
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointLocalTrace source current .C4).scalar =
      (completeJointLocalTrace source current .C2).scalar :=
  rfl

/-- The three later legs retain the whole matter field written at `C1`. -/
theorem completeJointLocalTrace_C4_matter_eq_C1
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointLocalTrace source current .C4).matter =
      (completeJointLocalTrace source current .C1).matter :=
  rfl

private theorem completeJointFinal_coframe_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).coframe =
      (completeJointScalarSecondJetCurrent source current).coframe := by
  simp [completeJointScalarSecondJetCurrent]

private theorem completeJointFinal_gaugeConnection_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).gaugeConnection =
      (completeJointScalarSecondJetCurrent source current).gaugeConnection := by
  simp [completeJointScalarSecondJetCurrent]

private theorem completeJointFinal_scalar_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).scalar =
      (completeJointScalarSecondJetCurrent source current).scalar :=
  sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_scalar
    source current

private theorem completeJointFinal_matter_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).matter =
      (completeJointScalarSecondJetCurrent source current).matter := by
  simp [completeJointScalarSecondJetCurrent]

private theorem completeJointFinal_conjugateMatter_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).conjugateMatter =
      (completeJointScalarSecondJetCurrent source current).conjugateMatter := by
  simp [completeJointScalarSecondJetCurrent]

private theorem completeJointFinal_scalarCovariantDerivative_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicScalarCovariantDerivative
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current) =
      holonomicScalarCovariantDerivative
        (completeJointScalarSecondJetCurrent source current) := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [completeJointFinal_scalar_eq_scalarStage,
    completeJointFinal_gaugeConnection_eq_scalarStage]

private theorem completeJointFinal_scalarMomentum_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction derivativeDirection =
      scalarDifferentialMomentum source
        (completeJointScalarSecondJetCurrent source current)
        direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [completeJointFinal_coframe_eq_scalarStage,
    completeJointFinal_scalarCovariantDerivative_eq_scalarStage]

private theorem completeJointFinal_scalarDivergence_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction =
      scalarDifferentialMomentumDivergence source
        (completeJointScalarSecondJetCurrent source current)
        direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [completeJointFinal_scalarMomentum_eq_scalarStage]

private theorem completeJointFinal_scalarAlgebraic_eq_scalarStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarAlgebraicDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction point =
      diracDualScalarAlgebraicDirectionalCoefficient source
        (completeJointScalarSecondJetCurrent source current)
        direction point := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection generatedVolumeDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  simp only [toContinuumPointField]
  rw [completeJointFinal_coframe_eq_scalarStage,
    completeJointFinal_scalarCovariantDerivative_eq_scalarStage,
    completeJointFinal_gaugeConnection_eq_scalarStage,
    completeJointFinal_scalar_eq_scalarStage,
    completeJointFinal_matter_eq_scalarStage,
    completeJointFinal_conjugateMatter_eq_scalarStage]

/-- The scalar Euler reader on the final contact is literally the reader on
the scalar-write contact: the P286 and EC legs touch none of its dependencies. -/
theorem completeJointLocalTrace_C4_scalarResidual_origin_eq_C2
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativePointwiseJointResidual source
        (completeJointLocalTrace source current .C4) 0).scalar =
      (diracDualFormNativePointwiseJointResidual source
        (completeJointLocalTrace source current .C2) 0).scalar := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction 0 =
      diracDualScalarEulerLagrangeDirectionalCoefficient source
        (completeJointScalarSecondJetCurrent source current) direction 0
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [completeJointFinal_scalarAlgebraic_eq_scalarStage,
    congrFun
      (completeJointFinal_scalarDivergence_eq_scalarStage source current
        direction) 0]

private theorem completeJointFinal_coframe_eq_repairedStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).coframe =
      (completeJointRepairedConstitutiveCurrent source current).coframe := by
  simp

private theorem completeJointFinal_conjugateMatter_eq_repairedStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).conjugateMatter =
      (completeJointRepairedConstitutiveCurrent source current
        ).conjugateMatter :=
  sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_conjugateMatter
    source current

private theorem completeJointFinal_gaugeConnection_eq_repairedStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).gaugeConnection =
      (completeJointRepairedConstitutiveCurrent source current
        ).gaugeConnection := by
  simp

private theorem completeJointFinal_connection_origin_eq_repairedStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).gravityConnection 0 =
      (completeJointRepairedConstitutiveCurrent source current
        ).gravityConnection 0 := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_connection_zero,
    completeJointRepairedConstitutiveCurrent_gravityConnection]

private theorem completeJointFinal_scalar_origin_eq_repairedStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current).scalar 0 =
      (completeJointRepairedConstitutiveCurrent source current).scalar 0 := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_scalar_origin,
    completeJointRepairedConstitutiveCurrent_scalar]

private theorem completeJointFinal_matterMomentum_eq_repairedStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction derivativeDirection =
      matterDifferentialMomentum source
        (completeJointRepairedConstitutiveCurrent source current)
        direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [completeJointFinal_coframe_eq_repairedStage,
    completeJointFinal_conjugateMatter_eq_repairedStage]

private theorem completeJointFinal_matterDivergence_eq_repairedStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction =
      matterDifferentialMomentumDivergence source
        (completeJointRepairedConstitutiveCurrent source current)
        direction := by
  funext point
  unfold matterDifferentialMomentumDivergence
  simp_rw [completeJointFinal_matterMomentum_eq_repairedStage]

private theorem completeJointFinal_matterAlgebraic_origin_eq_repairedStage
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient source
        (completeJointRepairedConstitutiveCurrent source current)
        direction 0 := by
  have variationEq :
      holonomicMatterVariationAlgebraicDirection
          (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
            source current)
          direction 0 =
        holonomicMatterVariationAlgebraicDirection
          (completeJointRepairedConstitutiveCurrent source current)
          direction 0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [completeJointFinal_connection_origin_eq_repairedStage,
      completeJointFinal_gaugeConnection_eq_repairedStage]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [completeJointFinal_coframe_eq_repairedStage,
    completeJointFinal_scalar_origin_eq_repairedStage,
    completeJointFinal_conjugateMatter_eq_repairedStage, variationEq]

/-- The final matter Euler reader is the same read-after-write value as at
the repaired-matter contact.  Scalar, P286, and EC writes preserve precisely
the whole-field/contact dependencies of this origin coefficient. -/
theorem completeJointLocalTrace_C4_matterResidual_origin_eq_C1
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativePointwiseJointResidual source
        (completeJointLocalTrace source current .C4) 0).matter =
      (diracDualFormNativePointwiseJointResidual source
        (completeJointLocalTrace source current .C1) 0).matter := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction 0 =
      diracDualMatterEulerLagrangeDirectionalCoefficient source
        (completeJointRepairedConstitutiveCurrent source current) direction 0
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [completeJointFinal_matterAlgebraic_origin_eq_repairedStage,
    congrFun
      (completeJointFinal_matterDivergence_eq_repairedStage source current
        direction) 0]

/-! ## The two local affine matter writes -/

private theorem
    installMatterLinearTimeResponse_matterCoordinateDerivative_origin_of_differentiableAt
    (configuration : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (configuration.matter point)) 0)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((installMatterLinearTimeResponse configuration response).matter
              point))
        0 direction =
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (configuration.matter point))
          0 direction +
        if direction = canonicalLorentzianTimeDirection then
          matterCoordinateEquiv response
        else
          0 := by
  have responseDifferentiable : DifferentiableAt ℝ
      (matterLinearTimeCoordinateWrite response) 0 :=
    ((matterLinearTimeCoordinateWrite_contDiff response).differentiable
      (by simp)).differentiableAt
  unfold fieldDirectionalDerivative
  rw [show
    (fun point =>
      matterCoordinateEquiv
        ((installMatterLinearTimeResponse configuration response).matter
          point)) =
      (fun point => matterCoordinateEquiv (configuration.matter point)) +
        matterLinearTimeCoordinateWrite response by
    funext point
    exact installMatterLinearTimeResponse_matter_coordinate
      configuration response point]
  rw [fderiv_add matterDifferentiable responseDifferentiable, add_apply]
  change
    _ + fieldDirectionalDerivative
          (matterLinearTimeCoordinateWrite response) 0 direction = _
  rw [matterLinearTimeCoordinateWrite_directionalDerivative]

private theorem
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin_of_differentiableAt
    (configuration : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (configuration.matter point)) 0)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (installMatterLinearTimeResponse configuration response) 0 direction =
      holonomicMatterCovariantDerivative configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then response else 0 := by
  unfold holonomicMatterCovariantDerivative
  rw [
    installMatterLinearTimeResponse_matterCoordinateDerivative_origin_of_differentiableAt
      configuration matterDifferentiable response direction]
  split_ifs <;>
    simp only [map_add, matterCoordinateEquiv.symm_apply_apply, map_zero,
      installMatterLinearTimeResponse_gravityConnection,
      installMatterLinearTimeResponse_gaugeConnection,
      installMatterLinearTimeResponse_matter_origin] <;>
    module

private theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw_of_matterDifferentiableAt
    (configuration : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (configuration.matter point)) 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
        configuration)
      0
      (holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  have spatialDerivative (direction : Fin 3) :
      holonomicMatterCovariantDerivative
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            configuration)
          0 direction.succ =
        holonomicMatterCovariantDerivative configuration 0 direction.succ := by
    unfold actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    rw [
      holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin_of_differentiableAt
        configuration matterDifferentiable
        (diracDualCurrentCoframeMatterTimeResponseWrite configuration)]
    simp [canonicalLorentzianTimeDirection]
  have timeDerivative :
      holonomicMatterCovariantDerivative
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            configuration)
          0 canonicalLorentzianTimeDirection =
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          configuration 0 := by
    unfold actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    rw [
      holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin_of_differentiableAt
        configuration matterDifferentiable
        (diracDualCurrentCoframeMatterTimeResponseWrite configuration)]
    simp only [if_pos]
    unfold diracDualCurrentCoframeMatterTimeResponseWrite
    abel
  have knownVector :
      holonomicDiracDualCurrentCoframeMatterKnownVector
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            configuration)
          0 =
        holonomicDiracDualCurrentCoframeMatterKnownVector configuration 0 := by
    unfold holonomicDiracDualCurrentCoframeMatterKnownVector
    rw [
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe,
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_scalar,
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]
    simp_rw [spatialDerivative]
  have generatedLaw :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      configuration 0 noncharacteristic
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generatedLaw ⊢
  rw [
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe,
    knownVector, timeDerivative]
  exact generatedLaw

private theorem
    holonomicConjugateMatterDerivativeCoordinates_installConjugateMatterLinearTimeResponse_origin_of_differentiableAt
    (configuration : StageNineHolonomicConfiguration)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (installConjugateMatterLinearTimeResponse configuration response)
        0 direction =
      holonomicConjugateMatterDerivativeCoordinates configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then
          matterDualCoordinates response
        else
          0 := by
  have responseDifferentiable : DifferentiableAt ℝ
      (conjugateMatterLinearTimeCoordinateWrite response) 0 :=
    ((conjugateMatterLinearTimeCoordinateWrite_contDiff response).differentiable
      (by simp)).differentiableAt
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  rw [show
    holonomicConjugateMatterCoordinates
        (installConjugateMatterLinearTimeResponse configuration response) =
      holonomicConjugateMatterCoordinates configuration +
        conjugateMatterLinearTimeCoordinateWrite response by
    funext point
    exact
      installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates
        configuration response point]
  rw [fderiv_add coordinateDifferentiable responseDifferentiable, add_apply]
  change
    _ + fieldDirectionalDerivative
          (conjugateMatterLinearTimeCoordinateWrite response) 0 direction = _
  rw [conjugateMatterLinearTimeCoordinateWrite_directionalDerivative]

private theorem
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin_of_differentiableAt
    (configuration : StageNineHolonomicConfiguration)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (installConjugateMatterLinearTimeResponse configuration response)
        0 direction =
      holonomicConjugateMatterDerivativeDual configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then response else 0 := by
  unfold holonomicConjugateMatterDerivativeDual
  rw [
    holonomicConjugateMatterDerivativeCoordinates_installConjugateMatterLinearTimeResponse_origin_of_differentiableAt
      configuration coordinateDifferentiable response direction]
  split_ifs <;>
    simp [matterDualOfCoordinates_add,
      matterDualOfCoordinates_surjective]

/-- The live-coframe adjoint origin writer needs only differentiability of
the supplied conjugate-matter coordinates at the written occurrence.  The
constructor still selects its response from the action velocity; no smooth
global-current certificate or equation readout is an input. -/
theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw_of_coordinateDifferentiableAt
    (configuration : StageNineHolonomicConfiguration)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) 0)
    (nondegenerate : Matrix.det (configuration.coframe 0) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
        configuration)
      0
      (holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  have spatialTransport :
      holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
          (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
            configuration)
          0 =
        holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
          configuration 0 := by
    unfold
      holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
    rw [
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_toContinuumPointField_origin,
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_coframe]
    apply Finset.sum_congr rfl
    intro direction _
    unfold actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    rw [
      holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin_of_differentiableAt
        configuration coordinateDifferentiable
        (liveCoframeConjugateMatterTimeResponseWrite configuration)
        direction.succ]
    have spatialNe :
        direction.succ ≠ canonicalLorentzianTimeDirection := by
      fin_cases direction <;> decide
    simp [spatialNe]
  have knownDual :
      holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
            configuration)
          0 =
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          configuration 0 := by
    unfold holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
    rw [
      holonomicDiracDualLiveCoframeAlgebraicDual_actionGenerated_origin,
      spatialTransport,
      holonomicLiveCoframeSpatialPrincipalDriftCoordinates_actionGenerated_origin,
      holonomicLiveCoframeTemporalPrincipalDriftCoordinates_actionGenerated_origin]
  have actionVelocity :
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
            configuration)
          0 =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          configuration 0 := by
    unfold holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
    rw [
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_toContinuumPointField_origin,
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_coframe,
      knownDual]
  have timeDerivative :
      holonomicConjugateMatterDerivativeDual
          (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
            configuration)
          0 canonicalLorentzianTimeDirection =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          configuration 0 := by
    unfold
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    rw [
      holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin_of_differentiableAt
        configuration coordinateDifferentiable
        (liveCoframeConjugateMatterTimeResponseWrite configuration)
        canonicalLorentzianTimeDirection]
    simp [liveCoframeConjugateMatterTimeResponseWrite]
  have generatedLaw :=
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
      (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
        configuration)
      0
      (by simpa using nondegenerate)
      (by simpa using noncharacteristic)
  rw [timeDerivative, ← actionVelocity]
  exact generatedLaw

/-! ## Local action-law readback on the complete output -/

theorem
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_primalActionLaw_of_matterDifferentiableAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current)
      0
      (holonomicMatterCovariantDerivative
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        0 canonicalLorentzianTimeDirection) := by
  have firstLaw :=
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw_of_matterDifferentiableAt
      current matterDifferentiable noncharacteristic
  have repairedLaw :
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
        (completeJointRepairedConstitutiveCurrent source current)
        0
        (holonomicMatterCovariantDerivative
          (completeJointRepairedConstitutiveCurrent source current)
          0 canonicalLorentzianTimeDirection) := by
    simpa [completeJointRepairedConstitutiveCurrent,
      diracDualFormNativeRepairedConstitutiveWrittenCurrent,
      diracDualFormNativeRepairedMatterWrittenCurrent,
      actionGeneratedDiracDualRepairedMatterJointResponseActual,
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw,
      holonomicDiracDualCurrentCoframeMatterKnownVector,
      holonomicMatterCovariantDerivative] using firstLaw
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at repairedLaw ⊢
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector at repairedLaw ⊢
  have derivativeEq :
      ∀ direction,
        holonomicMatterCovariantDerivative
            (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
              source current)
            0 direction =
          holonomicMatterCovariantDerivative
            (completeJointRepairedConstitutiveCurrent source current)
            0 direction := by
    intro direction
    unfold holonomicMatterCovariantDerivative
    rw [
      sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_matter,
      sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_connection_zero,
      sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_gaugeConnection,
      completeJointRepairedConstitutiveCurrent_gravityConnection,
      completeJointRepairedConstitutiveCurrent_gaugeConnection]
  rw [completeJointRepairedConstitutiveCurrent_coframe,
    completeJointRepairedConstitutiveCurrent_scalar] at repairedLaw
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_coframe,
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_scalar_origin,
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_matter]
  simp_rw [derivativeEq]
  exact repairedLaw

theorem
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_liveAdjointActionLaw_of_coordinateDifferentiableAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        source current)
      0
      (holonomicConjugateMatterDerivativeDual
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        0 canonicalLorentzianTimeDirection) := by
  let primal :=
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual current
  have primalCoordinateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates primal) 0 := by
    change DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0
    exact coordinateDifferentiable
  have firstLaw :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw_of_coordinateDifferentiableAt
      primal primalCoordinateDifferentiable
      (by simpa [primal] using nondegenerate)
      (by simpa [primal] using noncharacteristic)
  have matterJointLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
        (diracDualFormNativeRepairedMatterWrittenCurrent current)
        0
        (holonomicConjugateMatterDerivativeDual
          (diracDualFormNativeRepairedMatterWrittenCurrent current)
          0 canonicalLorentzianTimeDirection) := by
    simpa [primal, diracDualFormNativeRepairedMatterWrittenCurrent,
      actionGeneratedDiracDualRepairedMatterJointResponseActual] using firstLaw
  have repairedLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
        (completeJointRepairedConstitutiveCurrent source current)
        0
        (holonomicConjugateMatterDerivativeDual
          (completeJointRepairedConstitutiveCurrent source current)
          0 canonicalLorentzianTimeDirection) := by
    simpa [completeJointRepairedConstitutiveCurrent] using
      diracDualFormNativeRepairedConstitutiveWrittenCurrent_liveAdjointActionLaw_of_matterLaw
        source current matterJointLaw
  exact
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_liveAdjointActionLaw_of_repairedLaw
      source current repairedLaw

theorem
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_matterVector_origin_zero_of_matterDifferentiableAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    generatedContinuumDiracDualMatterVector source 0 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
            source current) 0) =
      0 :=
  generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    source
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
      source current)
    0
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_primalActionLaw_of_matterDifferentiableAt
      source current matterDifferentiable noncharacteristic)

theorem
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_conjugateMatterResidual_origin_zero_of_matterDifferentiableAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    (fun direction =>
      diracDualConjugateMatterDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        direction 0) =
      0 := by
  funext direction
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_matterVector_origin_zero_of_matterDifferentiableAt
      source current matterDifferentiable noncharacteristic]
  simp

/-! ## Lorentz readback from the same produced Cartan contact -/

theorem
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_lorentzEulerThreeForm_origin_zero_of_coframeContDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeSmooth : ContDiff ℝ ∞ current.coframe)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          source current)
        0 =
      0 := by
  let final :=
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
      source current
  have finalRestricted :
      restrictHolonomicConfigurationToIIPlus final = final := by
    apply StageNineHolonomicConfiguration.ext <;> rfl
  have finalCoframeSmooth : ContDiff ℝ ∞ final.coframe := by
    simpa [final] using coframeSmooth
  have finalNondegenerate : Matrix.det (final.coframe 0) ≠ 0 := by
    simpa [final] using nondegenerate
  have finalSelfGenerated :
      final.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source final 0 := by
    simpa [final] using
      (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_connectionSelfGenerated_zero
        source current selfGenerated)
  have finalLorentzSkew : LorentzSkew (final.gravityConnection 0) := by
    rw [finalSelfGenerated]
    exact diracDualFormNativeActionCartanConnectionAt_lorentzSkew
      source final 0 finalNondegenerate
  have torsionSpin :
      cartanTorsionThreeForm (final.coframe 0)
          (actualPointwiseCartanTorsionTwoForm
            (holonomicCoframeFirstJetAt final.coframe 0)
            (final.gravityConnection 0)) =
        diracDualFormNativeActionSpinResponseAt source final 0 := by
    rw [finalSelfGenerated]
    exact diracDualFormNativeActionCartanConnectionAt_generates_spinResponse
      source final 0 finalNondegenerate
  apply
    (holonomicFormNativeLorentzEulerThreeForm_eq_zero_iff_current source 0
      final 0).2
  calc
    holonomicGravityAuxiliaryExteriorCovariantDerivative final 0 =
        holonomicGravityAuxiliaryExteriorCovariantDerivative
          (restrictHolonomicConfigurationToIIPlus final) 0 := by
      rw [finalRestricted]
    _ = internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm (final.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt final.coframe 0)
              (final.gravityConnection 0))) := by
      change
        pointwisePhysicalBivectorExteriorCovariantDerivative
            (final.gravityConnection 0)
            (holonomicGravityAuxiliaryJet
              (restrictHolonomicConfigurationToIIPlus final) 0) = _
      rw [holonomicGravityAuxiliaryJet_restrictToIIPlus_of_coframeContDiff
        final finalCoframeSmooth 0]
      exact
        pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_torsionCoframe
          (holonomicCoframeFirstJetAt final.coframe 0)
          (final.gravityConnection 0) finalLorentzSkew
    _ = diracDualFormNativeActionSpinResponseAt source final 0 := by
      rw [← cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
      exact torsionSpin
    _ = formNativePhysicalSpinCurrentThreeForm source 0 0
          (toContinuumPointField final 0) := by
      unfold diracDualFormNativeActionSpinResponseAt
      rw [finalRestricted]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionResponseOperatorOriginAcceptance
