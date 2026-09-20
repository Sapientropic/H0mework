import H0mework.Physics.JointVariation.GeneratedProfilesFixed
import H0mework.Physics.RecenteredJoint.FixedFullJointConnectionOriginRegularity
import H0mework.Physics.FinalJoint.FixedRepairedConstitutiveCartanLiveDomainRegularity
import H0mework.Physics.RepairedAction.ActionSpatialSectionAdjointFirstJet

/-!
# Fixed P506/L0 complete-joint profile regularity

The complete-joint spacetime write already generates its contact profiles
from one fixed source and current.  This module proves spatial regularity of
those generated profiles from their fixed-lineage normal forms.  It accepts
no profile value, residual, seam, branch, or smoothness receipt as producer
input.

Scalar acceleration regularity is kept in its owning scalar module.  The
results here are readouts of the source/current-only generated bundle and do
not assert an all-point zero fiber.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506Regularity

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeGravityGaugeRegularity
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonRepairedConstitutiveCartanLiveDomainRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointResponseRegularity
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCoframeScalarMatterRegularity
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterNormalForm
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance completeJointRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  constitutiveRegularityP286ModuleFinite

local instance completeJointRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  constitutiveRegularityP286CoordinateIndexFintype

local instance completeJointRegularityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  constitutiveRegularityP286CoordinateIsTopologicalAddGroup

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- A fixed global field used only to expose the smooth spatial dependence
of the Cartan origin read by the matter writers.  Its connection is the
already generated constant restart origin; no profile is supplied to it. -/
private def fixedP506L0CompleteJointCartanOriginProfileActual :
    StageNineHolonomicConfiguration :=
  { FixedInput with
    gravityConnection := fun _ =>
      (fixedP506L0CartanRestartActual 0).gravityConnection 0 }

private theorem fixedP506L0CompleteJointCartanOriginProfileActual_smooth :
    fixedP506L0CompleteJointCartanOriginProfileActual.Smooth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
  · intro formDirection internalOut internalIn
    exact contDiff_const
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.2

private theorem fderiv_canonicalZeroSlice_spatial_local
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V) (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (fieldDifferentiableAt :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint 0 space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint 0) space
        (canonicalSpatialCoordinateDirection axis) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  have derivative := fieldDifferentiableAt.hasFDerivAt.comp space
    (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

private theorem fixedInput_gaugeConnectionCoordinate_zeroSlice_fderiv_axis_zero
    (axis : Fin 3) :
    fderiv ℝ
        (holonomicP286GaugeConnectionCoordinate FixedInput ∘
          canonicalCauchySlicePoint 0)
        0 (canonicalSpatialCoordinateDirection axis) =
      0 := by
  let field : StageNineSpatialPoint → P286GaugeOneForm :=
    holonomicP286GaugeConnectionCoordinate FixedInput ∘
      canonicalCauchySlicePoint 0
  have fieldDifferentiable : DifferentiableAt ℝ field 0 :=
    ((holonomicP286GaugeConnectionCoordinate_contDiff FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth).comp
        canonicalZeroSlice_contDiff).differentiable (by simp)
      |>.differentiableAt
  funext formDirection
  have derivativeEquality := fderiv_apply fieldDifferentiable formDirection
  have applied := congrArg
    (fun derivative : StageNineSpatialPoint →L[ℝ] P286CoordinateCarrier =>
      derivative (canonicalSpatialCoordinateDirection axis))
    derivativeEquality
  have componentDifferentiable : DifferentiableAt ℝ
      (fun point =>
        holonomicP286GaugeConnectionCoordinate FixedInput point
          formDirection)
      (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) :=
    ((fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
      formDirection).differentiable (by simp)).differentiableAt
  have componentDerivative :=
    fderiv_canonicalZeroSlice_spatial_local
      (fun point =>
        holonomicP286GaugeConnectionCoordinate FixedInput point
          formDirection)
      0 axis componentDifferentiable
  have componentZero :
      fderiv ℝ
          ((fun point =>
            holonomicP286GaugeConnectionCoordinate FixedInput point
              formDirection) ∘ canonicalCauchySlicePoint 0)
          0 (canonicalSpatialCoordinateDirection axis) =
        0 := by
    rw [componentDerivative]
    change
      p286GaugeConnectionCoordinateDerivative FixedInput
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
          axis.succ formDirection =
        0
    rw [show canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 by
      apply PiLp.ext
      intro direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]]
    exact
      fixedP506FormNativeJointActionSolvedSuccessor_connectionSpatialOneJet_zero
        axis formDirection
  simpa only [field, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Pi.zero_apply] using
      applied.symm.trans componentZero

/-- The source-written P286 connection has zero spatial derivative at the
canonical zero-slice origin.  This is the public derivative mouth consumed
by the fixed primal/adjoint action profiles below. -/
theorem
    fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnectionCoordinate_zeroSlice_fderiv_axis_zero
    (axis : Fin 3) :
    fderiv ℝ
        (holonomicP286GaugeConnectionCoordinate
            FixedP506FormNativeJointActionSolvedSuccessor ∘
          canonicalCauchySlicePoint 0)
        0 (canonicalSpatialCoordinateDirection axis) =
      0 := by
  simpa [FixedInput] using
    fixedInput_gaugeConnectionCoordinate_zeroSlice_fderiv_axis_zero axis

private theorem canonicalSpatialContactTranslation_zero_local
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  unfold canonicalSpatialContactTranslation
  exact add_zero _

private theorem canonicalSpatialContactTranslation_hasFDerivAt_local
    (space : StageNineSpatialPoint) :
    HasFDerivAt (canonicalSpatialContactTranslation space)
      (ContinuousLinearMap.id ℝ BasePoint) 0 := by
  unfold canonicalSpatialContactTranslation
  fun_prop

private theorem fixedP506L0CartanRestart_matterCoordinateDerivative_origin
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((fixedP506L0CartanRestartActual space).matter point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (FixedInput.matter point))
        (canonicalCauchySlicePoint 0 space) direction := by
  let coordinateField : BasePoint → MatterCoordinateCarrier :=
    fun point => matterCoordinateEquiv (FixedInput.matter point)
  have fieldDifferentiable :
      DifferentiableAt ℝ coordinateField
        (canonicalSpatialContactTranslation space 0) := by
    rw [canonicalSpatialContactTranslation_zero_local]
    exact
      ((fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
        ).differentiable (by simp)).differentiableAt
  have composed := fieldDifferentiable.hasFDerivAt.comp 0
    (canonicalSpatialContactTranslation_hasFDerivAt_local space)
  unfold fieldDirectionalDerivative
  change
    fderiv ℝ
        (coordinateField ∘ canonicalSpatialContactTranslation space)
        0 (coordinateDirection direction) =
      fderiv ℝ coordinateField (canonicalCauchySlicePoint 0 space)
        (coordinateDirection direction)
  rw [composed.fderiv]
  simp [canonicalSpatialContactTranslation_zero_local]

private theorem fixedP506L0CartanRestart_matterCovariantDerivative_origin
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (fixedP506L0CartanRestartActual space) 0 direction =
      holonomicMatterCovariantDerivative
        fixedP506L0CompleteJointCartanOriginProfileActual
        (canonicalCauchySlicePoint 0 space) direction := by
  have connectionEq :
      (fixedP506L0CartanRestartActual space).gravityConnection 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.gravityConnection
          (canonicalCauchySlicePoint 0 space) := by
    change
      (fixedP506L0CartanRestartActual space).gravityConnection 0 =
        (fixedP506L0CartanRestartActual 0).gravityConnection 0
    exact fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero space
  have matterEq :
      (fixedP506L0CartanRestartActual space).matter 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.matter
          (canonicalCauchySlicePoint 0 space) := by
    change
      FixedInput.matter (canonicalSpatialContactTranslation space 0) =
        FixedInput.matter (canonicalCauchySlicePoint 0 space)
    rw [canonicalSpatialContactTranslation_zero_local]
  have gaugeEq :
      (fixedP506L0CartanRestartActual space).gaugeConnection 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.gaugeConnection
          (canonicalCauchySlicePoint 0 space) := by
    change
      FixedInput.gaugeConnection (canonicalSpatialContactTranslation space 0) =
        FixedInput.gaugeConnection (canonicalCauchySlicePoint 0 space)
    rw [canonicalSpatialContactTranslation_zero_local]
  unfold holonomicMatterCovariantDerivative
  rw [fixedP506L0CartanRestart_matterCoordinateDerivative_origin]
  rw [connectionEq, matterEq, gaugeEq]
  rfl

private theorem fixedP506L0CartanRestart_coframe_origin
    (space : StageNineSpatialPoint) :
    (fixedP506L0CartanRestartActual space).coframe 0 = 1 := by
  change FixedInput.coframe (canonicalSpatialContactTranslation space 0) = 1
  rw [canonicalSpatialContactTranslation_zero_local]
  exact fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space

private theorem fixedP506L0CartanRestart_knownVector_origin
    (space : StageNineSpatialPoint) :
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (fixedP506L0CartanRestartActual space) 0 =
      holonomicDiracDualIdentityCoframeMatterKnownVector
        fixedP506L0CompleteJointCartanOriginProfileActual
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicDiracDualIdentityCoframeMatterKnownVector
  rw [fixedP506L0CartanRestart_coframe_origin]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp_rw [fixedP506L0CartanRestart_matterCovariantDerivative_origin]
  have scalarEq :
      (fixedP506L0CartanRestartActual space).scalar 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.scalar
          (canonicalCauchySlicePoint 0 space) := by
    change
      FixedInput.scalar (canonicalSpatialContactTranslation space 0) =
        FixedInput.scalar (canonicalCauchySlicePoint 0 space)
    rw [canonicalSpatialContactTranslation_zero_local]
  have matterEq :
      (fixedP506L0CartanRestartActual space).matter 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.matter
          (canonicalCauchySlicePoint 0 space) := by
    change
      FixedInput.matter (canonicalSpatialContactTranslation space 0) =
        FixedInput.matter (canonicalCauchySlicePoint 0 space)
    rw [canonicalSpatialContactTranslation_zero_local]
  rw [scalarEq, matterEq]

/-- Exact fixed-lineage normal form of the primal installer correction. -/
theorem fixedP506L0CompleteJointMatterResponseWrite_normalForm
    (space : StageNineSpatialPoint) :
    diracDualCurrentCoframeMatterTimeResponseWrite
        (fixedP506L0CartanRestartActual space) =
      holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space) -
        matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point => matterCoordinateEquiv (FixedInput.matter point))
            (canonicalCauchySlicePoint 0 space)
            canonicalLorentzianTimeDirection) := by
  unfold diracDualCurrentCoframeMatterTimeResponseWrite
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
  rw [fixedP506L0CartanRestart_coframe_origin,
    fixedP506L0CartanRestart_knownVector_origin,
    currentCoframeMatterTemporalPrincipalInverse_one,
    fixedP506L0CartanRestart_matterCovariantDerivative_origin]
  unfold holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
    holonomicMatterCovariantDerivative
  unfold
    StageNineCurrentCoframeMatterTimeResponse.holonomicMatterConnectionAction
  rw [show
    (fun point =>
      matterCoordinateEquiv
        (fixedP506L0CompleteJointCartanOriginProfileActual.matter point)) =
      fun point => matterCoordinateEquiv (FixedInput.matter point) by rfl]
  module

/-- Public source-field form of the primal correction.  This is the minimal
provenance fold needed by the downstream fixed-current first-jet consumer;
it exposes no new carrier or caller-supplied datum. -/
theorem fixedP506L0CompleteJointMatterResponseWrite_sourceFields
    (space : StageNineSpatialPoint) :
    diracDualCurrentCoframeMatterTimeResponseWrite
        (fixedP506L0CartanRestartActual space) =
      holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
          { FixedP506FormNativeJointActionSolvedSuccessor with
            gravityConnection := fun _ =>
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 }
          (canonicalCauchySlicePoint 0 space) -
        matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point => matterCoordinateEquiv
              (FixedP506FormNativeJointActionSolvedSuccessor.matter point))
            (canonicalCauchySlicePoint 0 space)
            canonicalLorentzianTimeDirection) := by
  simpa [fixedP506L0CompleteJointCartanOriginProfileActual, FixedInput] using
    fixedP506L0CompleteJointMatterResponseWrite_normalForm space

/-- The primal installer correction is smooth in its source-owned spatial
contact. -/
theorem fixedP506L0CompleteJointMatterResponseWrite_contDiff :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      matterCoordinateEquiv
        (diracDualCurrentCoframeMatterTimeResponseWrite
          (fixedP506L0CartanRestartActual space)) := by
  rw [show
    (fun space : StageNineSpatialPoint => matterCoordinateEquiv
      (diracDualCurrentCoframeMatterTimeResponseWrite
        (fixedP506L0CartanRestartActual space))) =
    fun space =>
      matterCoordinateEquiv
          (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
            fixedP506L0CompleteJointCartanOriginProfileActual
            (canonicalCauchySlicePoint 0 space)) -
        fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (FixedInput.matter point))
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection by
      funext space
      rw [fixedP506L0CompleteJointMatterResponseWrite_normalForm, map_sub,
        matterCoordinateEquiv.apply_symm_apply]]
  exact
    ((holonomicDiracDualIdentityCoframeMatterRawTimeVelocity_coordinate_contDiff
      fixedP506L0CompleteJointCartanOriginProfileActual
      fixedP506L0CompleteJointCartanOriginProfileActual_smooth).comp
        canonicalZeroSlice_contDiff).sub
      ((holonomicMatterCoordinateDerivative_contDiff_local FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        canonicalLorentzianTimeDirection).comp canonicalZeroSlice_contDiff)

/-! ## Adjoint installer correction -/

private def fixedP506L0CompleteJointPrimalWrittenContact
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (fixedP506L0CartanRestartActual space)

private theorem fixedInput_coframeFirstJet_zeroSlice_local
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt FixedInput.coframe
        (canonicalCauchySlicePoint 0 space) =
      identityCoframeMatterGeometry := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  simpa [identityCoframeMatterGeometry] using
    fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space

private theorem
    fixedP506L0CompleteJointCartanOriginProfileActual_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        fixedP506L0CompleteJointCartanOriginProfileActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      identityCoframeMatterGeometry := by
  exact fixedInput_coframeFirstJet_zeroSlice_local space

private theorem
    fixedP506L0CompleteJointPrimalWrittenContact_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (fixedP506L0CompleteJointPrimalWrittenContact space).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold fixedP506L0CompleteJointPrimalWrittenContact
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe]
  calc
    holonomicCoframeFirstJetAt
          (fixedP506L0CartanRestartActual space).coframe 0 =
        holonomicCoframeFirstJetAt FixedInput.coframe
          (canonicalCauchySlicePoint 0 space) := by
      apply coframeJet_eq_of_fields_eq
      · change
          FixedInput.coframe (canonicalSpatialContactTranslation space 0) =
            FixedInput.coframe (canonicalCauchySlicePoint 0 space)
        rw [canonicalSpatialContactTranslation_zero_local]
      · funext derivativeDirection internal coordinate
        let component : BasePoint → ℝ :=
          fun point => FixedInput.coframe point internal coordinate
        have fieldDifferentiable :
            DifferentiableAt ℝ component
              (canonicalSpatialContactTranslation space 0) := by
          rw [canonicalSpatialContactTranslation_zero_local]
          exact
            ((fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
              internal coordinate).differentiable (by simp)).differentiableAt
        have composed := fieldDifferentiable.hasFDerivAt.comp 0
          (canonicalSpatialContactTranslation_hasFDerivAt_local space)
        change
          fderiv ℝ
              (component ∘ canonicalSpatialContactTranslation space)
              0 (coordinateDirection derivativeDirection) =
            fderiv ℝ component (canonicalCauchySlicePoint 0 space)
              (coordinateDirection derivativeDirection)
        rw [composed.fderiv]
        simp [canonicalSpatialContactTranslation_zero_local]
    _ = identityCoframeMatterGeometry :=
      fixedInput_coframeFirstJet_zeroSlice_local space

private theorem
    fixedP506L0CompleteJointPrimalWrittenContact_conjugateMatterDerivative_origin
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (fixedP506L0CompleteJointPrimalWrittenContact space) 0 direction =
      holonomicConjugateMatterDerivativeDual
        fixedP506L0CompleteJointCartanOriginProfileActual
        (canonicalCauchySlicePoint 0 space) direction := by
  let coordinateField : BasePoint → MatterCoordinateCarrier :=
    holonomicConjugateMatterCoordinates FixedInput
  have fieldDifferentiable :
      DifferentiableAt ℝ coordinateField
        (canonicalSpatialContactTranslation space 0) := by
    rw [canonicalSpatialContactTranslation_zero_local]
    exact
      ((holonomicConjugateMatterCoordinates_contDiff FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        ).differentiable (by simp)).differentiableAt
  have composed := fieldDifferentiable.hasFDerivAt.comp 0
    (canonicalSpatialContactTranslation_hasFDerivAt_local space)
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  change
    matterDualOfCoordinates
        (fderiv ℝ
          (coordinateField ∘ canonicalSpatialContactTranslation space)
          0 (coordinateDirection direction)) =
      matterDualOfCoordinates
        (fderiv ℝ coordinateField (canonicalCauchySlicePoint 0 space)
          (coordinateDirection direction))
  rw [composed.fderiv]
  simp [canonicalSpatialContactTranslation_zero_local]

private theorem
    fixedP506L0CompleteJointPrimalWrittenContact_identityAdjointVelocity_origin
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        (fixedP506L0CompleteJointPrimalWrittenContact space) 0 =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        fixedP506L0CompleteJointCartanOriginProfileActual
        (canonicalCauchySlicePoint 0 space) := by
  have connectionEq :
      (fixedP506L0CompleteJointPrimalWrittenContact space).gravityConnection 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.gravityConnection
          (canonicalCauchySlicePoint 0 space) := by
    change
      (fixedP506L0CartanRestartActual space).gravityConnection 0 =
        (fixedP506L0CartanRestartActual 0).gravityConnection 0
    exact fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero space
  have gaugeEq :
      (fixedP506L0CompleteJointPrimalWrittenContact space).gaugeConnection 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.gaugeConnection
          (canonicalCauchySlicePoint 0 space) := by
    change
      FixedInput.gaugeConnection (canonicalSpatialContactTranslation space 0) =
        FixedInput.gaugeConnection (canonicalCauchySlicePoint 0 space)
    rw [canonicalSpatialContactTranslation_zero_local]
  have scalarEq :
      (fixedP506L0CompleteJointPrimalWrittenContact space).scalar 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.scalar
          (canonicalCauchySlicePoint 0 space) := by
    change
      FixedInput.scalar (canonicalSpatialContactTranslation space 0) =
        FixedInput.scalar (canonicalCauchySlicePoint 0 space)
    rw [canonicalSpatialContactTranslation_zero_local]
  have conjugateEq :
      (fixedP506L0CompleteJointPrimalWrittenContact space).conjugateMatter 0 =
        fixedP506L0CompleteJointCartanOriginProfileActual.conjugateMatter
          (canonicalCauchySlicePoint 0 space) := by
    change
      FixedInput.conjugateMatter
          (canonicalSpatialContactTranslation space 0) =
        FixedInput.conjugateMatter (canonicalCauchySlicePoint 0 space)
    rw [canonicalSpatialContactTranslation_zero_local]
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  simp_rw [
    fixedP506L0CompleteJointPrimalWrittenContact_conjugateMatterDerivative_origin]
  rw [connectionEq, gaugeEq, scalarEq, conjugateEq]

private theorem
    fixedP506L0CompleteJointPrimalWrittenContact_liveAdjointVelocity_origin
    (space : StageNineSpatialPoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (fixedP506L0CompleteJointPrimalWrittenContact space) 0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        fixedP506L0CompleteJointCartanOriginProfileActual
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (fixedP506L0CompleteJointPrimalWrittenContact space) 0 =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          (fixedP506L0CompleteJointPrimalWrittenContact space) 0 :=
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ (fixedP506L0CompleteJointPrimalWrittenContact_coframeFirstJet_origin
          space)
    _ =
        holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          (fixedP506L0CompleteJointPrimalWrittenContact space) 0 :=
      (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        _ _).symm
    _ =
        holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space) :=
      fixedP506L0CompleteJointPrimalWrittenContact_identityAdjointVelocity_origin
        space
    _ =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space) :=
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        _ _
    _ =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space) :=
      (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _
        (fixedP506L0CompleteJointCartanOriginProfileActual_coframeFirstJet_zeroSlice
          space)).symm

private theorem
    fixedP506L0CompleteJointCartanOriginProfileActual_liveAdjoint_eq_identity
    (space : StageNineSpatialPoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        fixedP506L0CompleteJointCartanOriginProfileActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        fixedP506L0CompleteJointCartanOriginProfileActual
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space) =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space) :=
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _
        (fixedP506L0CompleteJointCartanOriginProfileActual_coframeFirstJet_zeroSlice
          space)
    _ =
        holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space) :=
      (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        _ _).symm

/-- Exact fixed-lineage normal form of the adjoint installer correction. -/
theorem fixedP506L0CompleteJointAdjointResponseWrite_normalForm
    (space : StageNineSpatialPoint) :
    liveCoframeConjugateMatterTimeResponseWrite
        (fixedP506L0CompleteJointPrimalWrittenContact space) =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space) -
        holonomicConjugateMatterDerivativeDual
          fixedP506L0CompleteJointCartanOriginProfileActual
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection := by
  unfold liveCoframeConjugateMatterTimeResponseWrite
  rw [
    fixedP506L0CompleteJointPrimalWrittenContact_liveAdjointVelocity_origin,
    fixedP506L0CompleteJointCartanOriginProfileActual_liveAdjoint_eq_identity,
    fixedP506L0CompleteJointPrimalWrittenContact_conjugateMatterDerivative_origin]

/-- Public source-field form of the independent-adjoint correction, paired
with the same fixed profile as the primal fold above. -/
theorem fixedP506L0CompleteJointAdjointResponseWrite_sourceFields
    (space : StageNineSpatialPoint) :
    liveCoframeConjugateMatterTimeResponseWrite
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual space)) =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          { FixedP506FormNativeJointActionSolvedSuccessor with
            gravityConnection := fun _ =>
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 }
          (canonicalCauchySlicePoint 0 space) -
        holonomicConjugateMatterDerivativeDual
          { FixedP506FormNativeJointActionSolvedSuccessor with
            gravityConnection := fun _ =>
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 }
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection := by
  simpa [fixedP506L0CompleteJointPrimalWrittenContact,
    fixedP506L0CompleteJointCartanOriginProfileActual, FixedInput] using
      fixedP506L0CompleteJointAdjointResponseWrite_normalForm space

private theorem
    fixedP506L0CompleteJointCartanOriginProfileActual_conjugateDerivative_apply_contDiff
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point =>
      holonomicConjugateMatterDerivativeDual
        fixedP506L0CompleteJointCartanOriginProfileActual point direction
        matter := by
  rw [show
    (fun point =>
      holonomicConjugateMatterDerivativeDual
          fixedP506L0CompleteJointCartanOriginProfileActual point direction
          matter) =
      fun point => ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv matter index *
          holonomicConjugateMatterDerivativeCoordinates
            fixedP506L0CompleteJointCartanOriginProfileActual point direction
            index by
    funext point
    exact matterDualOfCoordinates_apply _ _]
  apply ContDiff.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have derivativeCoordinateSmooth : ContDiff ℝ ∞ fun point =>
      holonomicConjugateMatterDerivativeCoordinates
          fixedP506L0CompleteJointCartanOriginProfileActual point direction
          index :=
    (projection.restrictScalars ℝ).contDiff.comp
      (holonomicConjugateMatterDerivativeCoordinates_contDiff
        fixedP506L0CompleteJointCartanOriginProfileActual
        fixedP506L0CompleteJointCartanOriginProfileActual_smooth direction)
  exact contDiff_const.mul derivativeCoordinateSmooth

/-- The actual live-coframe adjoint installer correction is smooth in its
source-owned spatial contact. -/
theorem fixedP506L0CompleteJointAdjointResponseWrite_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      liveCoframeConjugateMatterTimeResponseWrite
        (fixedP506L0CompleteJointPrimalWrittenContact space) matter := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      liveCoframeConjugateMatterTimeResponseWrite
        (fixedP506L0CompleteJointPrimalWrittenContact space) matter) =
      fun space =>
        holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
            fixedP506L0CompleteJointCartanOriginProfileActual
            (canonicalCauchySlicePoint 0 space) matter -
          holonomicConjugateMatterDerivativeDual
            fixedP506L0CompleteJointCartanOriginProfileActual
            (canonicalCauchySlicePoint 0 space)
            canonicalLorentzianTimeDirection matter by
    funext space
    rw [fixedP506L0CompleteJointAdjointResponseWrite_normalForm]
    rfl]
  exact
    ((holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_apply_contDiff
      fixedP506L0CompleteJointCartanOriginProfileActual
      fixedP506L0CompleteJointCartanOriginProfileActual_smooth matter).comp
        canonicalZeroSlice_contDiff).sub
      ((fixedP506L0CompleteJointCartanOriginProfileActual_conjugateDerivative_apply_contDiff
        canonicalLorentzianTimeDirection matter).comp
          canonicalZeroSlice_contDiff)

/-- Public fixed-lineage mouth for the same adjoint correction, stated
without the private local abbreviation used by the proof above. -/
theorem fixedP506L0CompleteJointAdjointResponseWrite_direct_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      liveCoframeConjugateMatterTimeResponseWrite
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual space)) matter := by
  simpa [fixedP506L0CompleteJointPrimalWrittenContact] using
    fixedP506L0CompleteJointAdjointResponseWrite_apply_contDiff matter

/-! ## P286 generated profiles -/

private theorem
    recenteredCartanRepairedConstitutiveCurrent_gaugeConnection_eq_recenteredInput
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).gaugeConnection =
      (spatiallyRecenterHolonomicConfiguration FixedInput space
        ).gaugeConnection := by
  rw [recenteredCartanRepairedConstitutiveCurrent_gaugeConnection]
  unfold recenteredContactActual
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection]

private theorem
    recenteredCartanRepairedConstitutiveCurrent_gaugeCurvature_origin_eq_input
    (space : StageNineSpatialPoint) :
    holonomicGaugeCurvature
        (recenteredCartanRepairedConstitutiveCurrent space) 0 =
      holonomicGaugeCurvature FixedInput
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicGaugeCurvature
          (recenteredCartanRepairedConstitutiveCurrent space) 0 =
        holonomicGaugeCurvature
          (spatiallyRecenterHolonomicConfiguration FixedInput space) 0 :=
      holonomicGaugeCurvature_eq_of_connection_eq_current _ _
        (recenteredCartanRepairedConstitutiveCurrent_gaugeConnection_eq_recenteredInput
          space) 0
    _ = holonomicGaugeCurvature FixedInput
          (canonicalSpatialContactTranslation space 0) :=
      holonomicGaugeCurvature_spatiallyRecenter FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth space 0
    _ = holonomicGaugeCurvature FixedInput
          (canonicalCauchySlicePoint 0 space) := by
      rw [canonicalSpatialContactTranslation_zero_local]

/-- Exact source/current normal form of the P286 origin coordinate consumed
by the complete action write. -/
theorem fixedP506L0CompleteJointP286OriginAuxiliary_normalForm
    (space : StageNineSpatialPoint) :
    currentP286OriginAuxiliaryCoordinate
        (recenteredCartanRepairedScalarSecondJetActual space) =
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        1
        (holonomicP286GaugeCurvatureCoordinate FixedInput
          (canonicalCauchySlicePoint 0 space)) := by
  funext pair
  unfold currentP286OriginAuxiliaryCoordinate
    recenteredCartanRepairedScalarSecondJetActual
  rw [installScalarQuadraticTimeCorrection_gaugeAuxiliary,
    recenteredCartanRepairedConstitutiveCurrent_liveGaugeAuxiliary_origin,
    recenteredCartanRepairedConstitutiveCurrent_coframe_origin,
    recenteredCartanRepairedConstitutiveCurrent_gaugeCurvature_origin_eq_input]
  unfold
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    holonomicP286GaugeCurvatureCoordinate
  rw [show
    (fun pair =>
      p286CoordinateEquiv
        (holonomicGaugeCurvature FixedInput
          (canonicalCauchySlicePoint 0 space) pair)) =
      formNativeP286GaugeActualToCoordinateLinear
        (holonomicGaugeCurvature FixedInput
          (canonicalCauchySlicePoint 0 space)) by rfl]
  rw [formNativeP286GaugeActual_coordinate_actual]
  rfl

private theorem fixedInput_gaugeCurvatureCoordinate_component_contDiff
    (pair : Fin 6) (coordinate : P286CoordinateIndex) :
    ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate FixedInput point pair coordinate := by
  letI : Fintype P286CoordinateIndex :=
    StageNineCoframeGravityGaugeRegularity.p286CoordinateIndexFintype
  let projection : P286CoordinateCarrier →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate).comp
      (EuclideanSpace.equiv P286CoordinateIndex ℝ).toContinuousLinearMap
  exact projection.contDiff.comp
    (holonomicGaugeCurvature_coordinate_contDiff FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth pair)

private theorem fixedInput_gaugeCurvatureCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeCurvatureCoordinate FixedInput) := by
  apply contDiff_pi'
  intro pair
  apply contDiff_piLp'
  intro coordinate
  exact fixedInput_gaugeCurvatureCoordinate_component_contDiff pair coordinate

/-- Each P286 origin two-form component generated for the complete write is
smooth in the fixed source occurrence. -/
theorem fixedP506L0CompleteJointP286OriginAuxiliary_component_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      currentP286OriginAuxiliaryCoordinate
        (recenteredCartanRepairedScalarSecondJetActual space) pair := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      currentP286OriginAuxiliaryCoordinate
        (recenteredCartanRepairedScalarSecondJetActual space) pair) =
      fun space =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          1
          (holonomicP286GaugeCurvatureCoordinate FixedInput
            (canonicalCauchySlicePoint 0 space)) pair by
    funext space
    exact congrFun
      (fixedP506L0CompleteJointP286OriginAuxiliary_normalForm space) pair]
  apply contDiff_iff_contDiffAt.2
  intro space
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (1 : LorentzianCoframe) (by norm_num)
      (holonomicP286GaugeCurvatureCoordinate FixedInput
        (canonicalCauchySlicePoint 0 space))
  have inner : ContDiffAt ℝ ∞
      (fun candidate : StageNineSpatialPoint =>
        ((1 : LorentzianCoframe),
          holonomicP286GaugeCurvatureCoordinate FixedInput
            (canonicalCauchySlicePoint 0 candidate))) space :=
    contDiffAt_const.prodMk
      ((fixedInput_gaugeCurvatureCoordinate_contDiff.comp
        canonicalZeroSlice_contDiff).contDiffAt)
  exact contDiffAt_pi.mp (outer.comp space inner) pair

/-! ## Gravity-origin profile -/

private theorem fixedP506L0CompleteJointGeneratedProfiles_gravityConnectionOrigin_eq_restart
    (space : StageNineSpatialPoint) :
    (fixedP506L0CompleteJointGeneratedProfiles space).gravityConnectionOrigin =
      (fixedP506L0CartanRestartActual space).gravityConnection 0 := by
  unfold fixedP506L0CompleteJointGeneratedProfiles
    completeJointGeneratedProfilesFromCurrent
    sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
    diracDualFormNativeECNormalPreparedActual
    diracDualFormNativeECEvolutionWrittenCurrent
  rw [restrictHolonomicConfigurationToIIPlus_gravityConnection,
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero]
  simp [completeJointPreECCurrent, completeJointScalarSecondJetCurrent]

/-- Direct fixed-preEC normal form consumed by the global normalized-affine
connection. -/
theorem fixedP506L0FinalCommonPreECConnectionOrigin_eq_restart
    (space : StageNineSpatialPoint) :
    sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space) =
      (fixedP506L0CartanRestartActual space).gravityConnection 0 := by
  unfold sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
    diracDualFormNativeECNormalPreparedActual
    diracDualFormNativeECEvolutionWrittenCurrent
  rw [restrictHolonomicConfigurationToIIPlus_gravityConnection,
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero,
    fixedP506L0FinalCommonPreECActionActual_gravityConnection_eq_recentered,
    recenteredCartanRepairedConstitutiveCurrent_gravityConnection_eq_cartan]

/-- Every component of the direct fixed-preEC origin profile is smooth in
the source-owned spatial occurrence. -/
theorem fixedP506L0FinalCommonPreECConnectionOrigin_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space)
          formDirection internalOut internalIn := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space)
          formDirection internalOut internalIn) =
      fun _ =>
        (fixedP506L0CartanRestartActual 0).gravityConnection 0
          formDirection internalOut internalIn by
    funext space
    rw [fixedP506L0FinalCommonPreECConnectionOrigin_eq_restart,
      fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero]]
  exact contDiff_const

/-- Every coordinate of the generated EC origin profile is smooth in the
source-owned spatial occurrence.  On this lineage the entire origin is
constant, so no inverse or target regularity premise is needed. -/
theorem
    fixedP506L0CompleteJointGeneratedProfiles_gravityConnectionOrigin_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      (fixedP506L0CompleteJointGeneratedProfiles space).gravityConnectionOrigin
        formDirection internalOut internalIn := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      (fixedP506L0CompleteJointGeneratedProfiles space).gravityConnectionOrigin
        formDirection internalOut internalIn) =
    fun space =>
      (fixedP506L0CartanRestartActual space).gravityConnection 0
        formDirection internalOut internalIn by
      funext space
      exact congrFun (congrFun (congrFun
        (fixedP506L0CompleteJointGeneratedProfiles_gravityConnectionOrigin_eq_restart
          space) formDirection) internalOut) internalIn]
  rw [show
    (fun space : StageNineSpatialPoint =>
      (fixedP506L0CartanRestartActual space).gravityConnection 0
        formDirection internalOut internalIn) =
    fun _ =>
      (fixedP506L0CartanRestartActual 0).gravityConnection 0
        formDirection internalOut internalIn by
      funext space
      exact congrFun (congrFun (congrFun
        (fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero space)
        formDirection) internalOut) internalIn]
  exact contDiff_const

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506Regularity
