import H0mework.Physics.FinalJoint.FixedRepairedConstitutiveCartanWholeFieldWrite
import H0mework.Physics.FinalJoint.FixedP286AffineIdentification
import H0mework.Physics.FinalJoint.FixedTimeAxisCoframe
import H0mework.Physics.FixedJoint.FixedSectionResponseResidual
import H0mework.Physics.RepairedAction.ActionSpatialSectionAdjointResponseRegularity
import H0mework.Physics.Constitutive.P286GaugeConstitutiveEliminationRegularity

/-!
# Fixed P506/L0 repaired-Cartan live-domain regularity

The final repaired-constitutive--Cartan write contains live inverse-coframe
operations.  Its authoritative fixed coframe is globally smooth, but the
existing determinant calculation does not say that it is globally
nondegenerate.  This module therefore takes the canonical connected
component of the actual determinant complement containing the generated
origin.  The construction accepts no radius, branch, endpoint, or
regularity receipt.

The regularity layer below transports the polynomial/affine fields, proves
the repaired matter and adjoint fields smooth from their explicit generated
normal forms, and treats the live P286 constitutive inverse on the canonical
domain.  It neither changes the actual nor manufactures a replacement field.

No global smoothness is claimed for the Cartan connection or its curvature-
dependent reaction multiplier: the present library has only the pointwise
first-order Cartan inverse seam needed by the contact equations.  That stronger
regularity is not a premise of the fixed contact acceptance proved downstream.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonRepairedConstitutiveCartanLiveDomainRegularity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonMatterAcceptance
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506FinalCommonRepairedConstitutiveCartanWholeFieldWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointResponseRegularity
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterActionTimeVelocity
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance repairedCartanLiveP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  constitutiveRegularityP286ModuleFinite

local instance repairedCartanLiveP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  constitutiveRegularityP286CoordinateIndexFintype

local instance repairedCartanLiveP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  constitutiveRegularityP286CoordinateIsTopologicalAddGroup

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonActionActual 0

private abbrev Actual : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual

/-! ## Canonical source-generated live domain -/

/-- The exact nondegenerate locus of the fixed produced coframe. -/
def fixedP506L0FinalCommonRepairedCartanLiveSet : Set BasePoint :=
  {point | Matrix.det (Actual.coframe point) ≠ 0}

/-- The canonical live spacetime domain is the connected component of the
actual determinant complement that contains the generated origin. -/
def fixedP506L0FinalCommonRepairedCartanLiveDomain : Set BasePoint :=
  connectedComponentIn fixedP506L0FinalCommonRepairedCartanLiveSet 0

theorem fixedP506L0FinalCommonRepairedCartan_coframe_contDiff :
    ContDiff ℝ ∞ Actual.coframe := by
  rw [fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_coframe]
  exact fixedP506L0FinalCommonActionActual_coframe_contDiff 0

theorem fixedP506L0FinalCommonRepairedCartan_coframe_origin_eq_one :
    Actual.coframe 0 = 1 := by
  rw [fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_coframe]
  rw [show (0 : BasePoint) = canonicalCauchySlicePoint 0 0 by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]]
  exact fixedP506L0FinalCommonActionActual_coframe_timeAxis_zero 0

/-- The fixed whole-field write retains the generated identity coframe germ
at the common origin, including its complete first derivative. -/
theorem fixedP506L0FinalCommonRepairedCartan_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt Actual.coframe 0 =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_coframe]
  rw [← fixedP506L0FinalCommonMatterSmoothComparison_coframe_eq_final 0]
  exact fixedP506L0FinalCommonMatterSmoothComparison_coframeFirstJet_origin 0

theorem fixedP506L0FinalCommonRepairedCartanLiveSet_open :
    IsOpen fixedP506L0FinalCommonRepairedCartanLiveSet := by
  unfold fixedP506L0FinalCommonRepairedCartanLiveSet
  exact isOpen_ne_fun
    fixedP506L0FinalCommonRepairedCartan_coframe_contDiff.continuous.matrix_det
    continuous_const

theorem fixedP506L0FinalCommonRepairedCartanLiveDomain_origin_mem :
    0 ∈ fixedP506L0FinalCommonRepairedCartanLiveDomain := by
  unfold fixedP506L0FinalCommonRepairedCartanLiveDomain
  apply mem_connectedComponentIn
  change Matrix.det (Actual.coframe 0) ≠ 0
  rw [fixedP506L0FinalCommonRepairedCartan_coframe_origin_eq_one]
  norm_num

theorem fixedP506L0FinalCommonRepairedCartanLiveDomain_open :
    IsOpen fixedP506L0FinalCommonRepairedCartanLiveDomain := by
  unfold fixedP506L0FinalCommonRepairedCartanLiveDomain
  exact fixedP506L0FinalCommonRepairedCartanLiveSet_open.connectedComponentIn

theorem fixedP506L0FinalCommonRepairedCartanLiveDomain_mem_nhds_origin :
    fixedP506L0FinalCommonRepairedCartanLiveDomain ∈ nhds (0 : BasePoint) :=
  fixedP506L0FinalCommonRepairedCartanLiveDomain_open.mem_nhds
    fixedP506L0FinalCommonRepairedCartanLiveDomain_origin_mem

theorem fixedP506L0FinalCommonRepairedCartanLiveDomain_nondegenerate
    {point : BasePoint}
    (inDomain : point ∈ fixedP506L0FinalCommonRepairedCartanLiveDomain) :
    Matrix.det (Actual.coframe point) ≠ 0 := by
  exact connectedComponentIn_subset
    fixedP506L0FinalCommonRepairedCartanLiveSet 0 inDomain

/-! ## Globally regular preserved and polynomial fields -/

theorem fixedP506L0FinalCommonRepairedCartan_coframe_component_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun point => Actual.coframe point row column :=
  contDiff_pi.mp
    (contDiff_pi.mp
      fixedP506L0FinalCommonRepairedCartan_coframe_contDiff row) column

theorem
    fixedP506L0FinalCommonRepairedCartan_gravityAuxiliary_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      Actual.gravityAuxiliary point internalPair spacetimePair := by
  have auxiliarySmooth : ContDiff ℝ ∞ fun point =>
      physicalIIPlusBivector (Actual.coframe point) :=
    physicalIIPlusBivector_contDiff.comp
      fixedP506L0FinalCommonRepairedCartan_coframe_contDiff
  change ContDiff ℝ ∞ fun point =>
    physicalIIPlusBivector (Actual.coframe point)
      internalPair spacetimePair
  exact contDiff_pi.mp (contDiff_pi.mp auxiliarySmooth internalPair)
    spacetimePair

theorem
    fixedP506L0FinalCommonRepairedCartan_gaugeConnection_component_contDiff
    (direction : LorentzianIndex) (coordinate : P286CoordinateIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (Actual.gaugeConnection point direction)
        coordinate := by
  rw [show Actual.gaugeConnection = Current.gaugeConnection by
    exact
      fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_gaugeConnection]
  letI : Fintype P286CoordinateIndex :=
    StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity.finalCommonP286CoordinateIndexFintype
  let projection : P286CoordinateCarrier →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate).comp
      (EuclideanSpace.equiv P286CoordinateIndex ℝ).toContinuousLinearMap
  exact projection.contDiff.comp
    (fixedP506L0FinalCommonActionActual_gaugeConnection_contDiff 0 direction)

theorem fixedP506L0FinalCommonRepairedCartan_scalar_contDiff :
    ContDiff ℝ ∞ Actual.scalar := by
  rw [show Actual.scalar = Current.scalar by
    exact fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_scalar]
  exact fixedP506L0FinalCommonActionActual_scalar_contDiff 0

/-! ## Repaired spatial matter field -/

private def fixedCurrentRepairedSpatialInput
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  spatiallyRecenterHolonomicConfiguration Current space

/-- The actual repaired primal write recomputed at the matching fixed-current
spatial occurrence. -/
def fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite
    (space : StageNineSpatialPoint) : DiracExteriorMatterCarrier :=
  diracDualCurrentCoframeMatterTimeResponseWrite
    (fixedCurrentRepairedSpatialInput space)

private theorem canonicalSpatialContactTranslation_zero_local
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  unfold canonicalSpatialContactTranslation
  exact add_zero _

private theorem canonicalSpatialContactTranslation_hasFDerivAt_local
    (space : StageNineSpatialPoint) (point : BasePoint) :
    HasFDerivAt (canonicalSpatialContactTranslation space)
      (ContinuousLinearMap.id ℝ BasePoint) point := by
  unfold canonicalSpatialContactTranslation
  fun_prop

private theorem fixedCurrent_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    Current.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  rw [fixedP506L0FinalCommonActionActual_coframe_eq_solved]
  exact fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space

private theorem fixedCurrent_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt Current.coframe
        (canonicalCauchySlicePoint 0 space) =
      identityCoframeMatterGeometry := by
  rw [fixedP506L0FinalCommonActionActual_coframe_eq_solved,
    fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  simpa [identityCoframeMatterGeometry] using
    fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space

private theorem fixedCurrentRepairedSpatialInput_coframe_origin
    (space : StageNineSpatialPoint) :
    (fixedCurrentRepairedSpatialInput space).coframe 0 = 1 := by
  unfold fixedCurrentRepairedSpatialInput
    spatiallyRecenterHolonomicConfiguration
  change Current.coframe (canonicalSpatialContactTranslation space 0) = 1
  rw [canonicalSpatialContactTranslation_zero_local]
  exact fixedCurrent_coframe_zeroSlice space

private theorem fixedCurrentRepairedSpatialInput_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (fixedCurrentRepairedSpatialInput space).coframe 0 =
      identityCoframeMatterGeometry := by
  calc
    holonomicCoframeFirstJetAt
          (fixedCurrentRepairedSpatialInput space).coframe 0 =
        holonomicCoframeFirstJetAt Current.coframe
          (canonicalCauchySlicePoint 0 space) := by
      apply coframeJet_eq_of_fields_eq
      · change Current.coframe
          (canonicalSpatialContactTranslation space 0) = _
        rw [canonicalSpatialContactTranslation_zero_local]
        rfl
      · funext derivativeDirection internal coordinate
        let component : BasePoint → ℝ := fun point =>
          Current.coframe point internal coordinate
        have fieldDifferentiable : DifferentiableAt ℝ component
            (canonicalSpatialContactTranslation space 0) :=
          (((fixedP506L0FinalCommonActionActual_smooth 0).1
            internal coordinate).differentiable (by simp)).differentiableAt
        have composed :=
          fieldDifferentiable.hasFDerivAt.comp 0
            (canonicalSpatialContactTranslation_hasFDerivAt_local space 0)
        change
          fderiv ℝ
              (component ∘ canonicalSpatialContactTranslation space)
              0 (coordinateDirection derivativeDirection) =
            fderiv ℝ component (canonicalCauchySlicePoint 0 space)
              (coordinateDirection derivativeDirection)
        rw [composed.fderiv]
        simp [canonicalSpatialContactTranslation_zero_local]
    _ = identityCoframeMatterGeometry :=
      fixedCurrent_coframeFirstJet_zeroSlice space

private theorem
    fixedCurrentRepairedSpatialInput_matterCoordinateDerivative_origin
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((fixedCurrentRepairedSpatialInput space).matter point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Current.matter point))
        (canonicalCauchySlicePoint 0 space) direction := by
  let coordinateField : BasePoint → MatterCoordinateCarrier :=
    fun point => matterCoordinateEquiv (Current.matter point)
  have fieldDifferentiable : DifferentiableAt ℝ coordinateField
      (canonicalSpatialContactTranslation space 0) := by
    rw [canonicalSpatialContactTranslation_zero_local]
    exact
      ((fixedP506L0FinalCommonActionActual_smooth 0).2.2.2.2.2.2.2.1
        |>.differentiable (by simp)).differentiableAt
  have composed := fieldDifferentiable.hasFDerivAt.comp 0
    (canonicalSpatialContactTranslation_hasFDerivAt_local space 0)
  unfold fieldDirectionalDerivative
  change
    fderiv ℝ
        (coordinateField ∘ canonicalSpatialContactTranslation space)
        0 (coordinateDirection direction) =
      fderiv ℝ coordinateField (canonicalCauchySlicePoint 0 space)
        (coordinateDirection direction)
  rw [composed.fderiv]
  simp [canonicalSpatialContactTranslation_zero_local]

private theorem
    fixedCurrentRepairedSpatialInput_matterCovariantDerivative_origin
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (fixedCurrentRepairedSpatialInput space) 0 direction =
      holonomicMatterCovariantDerivative Current
        (canonicalCauchySlicePoint 0 space) direction := by
  unfold holonomicMatterCovariantDerivative
  rw [fixedCurrentRepairedSpatialInput_matterCoordinateDerivative_origin]
  simp [fixedCurrentRepairedSpatialInput,
    spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_zero_local]

private theorem fixedCurrentRepairedSpatialInput_knownVector_origin
    (space : StageNineSpatialPoint) :
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (fixedCurrentRepairedSpatialInput space) 0 =
      holonomicDiracDualIdentityCoframeMatterKnownVector Current
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicDiracDualIdentityCoframeMatterKnownVector
  rw [fixedCurrentRepairedSpatialInput_coframe_origin]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
        identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp_rw [fixedCurrentRepairedSpatialInput_matterCovariantDerivative_origin]
  simp [fixedCurrentRepairedSpatialInput,
    spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_zero_local]

theorem
    fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite_normalForm
    (space : StageNineSpatialPoint) :
    fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite space =
      holonomicDiracDualIdentityCoframeMatterRawTimeVelocity Current
          (canonicalCauchySlicePoint 0 space) -
        matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point => matterCoordinateEquiv (Current.matter point))
            (canonicalCauchySlicePoint 0 space)
            canonicalLorentzianTimeDirection) := by
  unfold fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite
    diracDualCurrentCoframeMatterTimeResponseWrite
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
  rw [fixedCurrentRepairedSpatialInput_coframe_origin,
    fixedCurrentRepairedSpatialInput_knownVector_origin,
    currentCoframeMatterTemporalPrincipalInverse_one,
    fixedCurrentRepairedSpatialInput_matterCovariantDerivative_origin]
  unfold holonomicDiracDualIdentityCoframeMatterRawTimeVelocity
    holonomicMatterCovariantDerivative
  unfold
    StageNineCurrentCoframeMatterTimeResponse.holonomicMatterConnectionAction
  module

private theorem canonicalZeroSlice_contDiff_local :
    ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
    funext space
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    simp]
  exact canonicalSpatialInclusion.contDiff

theorem
    fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite_contDiff :
    ContDiff ℝ ∞ fun space =>
      matterCoordinateEquiv
        (fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite
          space) := by
  rw [show
    (fun space => matterCoordinateEquiv
      (fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite
        space)) =
    fun space =>
      matterCoordinateEquiv
          (holonomicDiracDualIdentityCoframeMatterRawTimeVelocity Current
            (canonicalCauchySlicePoint 0 space)) -
        fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (Current.matter point))
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection by
      funext space
      rw [
        fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite_normalForm,
        map_sub, matterCoordinateEquiv.apply_symm_apply]]
  exact
    ((holonomicDiracDualIdentityCoframeMatterRawTimeVelocity_coordinate_contDiff
      Current (fixedP506L0FinalCommonActionActual_smooth 0)).comp
        canonicalZeroSlice_contDiff_local).sub
      ((holonomicMatterCoordinateDerivative_contDiff_local Current
        (fixedP506L0FinalCommonActionActual_smooth 0)
        canonicalLorentzianTimeDirection).comp
          canonicalZeroSlice_contDiff_local)

theorem fixedP506L0FinalCommonRepairedCartan_matter_normalForm
    (point : BasePoint) :
    matterCoordinateEquiv
        (fixedP506L0FinalCommonRepairedConstitutiveSectionActual.matter point) =
      matterCoordinateEquiv (Current.matter point) +
        canonicalTimeProjection point •
          matterCoordinateEquiv
            (fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite
              (canonicalSpatialProjection point)) := by
  rw [← canonicalCauchySlicePoint_projections point]
  change
    matterCoordinateEquiv
        ((diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          positiveSmoothUnifiedSource Current).matter
          (canonicalCauchySlicePoint (canonicalTimeProjection point)
            (canonicalSpatialProjection point))) = _
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_matter_slice]
  unfold
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter,
    installConjugateMatterLinearTimeResponse_matter,
    installMatterLinearTimeResponse_matter_coordinate]
  unfold fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite
    fixedCurrentRepairedSpatialInput matterLinearTimeCoordinateWrite
  simp [spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_timeAxis]

/-- The primal field of the fixed repaired-Cartan actual is globally smooth;
the proof uses its explicit current plus time-times-spatial-response normal
form, not a generic arbitrary-current section theorem. -/
theorem fixedP506L0FinalCommonRepairedCartan_matter_contDiff :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (Actual.matter point) := by
  rw [show Actual.matter =
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual.matter by
    exact sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
      positiveSmoothUnifiedSource
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual]
  rw [show
    (fun point => matterCoordinateEquiv
      (fixedP506L0FinalCommonRepairedConstitutiveSectionActual.matter point)) =
      (fun point => matterCoordinateEquiv (Current.matter point)) +
        (fun point : BasePoint => canonicalTimeProjection point) •
          ((fun space => matterCoordinateEquiv
            (fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite
              space)) ∘ canonicalSpatialProjection) by
    funext point
    exact fixedP506L0FinalCommonRepairedCartan_matter_normalForm point]
  exact
    (fixedP506L0FinalCommonActionActual_matter_contDiff 0).add
      (canonicalTimeProjection.contDiff.smul
        (fixedP506L0FinalCommonRepairedCartanSpatialMatterResponseWrite_contDiff.comp
          canonicalSpatialProjection.contDiff))

/-! ## Repaired spatial adjoint field -/

private def fixedCurrentRepairedSpatialPrimalInput
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (fixedCurrentRepairedSpatialInput space)

private theorem
    fixedCurrentRepairedSpatialPrimalInput_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (fixedCurrentRepairedSpatialPrimalInput space).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold fixedCurrentRepairedSpatialPrimalInput
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe]
  exact fixedCurrentRepairedSpatialInput_coframeFirstJet_origin space

/-- The same occurrence's adjoint write, generated after the repaired primal
write as required by the mother-action dependency order. -/
def fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
    (space : StageNineSpatialPoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  liveCoframeConjugateMatterTimeResponseWrite
    (fixedCurrentRepairedSpatialPrimalInput space)

private theorem
    fixedCurrentRepairedSpatialInput_conjugateMatterCoordinateDerivative_origin
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (fixedCurrentRepairedSpatialInput space) 0 direction =
      holonomicConjugateMatterDerivativeCoordinates Current
        (canonicalCauchySlicePoint 0 space) direction := by
  let coordinateField : BasePoint → MatterCoordinateCarrier :=
    holonomicConjugateMatterCoordinates Current
  have fieldDifferentiable : DifferentiableAt ℝ coordinateField
      (canonicalSpatialContactTranslation space 0) := by
    rw [canonicalSpatialContactTranslation_zero_local]
    exact
      ((holonomicConjugateMatterCoordinates_contDiff Current
        (fixedP506L0FinalCommonActionActual_smooth 0))
        |>.differentiable (by simp)).differentiableAt
  have composed := fieldDifferentiable.hasFDerivAt.comp 0
    (canonicalSpatialContactTranslation_hasFDerivAt_local space 0)
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  change
    fderiv ℝ
        (coordinateField ∘ canonicalSpatialContactTranslation space)
        0 (coordinateDirection direction) =
      fderiv ℝ coordinateField (canonicalCauchySlicePoint 0 space)
        (coordinateDirection direction)
  rw [composed.fderiv]
  simp [canonicalSpatialContactTranslation_zero_local]

private theorem
    fixedCurrentRepairedSpatialPrimalInput_conjugateMatter_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedCurrentRepairedSpatialPrimalInput space).conjugateMatter =
      (fixedCurrentRepairedSpatialInput space).conjugateMatter :=
  rfl

private theorem
    fixedCurrentRepairedSpatialPrimalInput_conjugateMatterCoordinateDerivative_origin
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (fixedCurrentRepairedSpatialPrimalInput space) 0 direction =
      holonomicConjugateMatterDerivativeCoordinates Current
        (canonicalCauchySlicePoint 0 space) direction := by
  unfold holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [fixedCurrentRepairedSpatialPrimalInput_conjugateMatter_eq_recentered]
  exact
    fixedCurrentRepairedSpatialInput_conjugateMatterCoordinateDerivative_origin
      space direction

private theorem
    fixedCurrentRepairedSpatialPrimalInput_conjugateMatterDerivative_origin
    (space : StageNineSpatialPoint) (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (fixedCurrentRepairedSpatialPrimalInput space) 0 direction =
      holonomicConjugateMatterDerivativeDual Current
        (canonicalCauchySlicePoint 0 space) direction := by
  unfold holonomicConjugateMatterDerivativeDual
  rw [
    fixedCurrentRepairedSpatialPrimalInput_conjugateMatterCoordinateDerivative_origin]

private theorem
    fixedCurrentRepairedSpatialPrimalInput_identityAdjointActionVelocity_origin
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        (fixedCurrentRepairedSpatialPrimalInput space) 0 =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity Current
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterSpatialTransport
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  simp_rw [
    fixedCurrentRepairedSpatialPrimalInput_conjugateMatterDerivative_origin]
  simp [fixedCurrentRepairedSpatialPrimalInput,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    fixedCurrentRepairedSpatialInput,
    spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_zero_local]

/-- The identity presentation is a fixed-first-jet compatibility readout of
the live response; the producer definition remains the live writer above. -/
private theorem
    fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite_eq_identity
    (space : StageNineSpatialPoint) :
    fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite space =
      diracDualIdentityCoframeConjugateMatterTimeResponseWrite
        (fixedCurrentRepairedSpatialPrimalInput space) := by
  unfold fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
  rw [liveCoframeConjugateMatterTimeResponseWrite_eq_rightChiralIdentity_of_firstJet
      _ (fixedCurrentRepairedSpatialPrimalInput_coframeFirstJet_origin space),
    ← diracDualIdentityCoframeConjugateMatterTimeResponseWrite_eq_rightChiralIdentity]

private theorem
    fixedCurrentRepairedSpatialPrimalInput_liveAdjointActionVelocity_origin
    (space : StageNineSpatialPoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (fixedCurrentRepairedSpatialPrimalInput space) 0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Current
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (fixedCurrentRepairedSpatialPrimalInput space) 0 =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          (fixedCurrentRepairedSpatialPrimalInput space) 0 :=
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ (fixedCurrentRepairedSpatialPrimalInput_coframeFirstJet_origin space)
    _ = holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          (fixedCurrentRepairedSpatialPrimalInput space) 0 :=
      (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        _ _).symm
    _ = holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity Current
          (canonicalCauchySlicePoint 0 space) :=
      fixedCurrentRepairedSpatialPrimalInput_identityAdjointActionVelocity_origin
        space
    _ = holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          Current (canonicalCauchySlicePoint 0 space) :=
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        _ _
    _ = holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Current
          (canonicalCauchySlicePoint 0 space) :=
      (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ (fixedCurrent_coframeFirstJet_zeroSlice space)).symm

theorem
    fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite_normalForm
    (space : StageNineSpatialPoint) :
    fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite space =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Current
          (canonicalCauchySlicePoint 0 space) -
        holonomicConjugateMatterDerivativeDual Current
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection := by
  unfold fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
    liveCoframeConjugateMatterTimeResponseWrite
  rw [fixedCurrentRepairedSpatialPrimalInput_liveAdjointActionVelocity_origin,
    fixedCurrentRepairedSpatialPrimalInput_conjugateMatterDerivative_origin]

private theorem
    fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite_identityNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite space =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity Current
          (canonicalCauchySlicePoint 0 space) -
        holonomicConjugateMatterDerivativeDual Current
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection := by
  rw [
    fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite_eq_identity]
  unfold diracDualIdentityCoframeConjugateMatterTimeResponseWrite
  rw [
    fixedCurrentRepairedSpatialPrimalInput_identityAdjointActionVelocity_origin,
    fixedCurrentRepairedSpatialPrimalInput_conjugateMatterDerivative_origin]

private theorem fixedCurrent_conjugateMatterDerivative_apply_contDiff
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point =>
      holonomicConjugateMatterDerivativeDual Current point direction
        matter := by
  rw [show
    (fun point =>
      holonomicConjugateMatterDerivativeDual Current point direction
        matter) =
      fun point => ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv matter index *
          holonomicConjugateMatterDerivativeCoordinates Current point
            direction index by
    funext point
    exact matterDualOfCoordinates_apply _ _]
  apply ContDiff.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have derivativeCoordinateSmooth : ContDiff ℝ ∞ fun point =>
      holonomicConjugateMatterDerivativeCoordinates Current point
        direction index :=
    (projection.restrictScalars ℝ).contDiff.comp
      (holonomicConjugateMatterDerivativeCoordinates_contDiff Current
        (fixedP506L0FinalCommonActionActual_smooth 0) direction)
  exact contDiff_const.mul derivativeCoordinateSmooth

theorem
    fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun space =>
      fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
        space matter := by
  rw [show
    (fun space =>
      fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
        space matter) =
    fun space =>
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity Current
          (canonicalCauchySlicePoint 0 space) matter -
        holonomicConjugateMatterDerivativeDual Current
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection matter by
      funext space
      rw [
        fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite_identityNormalForm]
      rfl]
  exact
    ((holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_apply_contDiff
      Current (fixedP506L0FinalCommonActionActual_smooth 0) matter).comp
        canonicalZeroSlice_contDiff_local).sub
      ((fixedCurrent_conjugateMatterDerivative_apply_contDiff
        canonicalLorentzianTimeDirection matter).comp
          canonicalZeroSlice_contDiff_local)

theorem fixedP506L0FinalCommonRepairedCartan_conjugateMatterCoordinates_normalForm
    (point : BasePoint) :
    matterDualCoordinates
        (fixedP506L0FinalCommonRepairedConstitutiveSectionActual.conjugateMatter
          point) =
      matterDualCoordinates (Current.conjugateMatter point) +
        canonicalTimeProjection point •
          matterDualCoordinates
            (fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
              (canonicalSpatialProjection point)) := by
  rw [← canonicalCauchySlicePoint_projections point]
  change
    matterDualCoordinates
        ((diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          positiveSmoothUnifiedSource Current).conjugateMatter
          (canonicalCauchySlicePoint (canonicalTimeProjection point)
            (canonicalSpatialProjection point))) = _
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice]
  unfold
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates]
  unfold fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
    fixedCurrentRepairedSpatialPrimalInput
    fixedCurrentRepairedSpatialInput
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    conjugateMatterLinearTimeCoordinateWrite
  simp [spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation_timeAxis]

theorem fixedP506L0FinalCommonRepairedCartan_conjugateMatter_normalForm
    (point : BasePoint) :
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual.conjugateMatter
        point =
      Current.conjugateMatter point +
        canonicalTimeProjection point •
          fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
            (canonicalSpatialProjection point) := by
  calc
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual.conjugateMatter
          point =
        matterDualOfCoordinates
          (matterDualCoordinates
            (fixedP506L0FinalCommonRepairedConstitutiveSectionActual.conjugateMatter
              point)) := by
      exact
        (matterDualOfCoordinates_surjective
          (fixedP506L0FinalCommonRepairedConstitutiveSectionActual.conjugateMatter
            point)).symm
    _ = matterDualOfCoordinates
          (matterDualCoordinates (Current.conjugateMatter point) +
            canonicalTimeProjection point •
              matterDualCoordinates
                (fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
                  (canonicalSpatialProjection point))) := by
      rw [
        fixedP506L0FinalCommonRepairedCartan_conjugateMatterCoordinates_normalForm]
    _ = _ := by
      rw [matterDualOfCoordinates_add, matterDualOfCoordinates_real_smul,
        matterDualOfCoordinates_surjective,
        matterDualOfCoordinates_surjective]

private theorem fixedCurrent_conjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point => Current.conjugateMatter point matter := by
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation
      matter).restrictScalars ℝ
  have composed : ContDiff ℝ ∞ fun point =>
      evaluation (holonomicConjugateMatterCoordinates Current point) :=
    evaluation.contDiff.comp
      (holonomicConjugateMatterCoordinates_contDiff Current
        (fixedP506L0FinalCommonActionActual_smooth 0))
  rw [show
    (fun point =>
      evaluation (holonomicConjugateMatterCoordinates Current point)) =
      fun point => Current.conjugateMatter point matter by
    funext point
    dsimp only [evaluation]
    change
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation
          matter (holonomicConjugateMatterCoordinates Current point) =
        Current.conjugateMatter point matter
    rw [
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation_apply]
    unfold holonomicConjugateMatterCoordinates
    rw [matterDualOfCoordinates_surjective]] at composed
  exact composed

/-- The adjoint field of the same fixed repaired-Cartan actual is globally
smooth when evaluated on every matter vector. -/
theorem fixedP506L0FinalCommonRepairedCartan_conjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point => Actual.conjugateMatter point matter := by
  rw [show Actual.conjugateMatter =
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual.conjugateMatter by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter
        positiveSmoothUnifiedSource
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual]
  rw [show
    (fun point =>
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual.conjugateMatter
        point matter) =
      (fun point => Current.conjugateMatter point matter) +
        (fun point : BasePoint => canonicalTimeProjection point) •
          ((fun space =>
            fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite
              space matter) ∘ canonicalSpatialProjection) by
    funext point
    rw [fixedP506L0FinalCommonRepairedCartan_conjugateMatter_normalForm]
    rfl]
  exact
    (fixedCurrent_conjugateMatter_apply_contDiff matter).add
      (canonicalTimeProjection.contDiff.smul
        ((fixedP506L0FinalCommonRepairedCartanSpatialAdjointResponseWrite_apply_contDiff
          matter).comp canonicalSpatialProjection.contDiff))

private def adjointRegularityComparison
    (adjoint : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  { coframe := fun _ => 0
    gravityConnection := fun _ _ _ _ => 0
    gravityAuxiliary := fun _ _ _ => 0
    gravitySimplicityMultiplier := fun _ _ _ => 0
    gaugeConnection := fun _ _ => 0
    gaugeAuxiliary := fun _ _ => 0
    scalar := fun _ => 0
    matter := fun _ => 0
    conjugateMatter := adjoint }

private theorem
    adjointRegularityComparison_smooth
    (adjoint : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (adjointSmooth : ∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞ fun point =>
        adjoint point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) :
    (adjointRegularityComparison adjoint).Smooth := by
  unfold StageNineHolonomicConfiguration.Smooth
  dsimp only [adjointRegularityComparison]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    fun_prop
  · intros
    fun_prop
  · intros
    fun_prop
  · intros
    fun_prop
  · intro
    fun_prop
  · intro
    fun_prop
  · fun_prop
  · fun_prop
  · exact adjointSmooth

private theorem matterDualCoordinates_contDiff_of_apply
    (adjoint : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (adjointSmooth : ∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞ fun point =>
        adjoint point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) :
    ContDiff ℝ ∞ (fun point => matterDualCoordinates (adjoint point)) := by
  have comparisonSmooth :=
    StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.holonomicConjugateMatterCoordinates_contDiff
      (adjointRegularityComparison adjoint)
      (adjointRegularityComparison_smooth adjoint adjointSmooth)
  change ContDiff ℝ ∞
    (fun point => matterDualCoordinates (adjoint point)) at comparisonSmooth
  exact comparisonSmooth

/-- Coordinate form of the fixed repaired adjoint regularity.  This is the
exact carrier consumed by the holonomic action-jet readouts. -/
theorem
    fixedP506L0FinalCommonRepairedCartan_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates Actual) := by
  change ContDiff ℝ ∞
    (fun point => matterDualCoordinates (Actual.conjugateMatter point))
  exact matterDualCoordinates_contDiff_of_apply Actual.conjugateMatter
    (fun index =>
      fixedP506L0FinalCommonRepairedCartan_conjugateMatter_apply_contDiff
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ))))

/-! ## Analytic boundary

The installed Cartan connection uses live inverse-coframe operations, while
the installed gravity multiplier additionally reads its curvature.  The
repository currently supplies only identity-contact differentiability for
the Levi--Civita carrier and no fixed all-point second-jet theorem for this
actual.  Consequently this module stops at the strongest generated
regularity proved above; it neither installs a replacement actual nor treats
a stronger regularity receipt as source data.
-/

/-! ## Live constitutive field -/

private theorem fixedCurrent_gaugeCurvatureCoordinate_component_contDiff
    (pair : Fin 6) (coordinate : P286CoordinateIndex) :
    ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate Current point pair coordinate := by
  letI : Fintype P286CoordinateIndex :=
    StageNineCoframeGravityGaugeRegularity.p286CoordinateIndexFintype
  let projection : P286CoordinateCarrier →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate).comp
      (EuclideanSpace.equiv P286CoordinateIndex ℝ).toContinuousLinearMap
  exact projection.contDiff.comp
    (holonomicGaugeCurvature_coordinate_contDiff Current
      (fixedP506L0FinalCommonActionActual_smooth 0) pair)

private theorem fixedCurrent_gaugeCurvatureCoordinate_contDiff :
    ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate Current point := by
  apply contDiff_pi'
  intro pair
  apply contDiff_piLp'
  intro coordinate
  exact fixedCurrent_gaugeCurvatureCoordinate_component_contDiff
    pair coordinate

/-- The P286 auxiliary carried by the repaired section is the actual live
Hodge inverse, and is smooth at every point of the canonical live domain. -/
theorem
    fixedP506L0FinalCommonRepairedCartan_gaugeAuxiliary_contDiffAt
    {point : BasePoint}
    (inDomain : point ∈ fixedP506L0FinalCommonRepairedCartanLiveDomain) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        fun pair => p286CoordinateEquiv
          (Actual.gaugeAuxiliary candidate pair)) point := by
  have nondegenerateCurrent : Matrix.det (Current.coframe point) ≠ 0 := by
    rw [← congrFun
      fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_coframe
      point]
    exact
      fixedP506L0FinalCommonRepairedCartanLiveDomain_nondegenerate inDomain
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (Current.coframe point) nondegenerateCurrent
      (holonomicP286GaugeCurvatureCoordinate Current point)
  have inner : ContDiffAt ℝ ∞
      (fun candidate =>
        (Current.coframe candidate,
          holonomicP286GaugeCurvatureCoordinate Current candidate)) point :=
    (fixedP506L0FinalCommonActionActual_coframe_contDiff 0).contDiffAt.prodMk
      fixedCurrent_gaugeCurvatureCoordinate_contDiff.contDiffAt
  have composed := outer.comp point inner
  rw [show
    (fun candidate =>
      fun pair => p286CoordinateEquiv
        (Actual.gaugeAuxiliary candidate pair)) =
    fun candidate =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (Current.coframe candidate)
        (holonomicP286GaugeCurvatureCoordinate Current candidate) by
      funext candidate
      rw [show Actual.gaugeAuxiliary =
          fixedP506L0FinalCommonRepairedConstitutiveSectionActual.gaugeAuxiliary by
        exact
          sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary
            positiveSmoothUnifiedSource
            fixedP506L0FinalCommonRepairedConstitutiveSectionActual]
      change
        (fun pair => p286CoordinateEquiv
          ((diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
            positiveSmoothUnifiedSource Current).gaugeAuxiliary
              candidate pair)) = _
      rw [
        diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
          positiveSmoothUnifiedSource Current
          (fixedP506L0FinalCommonActionActual_smooth 0) candidate]
      change
        formNativeP286GaugeActualToCoordinateLinear
            (StageNineFormNativeP286GaugeConstitutiveElimination.formNativeP286GaugeEliminatedAuxiliaryAtBoundary
              (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
              (Current.coframe candidate)
              (holonomicGaugeCurvature Current candidate)) = _
      unfold
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
      have curvatureCoordinate :
          formNativeP286GaugeCoordinateToActualLinear
              (holonomicP286GaugeCurvatureCoordinate Current candidate) =
            holonomicGaugeCurvature Current candidate := by
        change
          formNativeP286GaugeCoordinateToActualLinear
              (formNativeP286GaugeActualToCoordinateLinear
                (holonomicGaugeCurvature Current candidate)) = _
        exact formNativeP286GaugeActual_coordinate_actual _
      rw [curvatureCoordinate]]
  exact composed

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonRepairedConstitutiveCartanLiveDomainRegularity
