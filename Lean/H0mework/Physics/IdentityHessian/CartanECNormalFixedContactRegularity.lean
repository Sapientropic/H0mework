import H0mework.Physics.IdentityHessian.CartanECNormalFixedCartanJointRegularity

/-!
# Fixed P506/L0 contact-family regularity

This module expands the fields that are actually consumed by the KIN-16
contact family.  The current is fixed to the exact P506/L0 `U*` restriction;
the identity coframe turns the gauge constitutive operator into one fixed
finite-dimensional map.  No arbitrary-current regularity theory or gluing
receipt is introduced.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeGravityGaugeRegularity
open StageNineConjugateMatterActionTimeVelocity
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedCartanJointRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

local instance fixedP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fixedP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance fixedP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem fixedUStar_smooth :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.Smooth :=
  positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth

theorem fixedCurrent_gaugeConnectionCoordinate_contDiff
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateEquiv
        (positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeConnection
          space formDirection) := by
  change ContDiff ℝ ∞ fun space =>
    p286CoordinateEquiv
      (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        |>.gaugeConnection (canonicalCauchySlicePoint 0 space) formDirection)
  exact
    (fixedUStar_smooth.2.2.2.2.1 formDirection).comp
      canonicalZeroSlice_contDiff

theorem fixedCurrent_gaugeAuxiliaryCoordinate_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateEquiv
        (positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeAuxiliary
          space pair) := by
  change ContDiff ℝ ∞ fun space =>
    p286CoordinateEquiv
      (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        |>.gaugeAuxiliary (canonicalCauchySlicePoint 0 space) pair)
  exact
    (fixedUStar_smooth.2.2.2.2.2.1 pair).comp
      canonicalZeroSlice_contDiff

private theorem fixedCurrent_p286SpatialDerivative_contDiff
    (derivativeDirection : Fin 3) (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      cauchyP286SpatialConnectionDerivativeCoordinate
        positiveP506MatterCurrentFullSynchronizedCauchyState space
        derivativeDirection formDirection := by
  let coordinate : StageNineSpatialPoint → P286CoordinateCarrier :=
    fun space =>
      p286CoordinateEquiv
        (positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeConnection
          space formDirection)
  have coordinateSmooth : ContDiff ℝ ∞ coordinate :=
    fixedCurrent_gaugeConnectionCoordinate_contDiff formDirection
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry
        (fun _ : StageNineSpatialPoint => coordinate)) := by
    exact coordinateSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun space =>
      fderiv ℝ coordinate space := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id :
          ContDiff ℝ ∞ (fun space : StageNineSpatialPoint => space))
        (by simp)
  unfold cauchyP286SpatialConnectionDerivativeCoordinate
  change ContDiff ℝ ∞ fun space =>
    fderiv ℝ coordinate space
      (canonicalSpatialCoordinateDirection derivativeDirection)
  exact derivativeSmooth.clm_apply contDiff_const

private theorem fixedCurrent_p286Bracket_contDiff
    (first second : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateLieBracket
        (p286CoordinateEquiv
          (positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeConnection
            space first))
        (p286CoordinateEquiv
          (positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeConnection
            space second)) := by
  exact
    (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
      (fixedCurrent_gaugeConnectionCoordinate_contDiff first)).clm_apply
      (fixedCurrent_gaugeConnectionCoordinate_contDiff second)

private theorem fixedCurrent_actionGeneratedP286CurvatureCoordinate_contDiff
    (output : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space output) := by
  rw [show
    (fun space =>
      p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space output)) =
      fun space =>
        ∑ input : Fin 6,
          gaugeOperatorCoefficient
              (((sourceGeneratedUnifiedCouplings
                  positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
                coframeGaugeSpacetimeHodgeLinear
                  (1 : LorentzianCoframe))
              output input •
            p286CoordinateEquiv
              (positiveP506MatterCurrentFullSynchronizedCauchyState
                |>.gaugeAuxiliary space input) by
    funext space
    unfold actionGeneratedP286Curvature liftGaugeTwoFormOperator
    rw [fixedCurrent_coframe_one space, map_sum]
    apply Finset.sum_congr rfl
    intro input _
    rw [map_smul]]
  apply ContDiff.sum
  intro input _
  exact
    (contDiff_const :
      ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
        gaugeOperatorCoefficient
            (((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
              coframeGaugeSpacetimeHodgeLinear
                (1 : LorentzianCoframe))
            output input).smul
      (fixedCurrent_gaugeAuxiliaryCoordinate_contDiff input)

private theorem fixedCurrent_sourceGeneratedP286VelocityCoordinate_contDiff
    (direction : Fin 3) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space direction) := by
  rw [show
    (fun space =>
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space direction)) =
      fun space =>
        p286CoordinateEquiv
            (actionGeneratedP286Curvature positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState
              space (temporalSpatialPair direction)) +
          cauchyP286SpatialConnectionDerivativeCoordinate
              positiveP506MatterCurrentFullSynchronizedCauchyState
              space direction canonicalLorentzianTimeDirection -
          p286CoordinateLieBracket
            (p286CoordinateEquiv
              (positiveP506MatterCurrentFullSynchronizedCauchyState
                |>.gaugeConnection space canonicalLorentzianTimeDirection))
            (p286CoordinateEquiv
              (positiveP506MatterCurrentFullSynchronizedCauchyState
                |>.gaugeConnection space direction.succ)) by
    funext space
    exact sourceGeneratedP286SpatialConnectionVelocity_coordinate
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState
      space direction]
  exact
    ((fixedCurrent_actionGeneratedP286CurvatureCoordinate_contDiff
        (temporalSpatialPair direction)).add
      (fixedCurrent_p286SpatialDerivative_contDiff direction
        canonicalLorentzianTimeDirection)).sub
      (fixedCurrent_p286Bracket_contDiff
        canonicalLorentzianTimeDirection direction.succ)

private theorem fixedCurrent_actionGeneratedP286ExteriorDerivative_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      actionGeneratedP286ExteriorDerivativeCoordinate
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space pair := by
  unfold actionGeneratedP286ExteriorDerivativeCoordinate
  exact
    (fixedCurrent_actionGeneratedP286CurvatureCoordinate_contDiff pair).sub
      (fixedCurrent_p286Bracket_contDiff
        (pairFirst pair) (pairSecond pair))

private theorem fixedCurrent_sourceGeneratedP286LocalJet_contDiff
    (derivativeDirection formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      sourceGeneratedP286ActionLocalConnectionJet
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space derivativeDirection formDirection := by
  fin_cases derivativeDirection <;> fin_cases formDirection
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (contDiff_const :
        ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
          (0 : P286CoordinateCarrier))
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      fixedCurrent_sourceGeneratedP286VelocityCoordinate_contDiff 0
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      fixedCurrent_sourceGeneratedP286VelocityCoordinate_contDiff 1
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      fixedCurrent_sourceGeneratedP286VelocityCoordinate_contDiff 2
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      fixedCurrent_p286SpatialDerivative_contDiff 0
        canonicalLorentzianTimeDirection
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (contDiff_const :
        ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
          (0 : P286CoordinateCarrier))
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ)
        (fixedCurrent_actionGeneratedP286ExteriorDerivative_contDiff 5))
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ)
        (fixedCurrent_actionGeneratedP286ExteriorDerivative_contDiff 4)).neg
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      fixedCurrent_p286SpatialDerivative_contDiff 1
        canonicalLorentzianTimeDirection
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ)
        (fixedCurrent_actionGeneratedP286ExteriorDerivative_contDiff 5)).neg
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (contDiff_const :
        ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
          (0 : P286CoordinateCarrier))
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ)
        (fixedCurrent_actionGeneratedP286ExteriorDerivative_contDiff 3))
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      fixedCurrent_p286SpatialDerivative_contDiff 2
        canonicalLorentzianTimeDirection
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ)
        (fixedCurrent_actionGeneratedP286ExteriorDerivative_contDiff 4))
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (ContDiff.const_smul (R := ℝ) (1 / 2 : ℝ)
        (fixedCurrent_actionGeneratedP286ExteriorDerivative_contDiff 3)).neg
  · simpa [sourceGeneratedP286ActionLocalConnectionJet] using
      (contDiff_const :
        ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
          (0 : P286CoordinateCarrier))

theorem fixedJointGaugeConnectionCoordinate_contDiff
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      sourceGeneratedP286ActionLocalConnectionCoordinate
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1 joint.2 formDirection := by
  unfold sourceGeneratedP286ActionLocalConnectionCoordinate
    sourceGeneratedP286ActionLocalIncrement
  have baseSmooth : ContDiff ℝ ∞ fun joint :
      StageNineSpatialPoint × BasePoint =>
        p286CoordinateEquiv
          (positiveP506MatterCurrentFullSynchronizedCauchyState
            |>.gaugeConnection joint.1 formDirection) :=
    (fixedCurrent_gaugeConnectionCoordinate_contDiff formDirection).comp
      contDiff_fst
  have incrementSmooth : ContDiff ℝ ∞ fun joint :
      StageNineSpatialPoint × BasePoint =>
        ∑ derivativeDirection : LorentzianIndex,
          localBaseCoordinate derivativeDirection joint.2 •
            sourceGeneratedP286ActionLocalConnectionJet
              positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState
              joint.1 derivativeDirection formDirection := by
    apply ContDiff.sum
    intro derivativeDirection _
    exact
      ((localBaseCoordinate derivativeDirection).contDiff.comp
        contDiff_snd).smul
      ((fixedCurrent_sourceGeneratedP286LocalJet_contDiff
        derivativeDirection formDirection).comp contDiff_fst)
  simpa only [sum_apply,
    ContinuousLinearMap.smulRight_apply] using
      baseSmooth.add incrementSmooth

theorem fixedJointGaugeAuxiliaryCoordinate_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      p286CoordinateEquiv
        ((sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          joint.1).gaugeAuxiliary joint.2 pair) := by
  exact
    (fixedCurrent_gaugeAuxiliaryCoordinate_contDiff pair).comp contDiff_fst

theorem fixedJointCoframeCoordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1).coframe joint.2 row column := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1).coframe joint.2 row column) =
      fun _ => (1 : LorentzianCoframe) row column by
    funext joint
    change
      positiveP506MatterCurrentFullSynchronizedCauchyState.coframe
          joint.1 row column =
        (1 : LorentzianCoframe) row column
    rw [fixedCurrent_coframe_one]]
  exact contDiff_const

theorem fixedJointGaugeConnectionFieldCoordinate_contDiff
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      p286CoordinateEquiv
        ((sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          joint.1).gaugeConnection joint.2 formDirection) := by
  simpa only [sourceActionGeneratedJointLocalActualLift,
    sourceActionGeneratedMatterDualScalarLocalActualLift,
    sourceActionGeneratedMatterDualLocalActualLift,
    sourceActionGeneratedMatterLocalActualLift,
    sourceActionGeneratedGravityGaugeLocalActualLift,
    sourceGeneratedP286ActionLocalActualLift,
    sourceGeneratedP286ActionLocalConnection,
    p286CoordinateEquiv.apply_symm_apply] using
      fixedJointGaugeConnectionCoordinate_contDiff formDirection

private theorem fixedUStar_scalar_vacuum :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  calc
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar =
        positiveP506MatterCurrentCompleteBaseActual.scalar := rfl
    _ = positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.scalar :=
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields
        |>.2.2.2.2.2.1
    _ = _ :=
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalar_vacuum

theorem fixedCurrent_scalar_vacuum :
    positiveP506MatterCurrentFullSynchronizedCauchyState.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext space
  change
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar
        (canonicalCauchySlicePoint 0 space) =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [fixedUStar_scalar_vacuum]

theorem fixedCurrent_scalarVelocity_zero :
    positiveP506MatterCurrentFullSynchronizedCauchyState.scalarVelocity = 0 := by
  funext space
  change
    fieldDirectionalDerivative
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection = 0
  rw [fixedUStar_scalar_vacuum]
  simp [fieldDirectionalDerivative]

theorem fixedJointScalar_vacuum
    (space : StageNineSpatialPoint) (point : BasePoint) :
    (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space).scalar point =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    actionGeneratedScalarLocalField
        positiveP506MatterCurrentFullSynchronizedCauchyState space point =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    cauchyScalarSpatialDerivativeCoordinate,
    fixedCurrent_scalar_vacuum,
    fixedCurrent_scalarVelocity_zero,
    Fin.sum_univ_four]

theorem fixedJointScalar_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1).scalar joint.2 := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1).scalar joint.2) =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    funext joint
    exact fixedJointScalar_vacuum joint.1 joint.2]
  exact contDiff_const

def fixedCartanReactionContact
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionLocalActualLift
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentFullSynchronizedCauchyState space

@[simp] theorem fixedCartanReactionContact_coframe_one
    (space : StageNineSpatialPoint) (point : BasePoint) :
    (fixedCartanReactionContact space).coframe point = 1 := by
  change
    positiveP506MatterCurrentFullSynchronizedCauchyState.coframe space = 1
  exact fixedCurrent_coframe_one space

@[simp] theorem fixedCartanReactionContact_gaugeConnection_origin
    (space : StageNineSpatialPoint) (formDirection : LorentzianIndex) :
    (fixedCartanReactionContact space).gaugeConnection 0 formDirection =
      positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeConnection
        space formDirection := by
  change
    sourceGeneratedP286ActionLocalConnection
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space 0 formDirection =
      positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeConnection
        space formDirection
  exact sourceGeneratedP286ActionLocalConnection_origin _ _ _ _

@[simp] theorem fixedCartanReactionContact_gaugeAuxiliary_origin
    (space : StageNineSpatialPoint) (pair : Fin 6) :
    (fixedCartanReactionContact space).gaugeAuxiliary 0 pair =
      positiveP506MatterCurrentFullSynchronizedCauchyState.gaugeAuxiliary
        space pair :=
  rfl

@[simp] theorem fixedCartanReactionContact_scalar
    (space : StageNineSpatialPoint) (point : BasePoint) :
    (fixedCartanReactionContact space).scalar point =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource :=
  fixedJointScalar_vacuum space point

@[simp] theorem fixedCartanReactionContact_matter_origin
    (space : StageNineSpatialPoint) :
    (fixedCartanReactionContact space).matter 0 =
      diracSpinTwoMatterProbe := by
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentFullSynchronizedCauchyState space 0 =
      diracSpinTwoMatterProbe
  rw [actionGeneratedMatterLocalField_origin, fixedCurrent_matter_constant]

@[simp] theorem fixedCartanReactionContact_conjugateMatter_origin
    (space : StageNineSpatialPoint) :
    (fixedCartanReactionContact space).conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentFullSynchronizedCauchyState space 0 =
      diracSpinZeroMatterCoordinate
  rw [actionGeneratedConjugateMatterLocalField_origin,
    fixedCurrent_conjugateMatter_constant]

theorem fixedCartanReactionGravityConnection_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedCartanReactionContact joint.1).gravityConnection joint.2
        formDirection internalOut internalIn := by
  have connectionSmooth :=
    contDiff_pi.mp
      (contDiff_pi.mp
        (contDiff_pi.mp fixedJointCartanConnection_contDiff formDirection)
        internalOut)
      internalIn
  simpa only [fixedCartanReactionContact,
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection,
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_connection]
    using connectionSmooth

private theorem
    fixedJointCartanConnection_fderiv_origin_contDiff
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      fderiv ℝ
          (fun point =>
            sourceActionGeneratedDiracDualCartanConnectionField
              positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState
              space point formDirection internalOut internalIn)
          0 (coordinateDirection derivativeDirection) := by
  let coordinate : StageNineSpatialPoint → BasePoint → ℝ :=
    fun space point =>
      sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space point formDirection internalOut internalIn
  have jointSmooth :
      ContDiff ℝ ∞ (Function.uncurry coordinate) := by
    exact
      contDiff_pi.mp
        (contDiff_pi.mp
          (contDiff_pi.mp fixedJointCartanConnection_contDiff formDirection)
          internalOut)
        internalIn
  have derivativeSmooth :
      ContDiff ℝ ∞ fun space =>
        fderiv ℝ (coordinate space) (0 : BasePoint) := by
    simpa only [Function.uncurry_apply_pair] using
      jointSmooth.fderiv
        (contDiff_const :
          ContDiff ℝ ∞ fun _ : StageNineSpatialPoint => (0 : BasePoint))
        (by simp)
  change ContDiff ℝ ∞ fun space =>
    fderiv ℝ (coordinate space) 0
      (coordinateDirection derivativeDirection)
  exact derivativeSmooth.clm_apply contDiff_const

private def fixedJointCartanCurvatureAtOrigin
    (space : StageNineSpatialPoint) : PhysicalBivector :=
  fun internal spacetime =>
    let internalOut := pairFirst internal
    let internalIn := pairSecond internal
    let first := pairFirst spacetime
    let second := pairSecond spacetime
    minkowskiInternalSign internalOut *
      (fderiv ℝ
          (fun point =>
            sourceActionGeneratedDiracDualCartanConnectionField
              positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState
              space point second internalOut internalIn)
          0 (coordinateDirection first) -
        fderiv ℝ
          (fun point =>
            sourceActionGeneratedDiracDualCartanConnectionField
              positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState
              space point first internalOut internalIn)
          0 (coordinateDirection second) +
        ∑ middle : LorentzianIndex,
          (sourceActionGeneratedDiracDualCartanConnectionField
                positiveSmoothUnifiedSource
                positiveP506MatterCurrentFullSynchronizedCauchyState
                space 0 first internalOut middle *
              sourceActionGeneratedDiracDualCartanConnectionField
                positiveSmoothUnifiedSource
                positiveP506MatterCurrentFullSynchronizedCauchyState
                space 0 second middle internalIn -
            sourceActionGeneratedDiracDualCartanConnectionField
                positiveSmoothUnifiedSource
                positiveP506MatterCurrentFullSynchronizedCauchyState
                space 0 second internalOut middle *
              sourceActionGeneratedDiracDualCartanConnectionField
                positiveSmoothUnifiedSource
                positiveP506MatterCurrentFullSynchronizedCauchyState
                space 0 first middle internalIn))

private theorem fixedJointCartanCurvatureAtOrigin_component_contDiff
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      fixedJointCartanCurvatureAtOrigin space internal spacetime := by
  unfold fixedJointCartanCurvatureAtOrigin
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.add
  · apply ContDiff.sub
    · exact
        fixedJointCartanConnection_fderiv_origin_contDiff
          (pairFirst spacetime) (pairSecond spacetime)
          (pairFirst internal) (pairSecond internal)
    · exact
        fixedJointCartanConnection_fderiv_origin_contDiff
          (pairSecond spacetime) (pairFirst spacetime)
          (pairFirst internal) (pairSecond internal)
  · apply ContDiff.sum
    intro middle _
    exact
      ((fixedJointCartanConnection_origin_component_contDiff
          (pairFirst spacetime) (pairFirst internal) middle).mul
        (fixedJointCartanConnection_origin_component_contDiff
          (pairSecond spacetime) middle (pairSecond internal))).sub
      ((fixedJointCartanConnection_origin_component_contDiff
          (pairSecond spacetime) (pairFirst internal) middle).mul
        (fixedJointCartanConnection_origin_component_contDiff
          (pairFirst spacetime) middle (pairSecond internal)))

private theorem fixedCartanReactionGravityCurvature_origin_eq
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature
        (fixedCartanReactionContact space) 0 =
      fixedJointCartanCurvatureAtOrigin space := by
  funext internal spacetime
  simp only [holonomicGravityCurvature, gravityConnectionDerivative,
    fixedCartanReactionContact,
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection,
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_connection,
    fixedJointCartanCurvatureAtOrigin]

theorem fixedCartanReactionGravityCurvature_component_contDiff
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      holonomicGravityCurvature
        (fixedCartanReactionContact space) 0 internal spacetime := by
  rw [show
    (fun space =>
      holonomicGravityCurvature
        (fixedCartanReactionContact space) 0 internal spacetime) =
      fun space =>
        fixedJointCartanCurvatureAtOrigin space internal spacetime by
    funext space
    exact congrFun
      (congrFun (fixedCartanReactionGravityCurvature_origin_eq space)
        internal)
      spacetime]
  exact fixedJointCartanCurvatureAtOrigin_component_contDiff
    internal spacetime

theorem fixedCartanReactionCoframeCoordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedCartanReactionContact joint.1).coframe joint.2 row column := by
  exact fixedJointCoframeCoordinate_contDiff row column

theorem fixedCartanReactionGaugeConnectionCoordinate_contDiff
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      p286CoordinateEquiv
        ((fixedCartanReactionContact joint.1).gaugeConnection
          joint.2 formDirection) := by
  exact fixedJointGaugeConnectionFieldCoordinate_contDiff formDirection

theorem fixedCartanReactionGaugeAuxiliaryCoordinate_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      p286CoordinateEquiv
        ((fixedCartanReactionContact joint.1).gaugeAuxiliary joint.2 pair) := by
  exact fixedJointGaugeAuxiliaryCoordinate_contDiff pair

theorem fixedCartanReactionScalar_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedCartanReactionContact joint.1).scalar joint.2 := by
  exact fixedJointScalar_contDiff

theorem fixedCartanReactionMatterCoordinates_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      matterCoordinateEquiv
        ((fixedCartanReactionContact joint.1).matter joint.2) := by
  exact fixedJointMatterCoordinates_contDiff

theorem fixedCartanReactionConjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedCartanReactionContact joint.1).conjugateMatter
        joint.2 matter := by
  exact fixedJointConjugateMatter_apply_contDiff matter

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
