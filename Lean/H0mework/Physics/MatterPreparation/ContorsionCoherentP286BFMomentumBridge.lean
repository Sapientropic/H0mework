import H0mework.Physics.MatterPreparation.ContorsionCoherentBFMomentumRegularity

/-!
# S9-C3h200t: final-current coherent P286 BF-momentum bridge

C3h200r generated one coherent whole-domain actual from the corrected final
current, and C3h200s established its Lorentz BF regularity.  This module
performs the parallel P286 transport in the forward action direction:

```text
final-current P286 Cauchy data
→ same current-action dual as the generated profile
→ same unique BF-Legendre auxiliary velocity
→ same coherent P286 auxiliary field
→ exact whole-function BF-momentum equality
→ transported Fréchet derivative and spatial divergence.
```

The Lorentz correction changes no P286 input consumed by the current action
dual.  In particular, scalar velocity is rederived from the unchanged
source-vacuum scalar field rather than assumed as primitive slice fidelity.
No residual, inverse image, target field, branch receipt, or constraint
certificate enters the construction.

This is a transporter/readout checkpoint for the action-generated P286
momentum.  It does not yet prove P286 Gauss on the new actual, residual
tangency, constraint propagation, or a state-dependent local flow.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286BFMomentumBridge

open Filter Asymptotics
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineChangedBackgroundLorentzOriginResponseFiber
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCurrentResponse
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzSameActualConstraints
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance c3h200tP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance c3h200tP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance c3h200tP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## The Lorentz write preserves every P286 current input -/

/-- The Lorentz-only write preserves the whole P286 connection slice. -/
theorem
    preContorsionFullLorentzTriangularCurrent_gaugeConnection_eq_profile :
    PreContorsionFullLorentzTriangularCurrent.gaugeConnection =
      PreContorsionSpatialProfileCurrent.gaugeConnection := by
  funext space
  change
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gaugeConnection
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.gaugeConnection
        (canonicalCauchySlicePoint 0 space)
  rw [
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual]
  change
    (currentCanonicalFullActionLorentzCoherentDiagonalActual
      positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent).gaugeConnection
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.gaugeConnection
        (canonicalCauchySlicePoint 0 space)
  rw [coherentDiagonalActual_gaugeConnection_slice,
    preContorsionSpatialProfileCurrent_zeroStep]
  rfl

private theorem
    preContorsionFullLorentzTriangularCurrent_gaugeAuxiliary_eq_profile :
    PreContorsionFullLorentzTriangularCurrent.gaugeAuxiliary =
      PreContorsionSpatialProfileCurrent.gaugeAuxiliary := by
  funext space
  change
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space)
  rw [
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual]
  change
    (currentCanonicalFullActionLorentzCoherentDiagonalActual
      positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent).gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space)
  rw [coherentDiagonalActual_gaugeAuxiliary_slice,
    preContorsionSpatialProfileCurrent_zeroStep]
  rfl

/-- The Lorentz-only write preserves the whole primal matter slice. -/
theorem
    preContorsionFullLorentzTriangularCurrent_matter_eq_profile :
    PreContorsionFullLorentzTriangularCurrent.matter =
      PreContorsionSpatialProfileCurrent.matter := by
  funext space
  change
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.matter
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.matter
        (canonicalCauchySlicePoint 0 space)
  rw [
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_matter]
  change
    (currentCanonicalFullActionLorentzCoherentDiagonalActual
      positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent).matter
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.matter
        (canonicalCauchySlicePoint 0 space)
  rw [coherentDiagonalActual_matter_slice,
    preContorsionSpatialProfileCurrent_zeroStep]
  rfl

/-- The Lorentz-only write preserves the whole conjugate-matter slice. -/
theorem
    preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_profile :
    PreContorsionFullLorentzTriangularCurrent.conjugateMatter =
      PreContorsionSpatialProfileCurrent.conjugateMatter := by
  funext space
  change
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space)
  rw [
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual,
    changedBackgroundLorentzOriginCarrier_conjugateMatter]
  change
    (currentCanonicalFullActionLorentzCoherentDiagonalActual
      positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      preContorsionSpatialProfileActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space)
  rw [coherentDiagonalActual_conjugateMatter_slice,
    preContorsionSpatialProfileCurrent_zeroStep]
  rfl

private theorem preContorsionSpatialProfileCurrent_scalar_vacuum :
    PreContorsionSpatialProfileCurrent.scalar =
      fun _ => sourceGeneratedVacuumCoordinates
        positiveSmoothUnifiedSource := by
  funext space
  change
    preContorsionSpatialProfileActual.scalar
        (canonicalCauchySlicePoint 0 space) = _
  rw [congrFun preContorsionSpatialProfileActual_scalar_vacuum
    (canonicalCauchySlicePoint 0 space)]

private theorem preContorsionSpatialProfileCurrent_scalarVelocity_zero :
    PreContorsionSpatialProfileCurrent.scalarVelocity = 0 := by
  funext space
  change
    fieldDirectionalDerivative preContorsionSpatialProfileActual.scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection = 0
  rw [preContorsionSpatialProfileActual_scalar_vacuum]
  simp [fieldDirectionalDerivative]

/-- The C3h200n Lorentz-only write leaves the source-generated scalar vacuum
unchanged on the whole actual carrier. -/
theorem preContorsionFullLorentzTriangularActual_scalar_vacuum :
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates
        positiveSmoothUnifiedSource := by
  change
    positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates
        positiveSmoothUnifiedSource
  exact coherentProfileActual_scalar_vacuum

/-- The corrected current still carries the source-generated scalar vacuum
at every spatial contact. -/
theorem preContorsionFullLorentzTriangularCurrent_scalar_vacuum :
    PreContorsionFullLorentzTriangularCurrent.scalar =
      fun _ => sourceGeneratedVacuumCoordinates
        positiveSmoothUnifiedSource := by
  funext space
  change
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.scalar
        (canonicalCauchySlicePoint 0 space) = _
  rw [congrFun preContorsionFullLorentzTriangularActual_scalar_vacuum
    (canonicalCauchySlicePoint 0 space)]

private theorem
    preContorsionFullLorentzTriangularCurrent_scalarVelocity_zero :
    PreContorsionFullLorentzTriangularCurrent.scalarVelocity = 0 := by
  funext space
  change
    fieldDirectionalDerivative
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection = 0
  rw [preContorsionFullLorentzTriangularActual_scalar_vacuum]
  simp [fieldDirectionalDerivative]

private theorem preContorsionSpatialProfileCurrent_baseScalar_vacuum
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent space).scalar =
        fun _ =>
          sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    actionGeneratedScalarLocalField PreContorsionSpatialProfileCurrent space =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  funext point
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    cauchyScalarSpatialDerivativeCoordinate,
    preContorsionSpatialProfileCurrent_scalar_vacuum,
    preContorsionSpatialProfileCurrent_scalarVelocity_zero,
    Fin.sum_univ_four]

private theorem preContorsionFullLorentzTriangularCurrent_baseScalar_vacuum
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent space).scalar =
        fun _ =>
          sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    actionGeneratedScalarLocalField PreContorsionFullLorentzTriangularCurrent
        space =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  funext point
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    cauchyScalarSpatialDerivativeCoordinate,
    preContorsionFullLorentzTriangularCurrent_scalar_vacuum,
    preContorsionFullLorentzTriangularCurrent_scalarVelocity_zero,
    Fin.sum_univ_four]

/-! ## Same action target and unique P286 auxiliary velocity -/

private theorem
    preContorsionFullLorentzTriangularCurrent_baseP286AlgebraicCurrent_eq_profile
    (space : StageNineSpatialPoint) (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space)
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space)
        direction 0 := by
  let finalBase :=
    currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent space
  let profileBase :=
    currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent space
  have coframeEq : finalBase.coframe 0 = profileBase.coframe 0 := by
    change
      PreContorsionFullLorentzTriangularCurrent.coframe space =
        PreContorsionSpatialProfileCurrent.coframe space
    exact congrFun
      preContorsionFullLorentzTriangularCurrent_coframe_eq_profile space
  have gaugeConnectionEq :
      finalBase.gaugeConnection 0 = profileBase.gaugeConnection 0 := by
    change
      sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space 0 =
        sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space 0
    funext formDirection
    rw [sourceGeneratedP286ActionLocalConnection_origin,
      sourceGeneratedP286ActionLocalConnection_origin,
      congrFun
        preContorsionFullLorentzTriangularCurrent_gaugeConnection_eq_profile
        space]
  have gaugeAuxiliaryEq :
      finalBase.gaugeAuxiliary 0 = profileBase.gaugeAuxiliary 0 := by
    change
      PreContorsionFullLorentzTriangularCurrent.gaugeAuxiliary space =
        PreContorsionSpatialProfileCurrent.gaugeAuxiliary space
    exact congrFun
      preContorsionFullLorentzTriangularCurrent_gaugeAuxiliary_eq_profile
      space
  have scalarEq : finalBase.scalar 0 = profileBase.scalar 0 := by
    rw [preContorsionFullLorentzTriangularCurrent_baseScalar_vacuum,
      preContorsionSpatialProfileCurrent_baseScalar_vacuum]
  have scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative finalBase 0 =
        holonomicScalarCovariantDerivative profileBase 0 := by
    unfold holonomicScalarCovariantDerivative
    rw [preContorsionFullLorentzTriangularCurrent_baseScalar_vacuum,
      preContorsionSpatialProfileCurrent_baseScalar_vacuum,
      gaugeConnectionEq]
  have matterEq : finalBase.matter 0 = profileBase.matter 0 := by
    change
      (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space).matter 0 =
      (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent space).matter 0
    rw [sourceActionGeneratedJointLocalActualLift_initialMatter,
      sourceActionGeneratedJointLocalActualLift_initialMatter,
      congrFun preContorsionFullLorentzTriangularCurrent_matter_eq_profile
        space]
  have conjugateMatterEq :
      finalBase.conjugateMatter 0 = profileBase.conjugateMatter 0 := by
    change
      (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent space).conjugateMatter 0 =
      (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent space).conjugateMatter 0
    rw [sourceActionGeneratedJointLocalActualLift_initialConjugateMatter,
      sourceActionGeneratedJointLocalActualLift_initialConjugateMatter,
      congrFun
        preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_profile
        space]
  exact p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
    positiveSmoothUnifiedSource finalBase profileBase 0 coframeEq
    gaugeConnectionEq gaugeAuxiliaryEq scalarEq
    scalarCovariantDerivativeEq matterEq conjugateMatterEq direction

/-- The final current and the generated profile present the same action dual
to the P286 spatial BF-Legendre map.  The equality is derived from exactly the
local fields consumed by the action coefficient. -/
theorem
    preContorsionFullLorentzTriangularCurrent_p286SpatialActionTarget_eq_profile
    (space : StageNineSpatialPoint) :
    currentP286SpatialActionTarget positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space) =
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space) := by
  apply LinearMap.ext
  intro direction
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space)
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space)
        (canonicalP286SpatialGaugeOneForm direction) 0
  exact
    preContorsionFullLorentzTriangularCurrent_baseP286AlgebraicCurrent_eq_profile
      space (canonicalP286SpatialGaugeOneForm direction)

/-- Applying the fixed BF-Legendre inverse to that same action dual gives the
same unique P286 auxiliary velocity. -/
theorem
    preContorsionFullLorentzTriangularCurrent_p286AuxiliaryVelocity_eq_profile
    (space : StageNineSpatialPoint) :
    currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space) =
      currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space) := by
  unfold currentP286SpatialAuxiliaryVelocity
  rw [
    preContorsionFullLorentzTriangularCurrent_p286SpatialActionTarget_eq_profile]

private theorem
    preContorsionFullLorentzTriangularCurrent_baseP286OriginAuxiliary_eq_profile
    (space : StageNineSpatialPoint) :
    currentP286OriginAuxiliaryCoordinate
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space) =
      currentP286OriginAuxiliaryCoordinate
        (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent space) := by
  funext pair
  unfold currentP286OriginAuxiliaryCoordinate
  change
    p286CoordinateEquiv
        (PreContorsionFullLorentzTriangularCurrent.gaugeAuxiliary space pair) =
      p286CoordinateEquiv
        (PreContorsionSpatialProfileCurrent.gaugeAuxiliary space pair)
  rw [congrFun
    preContorsionFullLorentzTriangularCurrent_gaugeAuxiliary_eq_profile
    space]

/-! ## Exact coherent auxiliary and BF-momentum transport -/

/-- The new coherent actual and the old generated profile coherent actual
have the same coframe on the whole spacetime carrier. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_eq_profileCoherent :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe =
      positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual.coframe := by
  funext point
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_normalForm,
    coherentProfileActual_coframe_normalForm]

/-- The two coherent actuals also carry exactly the same source-generated
scalar germ.  This follows from the scalar Cauchy data before any P286
equation is tested. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_scalar_eq_profileCoherent :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.scalar =
      positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual.scalar := by
  funext point
  change
    (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent
      (canonicalSpatialProjection point)).scalar
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) =
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        PreContorsionSpatialProfileCurrent
        (canonicalSpatialProjection point)).scalar
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  rw [preContorsionFullLorentzTriangularCurrent_baseScalar_vacuum,
    preContorsionSpatialProfileCurrent_baseScalar_vacuum]

/-- The P286 auxiliary on the whole coherent carrier is unchanged.  Both
sides are generated by the same origin data and the same unique action
velocity; no endpoint field is reconstructed from a residual. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_gaugeAuxiliary_eq_profileCoherent :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gaugeAuxiliary =
      positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual.gaugeAuxiliary := by
  funext point pair
  apply p286CoordinateEquiv.injective
  change
    p286CoordinateEquiv
        ((currentCanonicalFullActionLorentzStateResponseUpdate
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent
          (canonicalTimeProjection point)).gaugeAuxiliary
          (canonicalSpatialProjection point) pair) =
      p286CoordinateEquiv
        ((currentCanonicalFullActionLorentzStateResponseUpdate
          positiveSmoothUnifiedSource
          PreContorsionSpatialProfileCurrent
          (canonicalTimeProjection point)).gaugeAuxiliary
          (canonicalSpatialProjection point) pair)
  rw [
    currentCanonicalFullActionLorentzStateResponseUpdate_p286Auxiliary_normalForm,
    currentCanonicalFullActionLorentzStateResponseUpdate_p286Auxiliary_normalForm,
    congrFun
      (preContorsionFullLorentzTriangularCurrent_baseP286OriginAuxiliary_eq_profile
        (canonicalSpatialProjection point)) pair,
    preContorsionFullLorentzTriangularCurrent_p286AuxiliaryVelocity_eq_profile]

/-- Whole-function equality of the P286 BF momentum.  This stronger
transporter lets every later derivative be taken on the actual function,
rather than replaying the old private differentiability calculation. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction =
      p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
    holonomicP286GaugeAuxiliaryCoordinate
  simp only [toContinuumPointField]
  rw [
    congrFun
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_coframe_eq_profileCoherent
      point,
    congrFun
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_gaugeAuxiliary_eq_profileCoherent
      point]

/-- The established coherent-profile Fréchet derivative is therefore a
genuine derivative of the new final-current coherent actual. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_hasFDerivAt_origin
    (direction : P286GaugeTwoForm) :
    HasFDerivAt
      (p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction)
      (((fderiv ℝ
          (p286GaugeConnectionBFDifferentialMomentum
            preContorsionSpatialProfileActual direction) 0).comp
          canonicalZeroSliceProjection) +
        (coherentProfileP286BFMomentumCorrectionCoefficient direction 0) •
          canonicalTimeProjection)
      0 := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent]
  exact coherentProfileActual_p286BFMomentum_hasFDerivAt_origin direction

/-- Every spatial derivative on the new actual agrees with the generated
profile derivative. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_spatialDerivative_eq_profile
    (axis : Fin 3) (direction : P286GaugeTwoForm) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction)
        0 axis.succ =
      fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction)
        0 axis.succ := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent]
  exact
    coherentProfileActual_p286BFMomentum_spatialDerivative_eq_profile
      axis direction

/-- Exact coherent-to-coherent spatial-divergence transport. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_eq_profileCoherent
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction 0 =
      p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction 0 := by
  unfold p286GaugeConnectionSpatialBFMomentumDivergence
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent,
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent,
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent]

/-- The new coherent actual and the C3h200n final actual have the same P286
spatial BF divergence at their common origin. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_eq_finalActual
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction 0 =
      p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
        direction 0 := by
  calc
    _ =
        p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
          direction 0 :=
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_eq_profileCoherent
        direction
    _ =
        p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
          direction 0 :=
      (fullLorentzTriangularActual_p286SpatialBFDivergence_eq_coherent
        direction).symm

/-! ## C3h200t bridge checkpoint -/

/-- Role-separated checkpoint.  Every field is a source/action transporter;
none is an independent equation or propagation receipt. -/
structure
    PositiveP506MatterPreContorsionFullLorentzFreshCoherentP286BFMomentumBridgeLaw :
    Prop where
  actionTargetTransport :
    ∀ space,
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
          (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent space) =
        currentP286SpatialActionTarget positiveSmoothUnifiedSource
          (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent space)
  wholeMomentumTransport :
    ∀ direction,
      p286GaugeConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction =
        p286GaugeConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
          direction
  finalDivergenceTransport :
    ∀ direction,
      p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction 0 =
        p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
          direction 0

theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentP286BFMomentumBridgeLaw :
    PositiveP506MatterPreContorsionFullLorentzFreshCoherentP286BFMomentumBridgeLaw where
  actionTargetTransport :=
    preContorsionFullLorentzTriangularCurrent_p286SpatialActionTarget_eq_profile
  wholeMomentumTransport :=
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent
  finalDivergenceTransport :=
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_eq_finalActual

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286BFMomentumBridge
