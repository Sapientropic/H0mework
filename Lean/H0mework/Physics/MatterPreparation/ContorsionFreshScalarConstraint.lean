import H0mework.Physics.Geometry.BiradialScalarOriginResponse
import H0mework.Physics.MatterPreparation.ContorsionCoherentP286GaussTangency

/-!
# S9-C3h201l: scalar constraint on the final-current fresh actual

The temporal P286 current in C3h200u is differentiated on the local actual
freshly generated from the final corrected current.  This module revalidates
the scalar Euler--Lagrange equation on that same actual and contact:

```text
final source/action-generated current
→ fresh unit-coframe contact germ
→ source-vacuum scalar and actual P286 connection jet
→ scalar divergence and algebraic term
→ scalar Euler coefficient at the common origin.
```

The P286 connection has zero origin value and zero diagonal first jet by the
existing antisymmetrized action constructor.  No scalar second jet, residual
zero, branch receipt, or fitted value is supplied.  This is the old
independent scalar constraint revalidated after the final-current epoch
change; it is not a new independent closure and is only one leg of the later
source-relative Ward balance.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshScalarConstraint

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBiradialCoframeResponse
open StageNineBiradialScalarOriginResponse
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286BFMomentumBridge
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286GaussTangency
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzSameActualConstraints
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift
open StageNineSourceGeneratedMatterSpinActionUpdate
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

local instance c3h201lP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance c3h201lP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance c3h201lP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Primitive provenance on the fresh contact germ -/

/-- The contact germ used by the temporal-current derivative retains the
unit coframe of the final current at the selected contact. -/
theorem positiveP506MatterPreContorsionFullLorentzFreshActual_coframe_one
    (point : BasePoint) :
    positiveP506MatterPreContorsionFullLorentzFreshActual.coframe point = 1 := by
  exact
    currentCanonicalFullActionLorentzActualFirstJetLift_coframe_one
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent 0
      preContorsionFullLorentzTriangularCurrent_coframe_origin point

/-- The fresh scalar is the source-generated vacuum on its whole local
domain, not merely at the contact point. -/
theorem positiveP506MatterPreContorsionFullLorentzFreshActual_scalar_vacuum :
    positiveP506MatterPreContorsionFullLorentzFreshActual.scalar =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    actionGeneratedScalarLocalField PreContorsionFullLorentzTriangularCurrent
        0 =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  have currentScalar :
      PreContorsionFullLorentzTriangularCurrent.scalar =
        fun _ =>
          sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    funext space
    change
      positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.scalar
          (canonicalCauchySlicePoint 0 space) = _
    rw [congrFun preContorsionFullLorentzTriangularActual_scalar_vacuum
      (canonicalCauchySlicePoint 0 space)]
  have currentScalarVelocity :
      PreContorsionFullLorentzTriangularCurrent.scalarVelocity = 0 := by
    funext space
    change
      fieldDirectionalDerivative
          positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.scalar
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection = 0
    rw [preContorsionFullLorentzTriangularActual_scalar_vacuum]
    simp [fieldDirectionalDerivative]
  funext point
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    cauchyScalarSpatialDerivativeCoordinate,
    currentScalar, currentScalarVelocity, Fin.sum_univ_four]

/-- The Lorentz auxiliary installer does not alter the P286 connection
generated by the established local action constructor. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_gaugeConnection_eq_sourceGenerated :
    positiveP506MatterPreContorsionFullLorentzFreshActual.gaugeConnection =
      (sourceGeneratedP286ActionLocalActualLift positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0).gaugeConnection :=
  rfl

theorem preContorsionSpatialProfileActual_gaugeConnection_origin_zero :
    preContorsionSpatialProfileActual.gaugeConnection 0 = 0 := by
  rw [congrFun preContorsionSpatialProfileActual_retains_p286Fields.1 0]
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveSourceTargetMatterCauchyState 0)).gaugeConnection 0 = 0
  rw [currentP286CompleteActionResponseOperator_gaugeConnection]
  change
    sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        positiveSourceTargetMatterCauchyState 0 0 =
      0
  funext direction
  rw [sourceGeneratedP286ActionLocalConnection_origin]
  simp [positiveSourceTargetMatterCauchyState, sourceTargetMatterCauchyState,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

theorem
    preContorsionFullLorentzTriangularCurrent_gaugeConnection_origin_zero :
    PreContorsionFullLorentzTriangularCurrent.gaugeConnection 0 = 0 := by
  rw [congrFun preContorsionFullLorentzTriangularCurrent_gaugeConnection_eq_profile
    0]
  change
    preContorsionSpatialProfileActual.gaugeConnection
        (canonicalCauchySlicePoint 0 0) =
      0
  rw [canonicalCauchySlicePoint_zero_zero,
    preContorsionSpatialProfileActual_gaugeConnection_origin_zero]

/-- The actual P286 connection vanishes at the common contact. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_connectionCoordinate_origin_zero
    (direction : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterPreContorsionFullLorentzFreshActual
        0 direction =
      0 := by
  change
    p286CoordinateEquiv
        (positiveP506MatterPreContorsionFullLorentzFreshActual.gaugeConnection
          0 direction) =
      0
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshActual_gaugeConnection_eq_sourceGenerated]
  change
    p286CoordinateEquiv
        (sourceGeneratedP286ActionLocalConnection
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent 0 0 direction) =
      0
  rw [sourceGeneratedP286ActionLocalConnection_origin,
    preContorsionFullLorentzTriangularCurrent_gaugeConnection_origin_zero]
  simp

/-- The diagonal part of the generated connection jet is zero by the
antisymmetrized action construction. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_connectionDerivative_diagonal_zero
    (direction : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506MatterPreContorsionFullLorentzFreshActual
        0 direction direction =
      0 := by
  calc
    p286GaugeConnectionCoordinateDerivative
          positiveP506MatterPreContorsionFullLorentzFreshActual
          0 direction direction =
        p286GaugeConnectionCoordinateDerivative
          (sourceGeneratedP286ActionLocalActualLift
            positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent 0)
          0 direction direction := by
      unfold p286GaugeConnectionCoordinateDerivative
        holonomicP286GaugeConnectionCoordinate
      rw [
        positiveP506MatterPreContorsionFullLorentzFreshActual_gaugeConnection_eq_sourceGenerated]
    _ =
        sourceGeneratedP286ActionLocalConnectionJet
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent 0 direction direction :=
      sourceGeneratedP286ActionLocalActualLift_connectionDerivative
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0 direction direction
    _ = 0 := by
      fin_cases direction <;>
        simp [sourceGeneratedP286ActionLocalConnectionJet]

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_conjugateMatter_origin_zero :
    positiveP506MatterPreContorsionFullLorentzFreshActual.conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent 0).conjugateMatter 0 =
      diracSpinZeroMatterCoordinate
  rw [
    currentCanonicalGravityPreservingActual_conjugateMatter_origin_eq_currentSlice,
    congrFun preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_profile
      0]
  change
    preContorsionSpatialProfileActual.conjugateMatter
        (canonicalCauchySlicePoint 0 0) =
      diracSpinZeroMatterCoordinate
  rw [canonicalCauchySlicePoint_zero_zero,
    congrFun preContorsionSpatialProfileActual_retains_matterFields.2 0,
    preContorsionP286Actual_conjugateMatter_origin]

/-! ## Scalar differential and algebraic legs -/

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarCovariantDerivative_eq_fixedVacuumAction
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        positiveP506MatterPreContorsionFullLorentzFreshActual
        point direction =
      scalarP286ActionBilinear
        (holonomicP286GaugeConnectionCoordinate
          positiveP506MatterPreContorsionFullLorentzFreshActual
          point direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarCovariantDerivative
  rw [positiveP506MatterPreContorsionFullLorentzFreshActual_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  unfold holonomicP286GaugeConnectionCoordinate
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (positiveP506MatterPreContorsionFullLorentzFreshActual.gaugeConnection
            point direction))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              (positiveP506MatterPreContorsionFullLorentzFreshActual.gaugeConnection
                point direction))))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  rw [p286CoordinateEquiv.symm_apply_apply]

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarCovariantDerivative_origin_zero
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        positiveP506MatterPreContorsionFullLorentzFreshActual
        0 direction =
      0 := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarCovariantDerivative_eq_fixedVacuumAction,
    positiveP506MatterPreContorsionFullLorentzFreshActual_connectionCoordinate_origin_zero]
  simp

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarCovariantDerivative_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative
            positiveP506MatterPreContorsionFullLorentzFreshActual
            point direction)
        0 direction =
      0 := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    holonomicP286GaugeConnectionCoordinate
      positiveP506MatterPreContorsionFullLorentzFreshActual
      point direction
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 := by
    have smooth :=
      (currentCanonicalFullActionLorentzActualFirstJetLift_smooth
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0).2.2.2.2.1 direction
    simpa [connection, holonomicP286GaugeConnectionCoordinate] using
      (smooth.differentiable (by simp)).differentiableAt
  have actionDerivative :
      fderiv ℝ
          (fun point =>
            action (connection point)
              (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
          0 =
        (action.flip
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).comp
            (fderiv ℝ connection 0) :=
    ((action.flip
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).hasFDerivAt.comp
      0 connectionDifferentiable.hasFDerivAt).fderiv
  rw [show
    (fun point =>
      holonomicScalarCovariantDerivative
        positiveP506MatterPreContorsionFullLorentzFreshActual
        point direction) =
      fun point =>
        action (connection point)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext point
    exact
      positiveP506MatterPreContorsionFullLorentzFreshActual_scalarCovariantDerivative_eq_fixedVacuumAction
        point direction]
  unfold fieldDirectionalDerivative
  rw [actionDerivative]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  change
    scalarP286ActionBilinear
        (p286GaugeConnectionCoordinateDerivative
          positiveP506MatterPreContorsionFullLorentzFreshActual
          0 direction direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      0
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshActual_connectionDerivative_diagonal_zero]
  simp

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarDivergence_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual
        direction 0 =
      0 := by
  apply scalarDifferentialMomentumDivergence_origin_eq_zero_of_biradial
      positiveSmoothUnifiedSource
      positiveP506MatterPreContorsionFullLorentzFreshActual
      (a := 1) (b := 1)
  · norm_num
  · norm_num
  · funext point
    rw [positiveP506MatterPreContorsionFullLorentzFreshActual_coframe_one,
      biradialCoframe_one_one]
  · intro formDirection
    exact
      ((holonomicScalarCovariantDerivative_contDiff
        positiveP506MatterPreContorsionFullLorentzFreshActual
        (currentCanonicalFullActionLorentzActualFirstJetLift_smooth
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent 0)
        formDirection).differentiable (by simp)).differentiableAt
  · exact
      positiveP506MatterPreContorsionFullLorentzFreshActual_scalarCovariantDerivative_diagonalDerivative_zero

/-! ## Scalar P286 current Ward leg -/

/-- Insert one P286 coordinate direction into one Lorentz component of a
gauge-connection variation.  Both indices are observation directions; this
definition carries no dynamical branch choice. -/
def p286GaugeOneFormCoordinateDirection
    (derivativeDirection : LorentzianIndex)
    (component : P286CoordinateCarrier) : P286GaugeOneForm :=
  fun formDirection =>
    if formDirection = derivativeDirection then component else 0

/-- The coordinate insertion at the fixed time direction is the canonical
temporal P286 one-form already used by the current response. -/
@[simp] theorem p286GaugeOneFormCoordinateDirection_time
    (component : P286CoordinateCarrier) :
    p286GaugeOneFormCoordinateDirection canonicalLorentzianTimeDirection
        component =
      p286TemporalGaugeOneForm component := by
  rfl

/-- A coordinate insertion at `axis.succ` is the existing canonical
single-axis spatial one-form. -/
@[simp] theorem p286GaugeOneFormCoordinateDirection_spatial
    (axis : Fin 3)
    (component : P286CoordinateCarrier) :
    p286GaugeOneFormCoordinateDirection axis.succ component =
      canonicalP286SpatialGaugeOneForm
        (p286SpatialSingleAxisDirection axis component) := by
  funext formDirection
  refine Fin.cases ?_ (fun spatialDirection => ?_) formDirection
  · have timeNeSpatial :
        (0 : LorentzianIndex) ≠ axis.succ := by
      exact (Fin.succ_ne_zero axis).symm
    simp [p286GaugeOneFormCoordinateDirection,
      canonicalP286SpatialGaugeOneForm, timeNeSpatial]
  · simp [p286GaugeOneFormCoordinateDirection,
      canonicalP286SpatialGaugeOneForm,
      p286SpatialSingleAxisDirection]

/-- The scalar orbit direction is fixed by the source vacuum and the tested
P286 Lie coordinate.  It is read from the existing representation action,
not supplied as an independent scalar variation. -/
def positiveSourceP286ScalarOrbitDirection
    (component : P286CoordinateCarrier) : ScalarCoordinateCarrier :=
  scalarP286ActionBilinear component
    (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)

/-- On the final-current fresh actual, the scalar P286 current in a single
Lorentz component is exactly the scalar differential momentum in the
representation-generated orbit direction.  This is the action identity
needed before invoking the independently checked scalar Euler equation. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_p286ScalarCurrent_coordinateDirection_eq_scalarDifferentialMomentum
    (derivativeDirection : LorentzianIndex)
    (component : P286CoordinateCarrier) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual
        (p286GaugeOneFormCoordinateDirection derivativeDirection component) =
      scalarDifferentialMomentum positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual
        (positiveSourceP286ScalarOrbitDirection component)
        derivativeDirection := by
  funext point
  have variationEq :
      holonomicScalarGaugeConnectionVariation
          positiveP506MatterPreContorsionFullLorentzFreshActual
          (fun _ =>
            p286GaugeOneFormCoordinateDirection derivativeDirection component)
          point =
        scalarVariationDifferentialDirection
          (positiveSourceP286ScalarOrbitDirection component)
          derivativeDirection := by
    funext formDirection
    unfold holonomicScalarGaugeConnectionVariation
      p286GaugeConnectionMotherVariation
    rw [congrFun
      positiveP506MatterPreContorsionFullLorentzFreshActual_scalar_vacuum point]
    by_cases sameDirection : formDirection = derivativeDirection <;>
      simp [sameDirection, p286GaugeOneFormCoordinateDirection,
        positiveSourceP286ScalarOrbitDirection,
        scalarP286ActionBilinear,
        scalarVariationDifferentialDirection]
  unfold p286ScalarCurrentCoefficient scalarDifferentialMomentum
  rw [variationEq]

/-- The four-component divergence of the scalar P286 current vanishes at
the common contact.  The zero is inherited from the scalar Euler constraint
through the exact orbit/current identity above; no current residual is
solved for a missing derivative. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_p286ScalarCurrent_divergence_origin_zero
    (component : P286CoordinateCarrier) :
    (∑ derivativeDirection : LorentzianIndex,
      fieldDirectionalDerivative
        (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshActual
          (p286GaugeOneFormCoordinateDirection derivativeDirection component))
        0 derivativeDirection) =
      0 := by
  rw [show
    (∑ derivativeDirection : LorentzianIndex,
      fieldDirectionalDerivative
        (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshActual
          (p286GaugeOneFormCoordinateDirection derivativeDirection component))
        0 derivativeDirection) =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual
        (positiveSourceP286ScalarOrbitDirection component) 0 by
    unfold scalarDifferentialMomentumDivergence
    apply Finset.sum_congr rfl
    intro derivativeDirection _
    rw [
      positiveP506MatterPreContorsionFullLorentzFreshActual_p286ScalarCurrent_coordinateDirection_eq_scalarDifferentialMomentum]]
  exact
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarDivergence_origin_zero
      (positiveSourceP286ScalarOrbitDirection component)

/-- Canonical `3+1` form of the scalar-current Ward leg on the same fresh
actual: the temporal scalar current derivative is cancelled by the three
spatial scalar-current derivatives. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_p286ScalarCurrent_temporal_add_spatialDivergence_origin_zero
    (component : P286CoordinateCarrier) :
    fieldDirectionalDerivative
        (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshActual
          (p286TemporalGaugeOneForm component))
        0 canonicalLorentzianTimeDirection +
      ∑ axis : Fin 3,
        fieldDirectionalDerivative
          (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
            positiveP506MatterPreContorsionFullLorentzFreshActual
            (canonicalP286SpatialGaugeOneForm
              (p286SpatialSingleAxisDirection axis component)))
          0 axis.succ =
      0 := by
  have divergence :=
    positiveP506MatterPreContorsionFullLorentzFreshActual_p286ScalarCurrent_divergence_origin_zero
      component
  rw [Fin.sum_univ_succ] at divergence
  have timeDirection :
      p286GaugeOneFormCoordinateDirection (0 : LorentzianIndex) component =
        p286TemporalGaugeOneForm component := by
    simpa [canonicalLorentzianTimeDirection] using
      p286GaugeOneFormCoordinateDirection_time component
  rw [timeDirection] at divergence
  simp_rw [p286GaugeOneFormCoordinateDirection_spatial] at divergence
  exact divergence

/-- The temporal scalar-current leg vanishes on its own.  The source vacuum,
unit coframe, and antisymmetric P286 connection jet make the corresponding
scalar momentum's diagonal derivative zero.  This is stronger than merely
reading a cancellation from the `3+1` Ward sum and leaves the later temporal
algebraic-current derivative entirely in the matter sector. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_p286ScalarCurrent_timeDerivative_origin_zero
    (component : P286CoordinateCarrier) :
    fieldDirectionalDerivative
        (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshActual
          (p286TemporalGaugeOneForm component))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [← p286GaugeOneFormCoordinateDirection_time component]
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshActual_p286ScalarCurrent_coordinateDirection_eq_scalarDifferentialMomentum]
  have coframeEq :
      positiveP506MatterPreContorsionFullLorentzFreshActual.coframe =
        fun _ => biradialCoframe 1 1 := by
    funext point
    rw [positiveP506MatterPreContorsionFullLorentzFreshActual_coframe_one,
      biradialCoframe_one_one]
  rw [scalarDifferentialMomentum_eq_biradialNormalForm
    positiveSmoothUnifiedSource
    positiveP506MatterPreContorsionFullLorentzFreshActual
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
    coframeEq
    (positiveSourceP286ScalarOrbitDirection component)
    canonicalLorentzianTimeDirection]
  apply
    biradialScalarDifferentialMomentumNormalForm_diagonalDerivative_eq_zero
  · intro formDirection
    exact
      ((holonomicScalarCovariantDerivative_contDiff
        positiveP506MatterPreContorsionFullLorentzFreshActual
        (currentCanonicalFullActionLorentzActualFirstJetLift_smooth
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent 0)
        formDirection).differentiable (by simp)).differentiableAt
  · exact
      positiveP506MatterPreContorsionFullLorentzFreshActual_scalarCovariantDerivative_diagonalDerivative_zero

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarKineticAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterPreContorsionFullLorentzFreshActual 0)
        (holonomicScalarVariationAlgebraicDirection
          positiveP506MatterPreContorsionFullLorentzFreshActual direction 0) =
      0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeOrigin :
      (toContinuumPointField
        positiveP506MatterPreContorsionFullLorentzFreshActual
        0).scalarCovariantDerivative =
        0 := by
    funext formDirection
    exact
      positiveP506MatterPreContorsionFullLorentzFreshActual_scalarCovariantDerivative_origin_zero
        formDirection
  rw [covariantDerivativeOrigin]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarPotential_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField
          positiveP506MatterPreContorsionFullLorentzFreshActual 0)
        direction =
      0 := by
  unfold scalarPotentialFirstVariation
  rw [show
    (toContinuumPointField
      positiveP506MatterPreContorsionFullLorentzFreshActual 0).scalar =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    exact congrFun
      positiveP506MatterPreContorsionFullLorentzFreshActual_scalar_vacuum 0]
  simp

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarYukawa_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField
          positiveP506MatterPreContorsionFullLorentzFreshActual 0)
        direction =
      0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  rw [show
    (toContinuumPointField
      positiveP506MatterPreContorsionFullLorentzFreshActual
      0).conjugateMatter =
        diracSpinZeroMatterCoordinate by
    exact
      positiveP506MatterPreContorsionFullLorentzFreshActual_conjugateMatter_origin_zero,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  norm_num

theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual
        direction 0 =
      0 := by
  unfold scalarAlgebraicDirectionalCoefficient
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarKineticAlgebraic_origin_zero,
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarPotential_origin_zero,
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarYukawa_origin_zero]
  ring

/-- The scalar equation is rechecked on the actual that supplies the
temporal P286 current germ.  Its constructor never solved this scalar
equation, so the old independent constraint survives the epoch change; the
statement itself is not counted a second time as new independent closure. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarEuler_origin
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual
        direction 0 =
      0 := by
  unfold scalarEulerLagrangeDirectionalCoefficient
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarAlgebraic_origin_zero,
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalarDivergence_origin_zero]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshScalarConstraint
