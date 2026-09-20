import H0mework.Physics.GaugeAction.P286TemporalGaussResidualTangency
import H0mework.Physics.MatterPreparation.ContorsionCoherentP286BaseGauss

/-!
# S9-C3h200u: temporal P286 Gauss tangency on the final-current actual

This module differentiates the complete canonical temporal-Gauss residual on
the same C3h200r actual and common contact:

```text
action-generated profile response
→ smooth coherent P286 BF momentum
→ genuine mixed time--space BF-divergence derivative
→ algebraic-current time derivative on the same actual
→ complete temporal-Gauss residual derivative.
```

The BF leg is obtained by differentiating the action-generated response, not
by solving the Gauss residual for a missing jet.  `HasDerivAt` is used
throughout, so a totalized `deriv` cannot manufacture a false zero.  The base
Gauss theorem remains producer consistency; only cancellation of the two
independently differentiable legs can establish tangency.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286GaussTangency

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineEinsteinCartanSkewCoframeActualResponseOperator
open StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator
open StageNineConnectionSectorSourceBalance
open StageNineCoframeTwoFormPairing
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286TemporalGaussResidualTangency
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286BaseGauss
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286BFMomentumBridge
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzSameActualConstraints
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCurrentResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineScalarActionCanonicalMomentumUpdate
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

open scoped ContDiff

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## Genuine mixed time--space BF regularity -/

/-- Whole-function transport from C3h200t upgrades the final-current
coherent actual to the smooth P286 BF momentum generated in C3h200o. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_contDiff
    (direction : P286GaugeTwoForm) :
    ContDiff ℝ ∞
      (p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction) := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent]
  exact coherentProfileActual_p286BFMomentum_contDiff direction

/-- A smooth scalar field has smooth directional derivative in every fixed
coordinate direction. -/
private theorem fieldDirectionalDerivative_contDiff_of_contDiff
    {field : BasePoint → ℝ}
    (smooth : ContDiff ℝ ∞ field)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      fieldDirectionalDerivative field point direction := by
  unfold fieldDirectionalDerivative
  simpa [Function.comp_def] using
    (smooth.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_prodMk_left (coordinateDirection direction))

/-- The complete three-axis spatial BF divergence on the C3h200r actual is
smooth.  This is the missing mixed-jet regularity, not its cancellation with
the algebraic current. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_contDiff
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞
      (p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        direction) := by
  unfold p286GaugeConnectionSpatialBFMomentumDivergence
  exact
    ((fieldDirectionalDerivative_contDiff_of_contDiff
      (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_contDiff
        (p286GaugeExteriorDerivativeDirection 1 direction)) 1).add
      (fieldDirectionalDerivative_contDiff_of_contDiff
        (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_contDiff
          (p286GaugeExteriorDerivativeDirection 2 direction)) 2)).add
      (fieldDirectionalDerivative_contDiff_of_contDiff
        (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_contDiff
          (p286GaugeExteriorDerivativeDirection 3 direction)) 3)

private theorem canonicalCauchyTimeLine_hasDerivAt_origin :
    HasDerivAt
      (fun time : ℝ =>
        canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
      (coordinateDirection canonicalLorentzianTimeDirection) 0 := by
  rw [show
    (fun time : ℝ =>
      canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
        fun time =>
          time • coordinateDirection canonicalLorentzianTimeDirection by
    funext time
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]]
  simpa using
    (hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const
      (coordinateDirection canonicalLorentzianTimeDirection)

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- Restricting a genuinely smooth scalar field to the canonical time line
has the actual time-direction derivative, not a totalized readout. -/
private theorem hasDerivAt_canonicalTimeTrace_origin
    {field : BasePoint → ℝ}
    (smooth : ContDiff ℝ ∞ field) :
    HasDerivAt
      (fun time =>
        field (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)))
      (fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection)
      0 := by
  have outer :
      HasFDerivAt field (fderiv ℝ field 0)
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    rw [canonicalCauchySlicePoint_zero_zero]
    exact
      (smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  simpa [Function.comp_def, fieldDirectionalDerivative] using
    outer.comp_hasDerivAt 0 canonicalCauchyTimeLine_hasDerivAt_origin

/-- Genuine mixed time--space derivative of the final-current P286 BF
divergence.  Its coefficient is deliberately left as the derivative of the
same actual field; the next cancellation theorem must derive its value. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_timeTrace_hasDerivAt_origin
    (direction : P286GaugeOneForm) :
    HasDerivAt
      (fun time =>
        p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)))
      (fieldDirectionalDerivative
        (p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction)
        0 canonicalLorentzianTimeDirection)
      0 :=
  hasDerivAt_canonicalTimeTrace_origin
    (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_contDiff
      direction)

/-! ## Algebraic-current time trace on the same generated actual -/

private theorem preContorsionFullLorentzTriangularCurrent_scalar_vacuum :
    PreContorsionFullLorentzTriangularCurrent.scalar =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
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

/-- The smooth local actual generated from `Ufinal` carries the same
source-generated scalar vacuum on its whole local domain. -/
private theorem
    positiveP506MatterPreContorsionFullLorentzFreshActual_scalar_vacuum :
    positiveP506MatterPreContorsionFullLorentzFreshActual.scalar =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent 0).scalar =
        fun _ =>
          sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  change
    actionGeneratedScalarLocalField PreContorsionFullLorentzTriangularCurrent
        0 =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  funext point
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    cauchyScalarSpatialDerivativeCoordinate,
    preContorsionFullLorentzTriangularCurrent_scalar_vacuum,
    preContorsionFullLorentzTriangularCurrent_scalarVelocity_zero,
    Fin.sum_univ_four]

private def freshLocalP286TemporalAlgebraicCurrent
    (component : P286CoordinateCarrier) : BasePoint → ℝ :=
  p286GaugeConnectionAlgebraicCurrentCoefficient
    positiveSmoothUnifiedSource
    positiveP506MatterPreContorsionFullLorentzFreshActual
    (p286TemporalGaugeOneForm component)

/-- Along the canonical time line, the algebraic current of the coherent
whole-domain actual is exactly the current of the smooth local actual
generated from the same `Ufinal` at the same contact.  This is primitive
contact fidelity, not a restart or reprojection of the judged actual. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286AlgebraicCurrent_timeTrace_eq_freshActual
    (component : P286CoordinateCarrier) :
    (fun time =>
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
        (p286TemporalGaugeOneForm component)
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))) =
      fun time =>
        freshLocalP286TemporalAlgebraicCurrent component
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) := by
  funext time
  let point :=
    canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)
  have coframeEq :
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.coframe
          point =
        positiveP506MatterPreContorsionFullLorentzFreshActual.coframe
          point := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent).coframe point =
      (currentCanonicalFullActionLorentzActualFirstJetLift
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0).coframe point
    dsimp [point]
    rw [coherentDiagonalActual_coframe_slice]
    rfl
  have gaugeConnectionEq :
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gaugeConnection
          point =
        positiveP506MatterPreContorsionFullLorentzFreshActual.gaugeConnection
          point := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent).gaugeConnection point =
      (currentCanonicalFullActionLorentzActualFirstJetLift
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0).gaugeConnection point
    dsimp [point]
    rw [coherentDiagonalActual_gaugeConnection_slice]
    rfl
  have gaugeAuxiliaryEq :
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.gaugeAuxiliary
          point =
        positiveP506MatterPreContorsionFullLorentzFreshActual.gaugeAuxiliary
          point := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent).gaugeAuxiliary point =
      (currentCanonicalFullActionLorentzActualFirstJetLift
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0).gaugeAuxiliary point
    dsimp [point]
    rw [coherentDiagonalActual_gaugeAuxiliary_slice]
    rfl
  have scalarEq :
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.scalar
          point =
        positiveP506MatterPreContorsionFullLorentzFreshActual.scalar
          point := by
    rw [
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_scalar_vacuum,
      positiveP506MatterPreContorsionFullLorentzFreshActual_scalar_vacuum]
  have scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual point =
        holonomicScalarCovariantDerivative
          positiveP506MatterPreContorsionFullLorentzFreshActual point := by
    unfold holonomicScalarCovariantDerivative
    rw [
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_scalar_vacuum,
      positiveP506MatterPreContorsionFullLorentzFreshActual_scalar_vacuum,
      gaugeConnectionEq]
  have matterEq :
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.matter
          point =
        positiveP506MatterPreContorsionFullLorentzFreshActual.matter
          point := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent).matter point =
      (currentCanonicalFullActionLorentzActualFirstJetLift
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0).matter point
    dsimp [point]
    rw [coherentDiagonalActual_matter_slice]
    rfl
  have conjugateMatterEq :
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
          point =
        positiveP506MatterPreContorsionFullLorentzFreshActual.conjugateMatter
          point := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent).conjugateMatter point =
      (currentCanonicalFullActionLorentzActualFirstJetLift
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0).conjugateMatter point
    dsimp [point]
    rw [coherentDiagonalActual_conjugateMatter_slice]
    rfl
  exact
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
      positiveSmoothUnifiedSource
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
      positiveP506MatterPreContorsionFullLorentzFreshActual point
      coframeEq gaugeConnectionEq gaugeAuxiliaryEq scalarEq
      scalarCovariantDerivativeEq matterEq conjugateMatterEq
      (p286TemporalGaugeOneForm component)

private theorem freshLocalP286TemporalAlgebraicCurrent_contDiff
    (component : P286CoordinateCarrier) :
    ContDiff ℝ ∞
      (freshLocalP286TemporalAlgebraicCurrent component) := by
  exact
    p286GaugeConnectionAlgebraicCurrentCoefficient_contDiff
      positiveSmoothUnifiedSource
      positiveP506MatterPreContorsionFullLorentzFreshActual
      (currentCanonicalFullActionLorentzActualFirstJetLift_smooth
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0)
      (currentCanonicalFullActionLorentzActualFirstJetLift_nondegenerate
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0
        preContorsionFullLorentzTriangularCurrent_coframe_origin)
      (p286TemporalGaugeOneForm component)

/-- Genuine algebraic-current time derivative of the same coherent actual,
transported only to the smooth local actual generated from the same current
at the same contact. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286AlgebraicCurrent_timeTrace_hasDerivAt_origin
    (component : P286CoordinateCarrier) :
    HasDerivAt
      (fun time =>
        p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          (p286TemporalGaugeOneForm component)
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)))
      (fieldDirectionalDerivative
        (freshLocalP286TemporalAlgebraicCurrent component)
        0 canonicalLorentzianTimeDirection)
      0 := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286AlgebraicCurrent_timeTrace_eq_freshActual]
  exact hasDerivAt_canonicalTimeTrace_origin
    (freshLocalP286TemporalAlgebraicCurrent_contDiff component)

/-! ## Complete residual derivative mouth -/

/-- The complete temporal-Gauss residual trace is genuinely differentiable.
The displayed coefficient keeps the algebraic and BF responsibilities
separate; proving it zero is the independent tangency gate. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286TemporalGaussResidual_timeTrace_hasDerivAt_origin
    (component : P286CoordinateCarrier) :
    HasDerivAt
      (p286TemporalGaussResidualTimeTrace positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshCoherentActual 0
        component)
      (fieldDirectionalDerivative
          (freshLocalP286TemporalAlgebraicCurrent component)
          0 canonicalLorentzianTimeDirection -
        fieldDirectionalDerivative
          (p286GaugeConnectionSpatialBFMomentumDivergence
            positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
            (p286TemporalGaugeOneForm component))
          0 canonicalLorentzianTimeDirection)
      0 := by
  change HasDerivAt
    (fun time =>
      p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          (p286TemporalGaugeOneForm component)
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) -
        p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          (p286TemporalGaugeOneForm component)
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)))
    _ 0
  exact
    (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286AlgebraicCurrent_timeTrace_hasDerivAt_origin
      component).sub
      (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_timeTrace_hasDerivAt_origin
        (p286TemporalGaugeOneForm component))

/-! ## Action-generated BF response normal form -/

private theorem fieldDirectionalDerivative_add_real_of_contDiff
    (first second : BasePoint → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate =>
        first candidate + second candidate) point direction =
      fieldDirectionalDerivative first point direction +
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

private theorem fieldDirectionalDerivative_comp_zeroSlice_time
    (field : BasePoint → ℝ)
    (smooth : ContDiff ℝ ∞ field)
    (point : BasePoint) :
    fieldDirectionalDerivative
        (field ∘ canonicalZeroSliceProjection)
        point canonicalLorentzianTimeDirection =
      0 := by
  have outer :
      HasFDerivAt field
        (fderiv ℝ field (canonicalZeroSliceProjection point))
        (canonicalZeroSliceProjection point) :=
    (smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have composed := outer.comp point canonicalZeroSliceProjection.hasFDerivAt
  unfold fieldDirectionalDerivative
  rw [composed.fderiv, ContinuousLinearMap.comp_apply,
    canonicalZeroSliceProjection_coordinateTime]
  simp

private theorem
    coherentProfileP286BFMomentumCorrectionCoefficient_zeroSliceInvariant
    (direction : P286GaugeTwoForm) :
    coherentProfileP286BFMomentumCorrectionCoefficient direction ∘
        canonicalZeroSliceProjection =
      coherentProfileP286BFMomentumCorrectionCoefficient direction := by
  funext point
  simp [coherentProfileP286BFMomentumCorrectionCoefficient]

private theorem
    coherentProfileP286BFMomentumCorrectionCoefficient_timeDerivative_zero
    (direction : P286GaugeTwoForm)
    (point : BasePoint) :
    fieldDirectionalDerivative
        (coherentProfileP286BFMomentumCorrectionCoefficient direction)
        point canonicalLorentzianTimeDirection =
      0 := by
  rw [←
    coherentProfileP286BFMomentumCorrectionCoefficient_zeroSliceInvariant
      direction]
  exact fieldDirectionalDerivative_comp_zeroSlice_time
    (coherentProfileP286BFMomentumCorrectionCoefficient direction)
    (coherentProfileP286BFMomentumCorrectionCoefficient_contDiff direction)
    point

private theorem fieldDirectionalDerivative_time_mul_timeInvariant
    (coefficient : BasePoint → ℝ)
    (smooth : ContDiff ℝ ∞ coefficient)
    (point : BasePoint)
    (timeDerivativeZero :
      fieldDirectionalDerivative coefficient point
        canonicalLorentzianTimeDirection = 0) :
    fieldDirectionalDerivative
        (fun candidate =>
          canonicalTimeProjection candidate * coefficient candidate)
        point canonicalLorentzianTimeDirection =
      coefficient point := by
  unfold fieldDirectionalDerivative at timeDerivativeZero ⊢
  let timeCoordinate :=
    localBaseCoordinate canonicalLorentzianTimeDirection
  have timeDifferentiable : DifferentiableAt ℝ timeCoordinate point :=
    timeCoordinate.differentiable.differentiableAt
  have coefficientDifferentiable : DifferentiableAt ℝ coefficient point :=
    (smooth.differentiable (by simp)).differentiableAt
  change
    fderiv ℝ
        (fun candidate =>
          timeCoordinate candidate * coefficient candidate)
        point (coordinateDirection canonicalLorentzianTimeDirection) =
      coefficient point
  rw [fderiv_fun_mul timeDifferentiable coefficientDifferentiable,
    timeCoordinate.hasFDerivAt.fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul]
  rw [timeDerivativeZero]
  simp [timeCoordinate, localBaseCoordinate, coordinateDirection,
    canonicalLorentzianTimeDirection]

/-- The physical-time derivative of the whole P286 BF momentum on the
final-current actual is exactly the action-generated correction coefficient.
This is a response law: the coefficient comes from the spatial action dual
and its unique BF-Legendre inverse, not from the Gauss residual. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_timeDerivative_eq_actionCorrection
    (direction : P286GaugeTwoForm)
    (point : BasePoint) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          direction)
        point canonicalLorentzianTimeDirection =
      coherentProfileP286BFMomentumCorrectionCoefficient direction point := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_eq_profileCoherent]
  let profilePullback : BasePoint → ℝ := fun candidate =>
    p286GaugeConnectionBFDifferentialMomentum
      preContorsionSpatialProfileActual direction
      (canonicalZeroSliceProjection candidate)
  let timeCorrection : BasePoint → ℝ := fun candidate =>
    canonicalTimeProjection candidate *
      coherentProfileP286BFMomentumCorrectionCoefficient direction candidate
  have momentumNormalForm :
      p286GaugeConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
          direction =
        fun candidate =>
          profilePullback candidate + timeCorrection candidate := by
    funext candidate
    exact coherentProfileActual_p286BFMomentum_normalForm direction candidate
  have profileSmooth : ContDiff ℝ ∞ profilePullback :=
    (p286GaugeConnectionBFDifferentialMomentum_contDiff
      preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth
      preContorsionSpatialProfileActual_nondegenerate direction).comp
        canonicalZeroSliceProjection.contDiff
  have correctionSmooth :
      ContDiff ℝ ∞
        (coherentProfileP286BFMomentumCorrectionCoefficient direction) :=
    coherentProfileP286BFMomentumCorrectionCoefficient_contDiff direction
  have timeCorrectionSmooth : ContDiff ℝ ∞ timeCorrection :=
    canonicalTimeProjection.contDiff.mul correctionSmooth
  rw [momentumNormalForm,
    fieldDirectionalDerivative_add_real_of_contDiff
      profilePullback timeCorrection profileSmooth timeCorrectionSmooth]
  have profileTimeZero :
      fieldDirectionalDerivative profilePullback point
          canonicalLorentzianTimeDirection =
        0 := by
    exact fieldDirectionalDerivative_comp_zeroSlice_time
      (p286GaugeConnectionBFDifferentialMomentum
        preContorsionSpatialProfileActual direction)
      (p286GaugeConnectionBFDifferentialMomentum_contDiff
        preContorsionSpatialProfileActual
        preContorsionSpatialProfileActual_smooth
        preContorsionSpatialProfileActual_nondegenerate direction)
      point
  have correctionTime :
      fieldDirectionalDerivative timeCorrection point
          canonicalLorentzianTimeDirection =
        coherentProfileP286BFMomentumCorrectionCoefficient direction point := by
    exact fieldDirectionalDerivative_time_mul_timeInvariant
      (coherentProfileP286BFMomentumCorrectionCoefficient direction)
      correctionSmooth
      point
      (coherentProfileP286BFMomentumCorrectionCoefficient_timeDerivative_zero
        direction point)
  rw [profileTimeZero, correctionTime, zero_add]

/-- Schwarz symmetry for real-valued coordinate derivatives.  The existing
P286-coordinate version cannot be applied to the scalar BF momentum
readout, so this is the dependency-local scalar specialization. -/
private theorem mixedFieldDirectionalDerivative_comm_real
    (field : BasePoint → ℝ)
    (smooth : ContDiff ℝ ∞ field)
    (point : BasePoint)
    (first second : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => fieldDirectionalDerivative field candidate first)
        point second =
      fieldDirectionalDerivative
        (fun candidate => fieldDirectionalDerivative field candidate second)
        point first := by
  have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ field) :=
    smooth.fderiv_right (m := ∞) (by simp)
  have derivativeDifferentiable :
      DifferentiableAt ℝ (fderiv ℝ field) point :=
    (derivativeSmooth.differentiable (by simp)).differentiableAt
  have evaluatedSecondDerivative
      (inner outer : LorentzianIndex) :
      fderiv ℝ
          (fun candidate =>
            fderiv ℝ field candidate (coordinateDirection inner))
          point (coordinateDirection outer) =
        fderiv ℝ (fderiv ℝ field) point
          (coordinateDirection outer)
          (coordinateDirection inner) := by
    let evaluation :
        (BasePoint →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ (coordinateDirection inner)
    have hEvaluation : HasFDerivAt
        (fun candidate => evaluation (fderiv ℝ field candidate))
        (evaluation.comp (fderiv ℝ (fderiv ℝ field) point)) point := by
      exact evaluation.hasFDerivAt.comp point
        derivativeDifferentiable.hasFDerivAt
    have evaluated := congrArg
      (fun derivative : BasePoint →L[ℝ] ℝ =>
        derivative (coordinateDirection outer))
      hEvaluation.fderiv
    change
      fderiv ℝ
          (fun candidate =>
            fderiv ℝ field candidate (coordinateDirection inner))
          point (coordinateDirection outer) =
        fderiv ℝ (fderiv ℝ field) point
          (coordinateDirection outer)
          (coordinateDirection inner)
      at evaluated
    exact evaluated
  have symmetricSecond : IsSymmSndFDerivAt ℝ field point :=
    smooth.contDiffAt.isSymmSndFDerivAt (by
      have finiteOrder : (2 : WithTop ℕ∞) ≤ ∞ :=
        WithTop.coe_le_coe.2 (OrderTop.le_top _)
      simpa [minSmoothness] using finiteOrder)
  unfold fieldDirectionalDerivative
  calc
    fderiv ℝ
        (fun candidate =>
          fderiv ℝ field candidate (coordinateDirection first))
        point (coordinateDirection second) =
      fderiv ℝ (fderiv ℝ field) point
        (coordinateDirection second)
        (coordinateDirection first) :=
      evaluatedSecondDerivative first second
    _ =
      fderiv ℝ (fderiv ℝ field) point
        (coordinateDirection first)
        (coordinateDirection second) :=
      symmetricSecond.eq
        (coordinateDirection second)
        (coordinateDirection first)
    _ =
      fderiv ℝ
        (fun candidate =>
          fderiv ℝ field candidate (coordinateDirection second))
        point (coordinateDirection first) :=
      (evaluatedSecondDerivative second first).symm

private theorem liftGaugeTwoFormOperator_id_p286_local
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator
        (LinearMap.id : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) form = form := by
  funext output
  unfold liftGaugeTwoFormOperator gaugeOperatorCoefficient
  simp

/-- At the identity coframe, the fixed `3+1` conventions identify the
BF-Legendre pairing of one spatial auxiliary velocity with the exterior
derivative of a temporal test component.  This pins the sign before any Ward
or propagation argument is attempted. -/
private theorem
    p286HodgePairing_spatialVelocityEmbedding_exteriorTemporal
    (velocity : P286SpatialGaugeDirection)
    (axis : Fin 3)
    (component : P286CoordinateCarrier) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1
        (p286SpatialAuxiliaryVelocityEmbedding velocity)
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component)) =
      p286CoordinateLiePairing (velocity axis) component := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286_local]
  rw [Fin.sum_univ_six]
  fin_cases axis <;>
    simp [p286SpatialAuxiliaryVelocityEmbedding,
      p286GaugeExteriorDerivativeDirection,
      p286TemporalGaugeOneForm,
      canonicalLorentzianTimeDirection,
      liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond]

private theorem p286CoordinateLiePairing_neg_right_local
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first (-second) =
      -p286CoordinateLiePairing first second := by
  rw [show -second = (-1 : ℝ) • second by simp,
    p286CoordinateLiePairing_smul_right]
  ring

/-- Along any skew-coframe axis, the BF pairing of a spatial auxiliary
velocity with the exterior derivative of a temporal component acquires
exactly the oriented determinant factor.  This is the geometric input that
prevents a first-order coframe term from being mistaken for current
transport. -/
private theorem
    skewCoframeAxis_p286HodgePairing_spatialVelocity_exteriorTemporal
    (coordinates : Fin 6 → ℝ)
    (parameter : ℝ)
    (velocity : P286SpatialGaugeDirection)
    (axis : Fin 3)
    (component : P286CoordinateCarrier) :
    p286GaugeAuxiliaryHodgePairingPolynomial
        (skewCoframeAxis coordinates parameter)
        (p286SpatialAuxiliaryVelocityEmbedding velocity)
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component)) =
      Matrix.det (skewCoframeAxis coordinates parameter) *
        p286CoordinateLiePairing (velocity axis) component := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [Fin.sum_univ_six]
  fin_cases axis <;>
    simp [liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      coframeTwoFormLinear, coframeWedge, skewCoframeAxis,
      p286SpatialAuxiliaryVelocityEmbedding,
      p286GaugeExteriorDerivativeDirection,
      p286TemporalGaugeOneForm,
      canonicalLorentzianTimeDirection,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      Matrix.one_apply,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      p286CoordinateLiePairing_add_left,
      p286CoordinateLiePairing_smul_left,
      p286CoordinateLiePairing_smul_right,
      p286CoordinateLiePairing_neg_right_local,
      Fin.sum_univ_six]
  all_goals
    rw [skewCoframeAxis_det]
    simp [skewCoframeAxisNormSq, skewCoframeAxisPfaffian,
      Fin.sum_univ_six]
    ring

def p286SpatialSingleAxisDirection
    (axis : Fin 3)
    (component : P286CoordinateCarrier) :
    P286SpatialGaugeDirection :=
  fun candidate => if candidate = axis then component else 0

private theorem
    p286SpatialBFLegendreDualOperator_singleAxis
    (velocity : P286SpatialGaugeDirection)
    (axis : Fin 3)
    (component : P286CoordinateCarrier) :
    p286SpatialBFLegendreDualOperator velocity
        (p286SpatialSingleAxisDirection axis component) =
      -p286CoordinateLiePairing (velocity axis) component := by
  rw [p286SpatialBFLegendreDualOperator_apply, Fin.sum_univ_three]
  fin_cases axis <;>
    simp [p286SpatialSingleAxisDirection]

/-- At the common contact, the action-generated BF response coefficient is
the negative spatial algebraic-current component selected by the same axis
and internal direction.  This fixes the Hamiltonian sign at value level;
the following tangency proof must still transport the genuine spatial
derivative rather than differentiating this point equality. -/
theorem
    coherentProfileP286BFMomentumCorrectionCoefficient_origin_eq_neg_spatialActionCurrent
    (axis : Fin 3)
    (component : P286CoordinateCarrier) :
    coherentProfileP286BFMomentumCorrectionCoefficient
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component))
        0 =
      -p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        preContorsionSpatialProfileActual
        (canonicalP286SpatialGaugeOneForm
          (p286SpatialSingleAxisDirection axis component))
        0 := by
  let base :=
    currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent 0
  let velocity :=
    currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource base
  let spatialDirection :=
    p286SpatialSingleAxisDirection axis component
  have responseAtDirection := LinearMap.congr_fun
    (currentP286SpatialAuxiliaryVelocity_response
      positiveSmoothUnifiedSource base)
    spatialDirection
  have actionTargetAtDirection :
      currentP286SpatialActionTarget positiveSmoothUnifiedSource base
          spatialDirection =
        p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource preContorsionSpatialProfileActual
          (canonicalP286SpatialGaugeOneForm spatialDirection) 0 := by
    simpa [base, canonicalCauchySlicePoint_zero_zero] using
      preContorsionSpatialProfileCurrent_baseP286SpatialActionTarget_apply_eq_profileSlice
        0 spatialDirection
  have pairingEq :
      p286CoordinateLiePairing (velocity axis) component =
        -p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource preContorsionSpatialProfileActual
          (canonicalP286SpatialGaugeOneForm spatialDirection) 0 := by
    rw [
      p286SpatialBFLegendreDualOperator_singleAxis
        velocity axis component,
      actionTargetAtDirection] at responseAtDirection
    linarith
  unfold coherentProfileP286BFMomentumCorrectionCoefficient
  rw [show canonicalZeroSliceProjection (0 : BasePoint) = 0 by
      exact LinearMap.map_zero _,
    show canonicalSpatialProjection (0 : BasePoint) = 0 by
      exact LinearMap.map_zero _]
  have volumeOne :
      generatedVolumeDensity
          (toContinuumPointField preContorsionSpatialProfileActual 0) =
        1 := by
    unfold generatedVolumeDensity
    rw [show
      (toContinuumPointField preContorsionSpatialProfileActual 0).coframe =
        1 by
      exact preContorsionSpatialProfileActual_coframe_origin]
    simp
  change
    generatedVolumeDensity
        (toContinuumPointField preContorsionSpatialProfileActual 0) *
      p286GaugeAuxiliaryHodgePairingPolynomial
        (preContorsionSpatialProfileActual.coframe 0)
        (p286SpatialAuxiliaryVelocityEmbedding velocity)
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component)) =
      _
  rw [volumeOne, one_mul,
    preContorsionSpatialProfileActual_coframe_origin,
    p286HodgePairing_spatialVelocityEmbedding_exteriorTemporal
      velocity axis component,
    pairingEq]

/-- Along a generated spatial axis, the complete BF correction coefficient
is the negative action-current readout times the square of the actual
skew-coframe determinant.  The action target is recomputed from the current
state at every contact; no residual field or endpoint coefficient is used to
construct it. -/
theorem
    coherentProfileP286BFMomentumCorrectionCoefficient_axisTrace_eq_neg_det_sq_actionTarget
    (axis : Fin 3)
    (component : P286CoordinateCarrier)
    (parameter : ℝ) :
    coherentProfileP286BFMomentumCorrectionCoefficient
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component))
        (parameter • coordinateDirection axis.succ) =
      -(Matrix.det
          (skewCoframeAxis
            (generatedSpatialSkewCoframeJet axis) parameter) ^ 2 *
        currentP286SpatialActionTarget positiveSmoothUnifiedSource
          (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent
            (canonicalSpatialProjection
              (parameter • coordinateDirection axis.succ)))
          (p286SpatialSingleAxisDirection axis component)) := by
  let point : BasePoint :=
    parameter • coordinateDirection axis.succ
  let base :=
    currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent
      (canonicalSpatialProjection point)
  let velocity :=
    currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource base
  let spatialDirection :=
    p286SpatialSingleAxisDirection axis component
  have responseAtDirection := LinearMap.congr_fun
    (currentP286SpatialAuxiliaryVelocity_response
      positiveSmoothUnifiedSource base)
    spatialDirection
  have pairingEq :
      p286CoordinateLiePairing (velocity axis) component =
        -currentP286SpatialActionTarget positiveSmoothUnifiedSource
          base spatialDirection := by
    rw [
      p286SpatialBFLegendreDualOperator_singleAxis
        velocity axis component] at responseAtDirection
    linarith
  have zeroSlice :
      canonicalZeroSliceProjection point = point := by
    dsimp [point]
    rw [map_smul, canonicalZeroSliceProjection_coordinateSpatial]
  have coframeAxis :
      preContorsionSpatialProfileActual.coframe point =
        skewCoframeAxis
          (generatedSpatialSkewCoframeJet axis) parameter := by
    dsimp [point]
    change
      (skewCoframeActual
        (spatialSkewCoframeJetLift
          generatedSpatialSkewCoframeJet)).coframe
          (parameter • coordinateDirection axis.succ) =
        _
    rw [skewCoframeActual_axis_eq,
      spatialSkewCoframeJetLift_spatial]
  unfold coherentProfileP286BFMomentumCorrectionCoefficient
  rw [show
      canonicalZeroSliceProjection
          (parameter • coordinateDirection axis.succ) =
        point by simpa [point] using zeroSlice,
    coframeAxis]
  change
    |Matrix.det
        (preContorsionSpatialProfileActual.coframe point)| *
      p286GaugeAuxiliaryHodgePairingPolynomial
        (skewCoframeAxis
          (generatedSpatialSkewCoframeJet axis) parameter)
        (p286SpatialAuxiliaryVelocityEmbedding velocity)
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component)) =
      _
  rw [coframeAxis]
  rw [
    skewCoframeAxis_p286HodgePairing_spatialVelocity_exteriorTemporal,
    abs_of_pos (skewCoframeAxis_det_pos
      (generatedSpatialSkewCoframeJet axis) parameter),
    pairingEq]
  dsimp [base, velocity, spatialDirection, point]
  ring

/-- The preceding action-target trace is the actual spatial algebraic
current of the same P506 profile at the same contact.  This is lineage/contact
transport only; the current is still generated by the full action target. -/
theorem
    coherentProfileP286BFMomentumCorrectionCoefficient_axisTrace_eq_neg_det_sq_spatialCurrent
    (axis : Fin 3)
    (component : P286CoordinateCarrier)
    (parameter : ℝ) :
    coherentProfileP286BFMomentumCorrectionCoefficient
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component))
        (parameter • coordinateDirection axis.succ) =
      -(Matrix.det
          (skewCoframeAxis
            (generatedSpatialSkewCoframeJet axis) parameter) ^ 2 *
        p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource preContorsionSpatialProfileActual
          (canonicalP286SpatialGaugeOneForm
            (p286SpatialSingleAxisDirection axis component))
          (parameter • coordinateDirection axis.succ)) := by
  rw [
    coherentProfileP286BFMomentumCorrectionCoefficient_axisTrace_eq_neg_det_sq_actionTarget,
    preContorsionSpatialProfileCurrent_baseP286SpatialActionTarget_apply_eq_profileSlice]
  congr 3
  rw [← canonicalZeroSliceProjection_apply]
  rw [map_smul, canonicalZeroSliceProjection_coordinateSpatial]

/-- The spatial derivative of the coherent BF correction is the negative
spatial derivative of the same action-generated algebraic-current component.
The determinant square is an actual geometric factor whose value is one and
whose derivative is zero at the contact; it is not silently discarded. -/
theorem
    coherentProfileP286BFMomentumCorrectionCoefficient_spatialDerivative_eq_neg_spatialCurrentDerivative
    (axis : Fin 3)
    (component : P286CoordinateCarrier) :
    fieldDirectionalDerivative
        (coherentProfileP286BFMomentumCorrectionCoefficient
          (p286GaugeExteriorDerivativeDirection axis.succ
            (p286TemporalGaugeOneForm component)))
        0 axis.succ =
      -fieldDirectionalDerivative
        (p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource preContorsionSpatialProfileActual
          (canonicalP286SpatialGaugeOneForm
            (p286SpatialSingleAxisDirection axis component)))
        0 axis.succ := by
  let correction : BasePoint → ℝ :=
    coherentProfileP286BFMomentumCorrectionCoefficient
      (p286GaugeExteriorDerivativeDirection axis.succ
        (p286TemporalGaugeOneForm component))
  let current : BasePoint → ℝ :=
    p286GaugeConnectionAlgebraicCurrentCoefficient
      positiveSmoothUnifiedSource preContorsionSpatialProfileActual
      (canonicalP286SpatialGaugeOneForm
        (p286SpatialSingleAxisDirection axis component))
  let line : ℝ → BasePoint := fun parameter =>
    parameter • coordinateDirection axis.succ
  let determinant : ℝ → ℝ := fun parameter =>
    Matrix.det
      (skewCoframeAxis
        (generatedSpatialSkewCoframeJet axis) parameter)
  have lineDerivative :
      HasDerivAt line (coordinateDirection axis.succ) 0 := by
    simpa [line] using
      (hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const
        (coordinateDirection axis.succ)
  have correctionSmooth : ContDiff ℝ ∞ correction :=
    coherentProfileP286BFMomentumCorrectionCoefficient_contDiff
      (p286GaugeExteriorDerivativeDirection axis.succ
        (p286TemporalGaugeOneForm component))
  have currentSmooth : ContDiff ℝ ∞ current :=
    p286GaugeConnectionAlgebraicCurrentCoefficient_contDiff
      positiveSmoothUnifiedSource preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth
      preContorsionSpatialProfileActual_nondegenerate
      (canonicalP286SpatialGaugeOneForm
        (p286SpatialSingleAxisDirection axis component))
  have correctionComposition :
      HasDerivAt (correction ∘ line)
        (fieldDirectionalDerivative correction 0 axis.succ) 0 := by
    have outer :
        HasFDerivAt correction (fderiv ℝ correction 0) (line 0) := by
      simpa [line] using
        (correctionSmooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    simpa [fieldDirectionalDerivative] using
      outer.comp_hasDerivAt 0 lineDerivative
  have currentComposition :
      HasDerivAt (current ∘ line)
        (fieldDirectionalDerivative current 0 axis.succ) 0 := by
    have outer :
        HasFDerivAt current (fderiv ℝ current 0) (line 0) := by
      simpa [line] using
        (currentSmooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    simpa [fieldDirectionalDerivative] using
      outer.comp_hasDerivAt 0 lineDerivative
  have determinantDerivative :
      HasDerivAt determinant 0 0 := by
    simpa [determinant] using
      skewCoframeAxis_det_hasDerivAt_zero
        (generatedSpatialSkewCoframeJet axis)
  have determinantOrigin : determinant 0 = 1 := by
    simp [determinant]
  have determinantSquareDerivative :
      HasDerivAt
        (fun parameter =>
          determinant parameter * determinant parameter) 0 0 := by
    have raw := determinantDerivative.mul determinantDerivative
    have rawZero : HasDerivAt (determinant * determinant) 0 0 :=
      raw.congr_deriv (by ring)
    apply rawZero.congr_of_eventuallyEq
    filter_upwards with parameter
    rfl
  have targetDerivative :
      HasDerivAt
        (fun parameter =>
          -((determinant parameter * determinant parameter) *
            current (line parameter)))
        (-fieldDirectionalDerivative current 0 axis.succ) 0 := by
    have raw :=
      (determinantSquareDerivative.mul currentComposition).neg
    have rawCoefficient :
        HasDerivAt
          (-((fun parameter =>
              determinant parameter * determinant parameter) *
            (current ∘ line)))
          (-fieldDirectionalDerivative current 0 axis.succ) 0 :=
      raw.congr_deriv (by
        rw [determinantOrigin]
        ring)
    apply rawCoefficient.congr_of_eventuallyEq
    filter_upwards with parameter
    rfl
  have traceEquality :
      correction ∘ line =
        fun parameter =>
          -((determinant parameter * determinant parameter) *
            current (line parameter)) := by
    funext parameter
    simpa [pow_two] using
      coherentProfileP286BFMomentumCorrectionCoefficient_axisTrace_eq_neg_det_sq_spatialCurrent
        axis component parameter
  rw [traceEquality] at correctionComposition
  exact correctionComposition.unique targetDerivative

/-- The mixed physical-time derivative of the complete spatial BF
divergence is the spatial divergence of the action-generated response
coefficient.  This is the exact BF leg required by Gauss propagation; it is
not a restatement of base Gauss acceptance. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_timeDerivative_eq_actionCorrectionDivergence
    (component : P286CoordinateCarrier) :
    fieldDirectionalDerivative
        (p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          (p286TemporalGaugeOneForm component))
        0 canonicalLorentzianTimeDirection =
      ∑ axis : Fin 3,
        fieldDirectionalDerivative
          (coherentProfileP286BFMomentumCorrectionCoefficient
            (p286GaugeExteriorDerivativeDirection axis.succ
              (p286TemporalGaugeOneForm component)))
          0 axis.succ := by
  let momentum (axis : Fin 3) : BasePoint → ℝ :=
    p286GaugeConnectionBFDifferentialMomentum
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
      (p286GaugeExteriorDerivativeDirection axis.succ
        (p286TemporalGaugeOneForm component))
  have momentumSmooth (axis : Fin 3) :
      ContDiff ℝ ∞ (momentum axis) :=
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_contDiff
      (p286GaugeExteriorDerivativeDirection axis.succ
        (p286TemporalGaugeOneForm component))
  have spatialDerivativeSmooth (axis : Fin 3) :
      ContDiff ℝ ∞ fun point =>
        fieldDirectionalDerivative (momentum axis) point axis.succ :=
    fieldDirectionalDerivative_contDiff_of_contDiff
      (momentumSmooth axis) axis.succ
  change
    fieldDirectionalDerivative
        (fun point =>
          (fieldDirectionalDerivative (momentum 0) point 1 +
            fieldDirectionalDerivative (momentum 1) point 2) +
          fieldDirectionalDerivative (momentum 2) point 3)
        0 canonicalLorentzianTimeDirection =
      _
  rw [fieldDirectionalDerivative_add_real_of_contDiff
      (fun point =>
        fieldDirectionalDerivative (momentum 0) point 1 +
          fieldDirectionalDerivative (momentum 1) point 2)
      (fun point => fieldDirectionalDerivative (momentum 2) point 3)
      ((spatialDerivativeSmooth 0).add (spatialDerivativeSmooth 1))
      (spatialDerivativeSmooth 2),
    fieldDirectionalDerivative_add_real_of_contDiff
      (fun point => fieldDirectionalDerivative (momentum 0) point 1)
      (fun point => fieldDirectionalDerivative (momentum 1) point 2)
      (spatialDerivativeSmooth 0)
      (spatialDerivativeSmooth 1)]
  rw [
    mixedFieldDirectionalDerivative_comm_real
      (momentum 0) (momentumSmooth 0) 0 1
        canonicalLorentzianTimeDirection,
    mixedFieldDirectionalDerivative_comm_real
      (momentum 1) (momentumSmooth 1) 0 2
        canonicalLorentzianTimeDirection,
    mixedFieldDirectionalDerivative_comm_real
      (momentum 2) (momentumSmooth 2) 0 3
        canonicalLorentzianTimeDirection]
  have timeDerivativeFunction (axis : Fin 3) :
      (fun point =>
        fieldDirectionalDerivative (momentum axis) point
          canonicalLorentzianTimeDirection) =
        coherentProfileP286BFMomentumCorrectionCoefficient
          (p286GaugeExteriorDerivativeDirection axis.succ
            (p286TemporalGaugeOneForm component)) := by
    funext point
    exact
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286BFMomentum_timeDerivative_eq_actionCorrection
        (p286GaugeExteriorDerivativeDirection axis.succ
          (p286TemporalGaugeOneForm component))
        point
  rw [timeDerivativeFunction 0, timeDerivativeFunction 1,
    timeDerivativeFunction 2, Fin.sum_univ_three]
  rfl

/-- Summing the three independently transported axes identifies the mixed BF
leg with minus the spatial divergence of the full action-generated algebraic
current on the same P506 profile. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_timeDerivative_eq_neg_spatialCurrentDivergence
    (component : P286CoordinateCarrier) :
    fieldDirectionalDerivative
        (p286GaugeConnectionSpatialBFMomentumDivergence
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual
          (p286TemporalGaugeOneForm component))
        0 canonicalLorentzianTimeDirection =
      -(∑ axis : Fin 3,
        fieldDirectionalDerivative
          (p286GaugeConnectionAlgebraicCurrentCoefficient
            positiveSmoothUnifiedSource preContorsionSpatialProfileActual
            (canonicalP286SpatialGaugeOneForm
              (p286SpatialSingleAxisDirection axis component)))
          0 axis.succ) := by
  rw [
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286SpatialBFDivergence_timeDerivative_eq_actionCorrectionDivergence]
  calc
    (∑ axis : Fin 3,
      fieldDirectionalDerivative
        (coherentProfileP286BFMomentumCorrectionCoefficient
          (p286GaugeExteriorDerivativeDirection axis.succ
            (p286TemporalGaugeOneForm component)))
        0 axis.succ) =
        ∑ axis : Fin 3,
          -fieldDirectionalDerivative
            (p286GaugeConnectionAlgebraicCurrentCoefficient
              positiveSmoothUnifiedSource preContorsionSpatialProfileActual
              (canonicalP286SpatialGaugeOneForm
                (p286SpatialSingleAxisDirection axis component)))
            0 axis.succ := by
      apply Finset.sum_congr rfl
      intro axis _
      exact
        coherentProfileP286BFMomentumCorrectionCoefficient_spatialDerivative_eq_neg_spatialCurrentDerivative
          axis component
    _ = _ := by
      rw [Finset.sum_neg_distrib]

/-! ## Action-sector audit of the algebraic-current leg -/

/-- The time derivative of the complete algebraic current is the sum of the
three genuine action-sector derivatives on the same fresh local actual.
This is a decomposition readout only: it neither declares the sum zero nor
recounts the producer equations as an independent constraint. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_p286AlgebraicCurrent_timeDerivative_eq_sectors
    (component : P286CoordinateCarrier) :
    fieldDirectionalDerivative
        (freshLocalP286TemporalAlgebraicCurrent component)
        0 canonicalLorentzianTimeDirection =
      (fieldDirectionalDerivative
          (p286GaugeBFAlgebraicCoefficient
            positiveP506MatterPreContorsionFullLorentzFreshActual
            (p286TemporalGaugeOneForm component))
          0 canonicalLorentzianTimeDirection +
        fieldDirectionalDerivative
          (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
            positiveP506MatterPreContorsionFullLorentzFreshActual
            (p286TemporalGaugeOneForm component))
          0 canonicalLorentzianTimeDirection) +
      fieldDirectionalDerivative
        (p286MatterCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshActual
          (p286TemporalGaugeOneForm component))
        0 canonicalLorentzianTimeDirection := by
  let actual :=
    positiveP506MatterPreContorsionFullLorentzFreshActual
  let direction := p286TemporalGaugeOneForm component
  have actualSmooth : actual.Smooth :=
    currentCanonicalFullActionLorentzActualFirstJetLift_smooth
      positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent 0
  have actualNondegenerate : actual.Nondegenerate :=
    currentCanonicalFullActionLorentzActualFirstJetLift_nondegenerate
      positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent 0
      preContorsionFullLorentzTriangularCurrent_coframe_origin
  have bfSmooth :
      ContDiff ℝ ∞ (p286GaugeBFAlgebraicCoefficient actual direction) :=
    p286GaugeBFAlgebraicCoefficient_contDiff actual actualSmooth
      actualNondegenerate direction
  have scalarSmooth :
      ContDiff ℝ ∞
        (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource actual
          direction) :=
    p286ScalarCurrentCoefficient_contDiff positiveSmoothUnifiedSource actual
      actualSmooth actualNondegenerate direction
  have matterSmooth :
      ContDiff ℝ ∞
        (p286MatterCurrentCoefficient positiveSmoothUnifiedSource actual
          direction) :=
    p286MatterCurrentCoefficient_contDiff positiveSmoothUnifiedSource actual
      actualSmooth actualNondegenerate direction
  have sectorFunction :
      freshLocalP286TemporalAlgebraicCurrent component =
        fun point =>
          (p286GaugeBFAlgebraicCoefficient actual direction point +
            p286ScalarCurrentCoefficient positiveSmoothUnifiedSource actual
              direction point) +
          p286MatterCurrentCoefficient positiveSmoothUnifiedSource actual
            direction point := by
    funext point
    exact p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors
      positiveSmoothUnifiedSource actual direction point
  rw [sectorFunction,
    fieldDirectionalDerivative_add_real_of_contDiff
      (fun point =>
        p286GaugeBFAlgebraicCoefficient actual direction point +
          p286ScalarCurrentCoefficient positiveSmoothUnifiedSource actual
            direction point)
      (p286MatterCurrentCoefficient positiveSmoothUnifiedSource actual
        direction)
      (bfSmooth.add scalarSmooth) matterSmooth,
    fieldDirectionalDerivative_add_real_of_contDiff
      (p286GaugeBFAlgebraicCoefficient actual direction)
      (p286ScalarCurrentCoefficient positiveSmoothUnifiedSource actual
        direction)
      bfSmooth scalarSmooth]

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286GaussTangency
