import H0mework.Physics.MatterPreparation.ContorsionSpatialProfileCoherentFirstGermSimplicityTangent
import H0mework.Physics.Cauchy.LorentzActionCauchySplit

/-!
# S9-C3h200m: coherent profile BF-momentum regularity at the common contact

C3h200k installed the complete current response on one spacetime carrier,
and C3h200l checked tangent simplicity at its canonical contact.  This module
establishes exactly the regularity needed to evaluate the spatial Lorentz
constraint on that same actual.

The proof does not assert that the complete coherent actual is smooth.  Its
coframe is the generated C3h200i profile pulled back along the zero-slice
projection, while its auxiliary differs from that pullback by
`time * V(space)`.  The action-generated response `V` is continuous and
vanishes at the canonical contact, so the correction has zero Fréchet
derivative there by a direct little-`o` argument.  Consequently the coherent
actual and the generated profile have the same three spatial BF-momentum
derivatives at that contact.

This is a positive same-actual differentiability and transport gate.  It is
not a temporal Gauss equation, an independent Euler--Lagrange closure, a
flow, or a stationarity receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularity

open Filter Asymptotics
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineConnectionSectorSourceBalance
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineEnrichedProofFreeSource
open StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionMomentumRegularity
open StageNinePlebanskiMultiplierVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCurrentResponse
open scoped ContDiff Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## Zero-slice projection and coherent primitive normal forms -/

/-- Linear projection of spacetime onto its canonical time-zero slice. -/
def canonicalZeroSliceProjection : BasePoint →L[ℝ] BasePoint :=
  canonicalSpatialInclusion.comp canonicalSpatialProjection

@[simp] theorem canonicalZeroSliceProjection_apply (point : BasePoint) :
    canonicalZeroSliceProjection point =
      canonicalCauchySlicePoint 0 (canonicalSpatialProjection point) := by
  unfold canonicalZeroSliceProjection
  rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
  simp

@[simp] theorem canonicalZeroSliceProjection_coordinateSpatial
    (axis : Fin 3) :
    canonicalZeroSliceProjection (coordinateDirection axis.succ) =
      coordinateDirection axis.succ := by
  have spatialProjection :
      canonicalSpatialProjection (coordinateDirection axis.succ) =
        canonicalSpatialCoordinateDirection axis := by
    apply PiLp.ext
    intro component
    fin_cases axis <;> fin_cases component <;>
      simp [canonicalSpatialProjection, canonicalSpatialCoordinateDirection,
        localBaseCoordinate_apply, coordinateDirection]
  unfold canonicalZeroSliceProjection
  rw [ContinuousLinearMap.comp_apply, spatialProjection,
    canonicalSpatialInclusion_coordinateDirection]

@[simp] theorem canonicalZeroSliceProjection_coordinateTime :
    canonicalZeroSliceProjection
        (coordinateDirection canonicalLorentzianTimeDirection) = 0 := by
  unfold canonicalZeroSliceProjection
  rw [ContinuousLinearMap.comp_apply]
  have spatialProjection :
      canonicalSpatialProjection
          (coordinateDirection canonicalLorentzianTimeDirection) = 0 := by
    apply PiLp.ext
    intro axis
    fin_cases axis <;>
      simp [canonicalSpatialProjection, localBaseCoordinate_apply,
        coordinateDirection, canonicalLorentzianTimeDirection]
  rw [spatialProjection]
  exact canonicalSpatialInclusion.map_zero

/-- The coherent actual's coframe is the generated profile pulled back to
the zero slice.  The primitive coframe velocity is identically zero. -/
theorem coherentProfileActual_coframe_normalForm (point : BasePoint) :
    positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual.coframe
        point =
      preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point) := by
  rw [canonicalZeroSliceProjection_apply]
  change
    (currentCanonicalFullActionLorentzActualFirstJetLift
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
      (canonicalSpatialProjection point)).coframe
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) = _
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
      (canonicalSpatialProjection point)).coframe
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) = _
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe]
  rfl

/-- The only extra auxiliary term in the coherent actual is the
action-generated response multiplied by the canonical time coordinate. -/
theorem coherentProfileActual_gravityAuxiliary_normalForm
    (point : BasePoint) :
    positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual.gravityAuxiliary
        point =
      preContorsionSpatialProfileActual.gravityAuxiliary
          (canonicalZeroSliceProjection point) +
        canonicalTimeProjection point •
          currentCanonicalFullActionLorentzAuxiliaryVelocity
            positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
            (canonicalSpatialProjection point) := by
  rw [canonicalZeroSliceProjection_apply]
  change
    (currentCanonicalFullActionLorentzActualFirstJetLift
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
      (canonicalSpatialProjection point)).gravityAuxiliary
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) = _
  unfold currentCanonicalFullActionLorentzActualFirstJetLift
  rw [currentCanonicalGravityPreservingActual_gravityAuxiliary]
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
      (canonicalSpatialProjection point)).gravityAuxiliary
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) +
      localBaseCoordinate canonicalLorentzianTimeDirection
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) •
        currentCanonicalFullActionLorentzAuxiliaryVelocity
          positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
          (canonicalSpatialProjection point) = _
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_auxiliary,
    congrFun preContorsionSpatialProfileCurrent_gravityAuxiliaryPrepared
      (canonicalSpatialProjection point)]
  change
    preContorsionSpatialProfileActual.gravityAuxiliary
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) +
        _ = _
  simp [localBaseCoordinate_apply]

/-! ## Continuity of the action-generated auxiliary response -/

theorem preContorsionSpatialProfileActual_spatialBFMomentumDivergence_continuous
    (direction : LorentzBivectorOneForm) :
    Continuous
      (lorentzConnectionSpatialBFMomentumDivergence
        preContorsionSpatialProfileActual direction) := by
  unfold lorentzConnectionSpatialBFMomentumDivergence
    lorentzConnectionSpatialBFMomentumDerivative
    fieldDirectionalDerivative
  apply continuous_finsetSum
  intro derivativeDirection _
  have momentumSmooth :=
    lorentzConnectionBFDifferentialMomentum_contDiff
      preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth
      preContorsionSpatialProfileActual_nondegenerate
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection.succ
        direction)
  exact (momentumSmooth.continuous_fderiv (by simp)).clm_apply
    continuous_const

theorem preContorsionSpatialProfileCurrent_rawActionReadout_eq_profileSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        space direction =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource preContorsionSpatialProfileActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 space) -
        lorentzConnectionSpatialBFMomentumDivergence
          preContorsionSpatialProfileActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 space) := by
  change
    lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource
          (currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
            PreContorsionSpatialProfileCurrent space)
          (canonicalLorentzSpatialBivectorOneForm direction) 0 -
        currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
          positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
          space direction = _
  rw [
    preContorsionSpatialProfileCurrent_freshAlgebraicAction_eq_profileSlice,
    preContorsionSpatialProfileCurrent_spatialBFMomentumDivergence_eq_profileSlice]

theorem preContorsionSpatialProfileCurrent_rawActionReadout_continuous
    (direction : LorentzSpatialBivectorDirection) :
    Continuous fun space =>
      currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        space direction := by
  rw [show (fun space =>
      currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        space direction) =
    fun space =>
      lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource preContorsionSpatialProfileActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 space) -
        lorentzConnectionSpatialBFMomentumDivergence
          preContorsionSpatialProfileActual
          (canonicalLorentzSpatialBivectorOneForm direction)
          (canonicalCauchySlicePoint 0 space) by
    funext space
    exact preContorsionSpatialProfileCurrent_rawActionReadout_eq_profileSlice
      space direction]
  have sliceContinuous : Continuous (canonicalCauchySlicePoint 0) := by
    rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
      funext space
      rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
      simp]
    exact canonicalSpatialInclusion.continuous
  exact
    (lorentzConnectionAlgebraicSpinCurrentCoefficient_continuous
      positiveSmoothUnifiedSource preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth
      preContorsionSpatialProfileActual_nondegenerate
      (canonicalLorentzSpatialBivectorOneForm direction)).comp
        sliceContinuous |>.sub
      ((preContorsionSpatialProfileActual_spatialBFMomentumDivergence_continuous
        (canonicalLorentzSpatialBivectorOneForm direction)).comp
          sliceContinuous)

theorem preContorsionSpatialProfileCurrent_actionCoordinates_continuous :
    Continuous
      (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent) := by
  apply continuous_pi
  intro spatialDirection
  apply continuous_pi
  intro internalPair
  exact preContorsionSpatialProfileCurrent_rawActionReadout_continuous
    (canonicalLorentzSpatialBivectorCoordinateDirection
      spatialDirection internalPair)

theorem preContorsionSpatialProfileCurrent_auxiliaryVelocity_continuous :
    Continuous
      (currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent) := by
  have coordinatesContinuous :=
    preContorsionSpatialProfileCurrent_actionCoordinates_continuous
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  fin_cases spacetimePair <;>
    simp [currentCanonicalFullActionLorentzAuxiliaryVelocity,
      lorentzSpatialAuxiliaryVelocityEmbedding] <;>
    fun_prop

/-! ## BF-momentum normal form and origin differentiability -/

/-- Coefficient of the only time-dependent correction to one BF-momentum
field. -/
def coherentProfileBFMomentumCorrectionCoefficient
    (direction : PhysicalBivector) (point : BasePoint) : ℝ :=
  generatedVolumeDensity
      (toContinuumPointField preContorsionSpatialProfileActual
        (canonicalZeroSliceProjection point)) *
    gravityAuxiliaryHodgePairingPolynomial
      (preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point))
      (currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        (canonicalSpatialProjection point))
      direction

theorem coherentProfileBFMomentumCorrectionCoefficient_continuous
    (direction : PhysicalBivector) :
    Continuous (coherentProfileBFMomentumCorrectionCoefficient direction) := by
  have zeroSliceContinuous := canonicalZeroSliceProjection.continuous
  have coframeContinuous : Continuous fun point =>
      preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point) :=
    (holonomicCoframe_continuous preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth).comp zeroSliceContinuous
  have velocityContinuous : Continuous fun point =>
      currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
        (canonicalSpatialProjection point) :=
    preContorsionSpatialProfileCurrent_auxiliaryVelocity_continuous.comp
      canonicalSpatialProjection.continuous
  have velocityTransformContinuous : Continuous fun point =>
      fun internalPair =>
        coframeTwoFormLinear
          (preContorsionSpatialProfileActual.coframe
            (canonicalZeroSliceProjection point))
          (currentCanonicalFullActionLorentzAuxiliaryVelocity
            positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
            (canonicalSpatialProjection point) internalPair) := by
    apply continuous_pi
    intro internalPair
    exact coframeTwoFormLinear_apply_continuous
      (fun point => preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point)) coframeContinuous
      (fun point =>
        currentCanonicalFullActionLorentzAuxiliaryVelocity
          positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent
          (canonicalSpatialProjection point) internalPair)
      ((continuous_apply internalPair).comp velocityContinuous)
  have directionTransformContinuous : Continuous fun point =>
      fun internalPair =>
        coframeTwoFormLinear
          (preContorsionSpatialProfileActual.coframe
            (canonicalZeroSliceProjection point))
          (direction internalPair) := by
    apply continuous_pi
    intro internalPair
    exact coframeTwoFormLinear_apply_continuous
      (fun point => preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point)) coframeContinuous
      (fun _ => direction internalPair) continuous_const
  have hodgeDirectionTransformContinuous : Continuous fun point =>
      fun internalPair =>
        lorentzianCoframeHodge
          (coframeTwoFormLinear
            (preContorsionSpatialProfileActual.coframe
              (canonicalZeroSliceProjection point))
            (direction internalPair)) := by
    apply continuous_pi
    intro internalPair
    exact lorentzianCoframeHodge_apply_continuous
      (fun point =>
        coframeTwoFormLinear
          (preContorsionSpatialProfileActual.coframe
            (canonicalZeroSliceProjection point))
          (direction internalPair))
      ((continuous_apply internalPair).comp directionTransformContinuous)
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity
        (toContinuumPointField preContorsionSpatialProfileActual
          (canonicalZeroSliceProjection point)) :=
    (holonomicGeneratedVolumeDensity_contDiff
      preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth
      preContorsionSpatialProfileActual_nondegenerate).continuous.comp
        zeroSliceContinuous
  unfold coherentProfileBFMomentumCorrectionCoefficient
    gravityAuxiliaryHodgePairingPolynomial
  apply volumeContinuous.mul
  apply continuous_finsetSum
  intro internalPair _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro spacetimePair _
  exact (continuous_const.mul
      ((continuous_apply spacetimePair).comp
        ((continuous_apply internalPair).comp
          velocityTransformContinuous))).mul
    ((continuous_apply spacetimePair).comp
      ((continuous_apply internalPair).comp
        hodgeDirectionTransformContinuous))

@[simp] theorem coherentProfileBFMomentumCorrectionCoefficient_origin
    (direction : PhysicalBivector) :
    coherentProfileBFMomentumCorrectionCoefficient direction 0 = 0 := by
  unfold coherentProfileBFMomentumCorrectionCoefficient
  rw [canonicalZeroSliceProjection.map_zero,
    canonicalSpatialProjection.map_zero,
    preContorsionSpatialProfileCurrent_lorentzAuxiliaryVelocity_zero]
  simp [gravityAuxiliaryHodgePairingPolynomial]

/-- Exact decomposition of the coherent actual's BF momentum into the
generated profile pullback and one time-weighted response correction. -/
theorem coherentProfileActual_BFMomentum_normalForm
    (direction : PhysicalBivector) (point : BasePoint) :
    lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction point =
      lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction
          (canonicalZeroSliceProjection point) +
        canonicalTimeProjection point *
          coherentProfileBFMomentumCorrectionCoefficient direction point := by
  unfold lorentzConnectionBFDifferentialMomentum
    coherentProfileBFMomentumCorrectionCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [coherentProfileActual_coframe_normalForm,
    coherentProfileActual_gravityAuxiliary_normalForm,
    gravityAuxiliaryHodgePairingPolynomial_add_smul_left
      (preContorsionSpatialProfileActual.coframe
        (canonicalZeroSliceProjection point))
      (preContorsionSpatialProfileActual_nondegenerate
        (canonicalZeroSliceProjection point))]
  ring

private theorem hasFDerivAt_mul_zero_of_first_zero_second_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {first second : E → ℝ} {firstDerivative : E →L[ℝ] ℝ}
    (firstHasDerivative : HasFDerivAt first firstDerivative 0)
    (firstZero : first 0 = 0)
    (secondContinuous : ContinuousAt second 0)
    (secondZero : second 0 = 0) :
    HasFDerivAt (fun point => first point * second point)
      (0 : E →L[ℝ] ℝ) 0 := by
  have firstOrder : first =O[𝓝 0] fun point : E => ‖point‖ := by
    have firstOrderVector : first =O[𝓝 0] fun point : E => point := by
      simpa [firstZero] using firstHasDerivative.isBigO_sub
    exact firstOrderVector.norm_right
  have secondLittle : second =o[𝓝 0] fun _ : E => (1 : ℝ) := by
    rw [isLittleO_one_iff]
    simpa only [secondZero] using secondContinuous.tendsto
  have productLittle :
      (fun point => first point * second point) =o[𝓝 0]
        fun point : E => ‖point‖ * (1 : ℝ) :=
    firstOrder.mul_isLittleO secondLittle
  have productLittleNorm :
      (fun point => first point * second point) =o[𝓝 0]
        fun point : E => ‖point‖ := by
    simpa only [mul_one] using productLittle
  have productLittleVector :
      (fun point => first point * second point) =o[𝓝 0]
        fun point : E => point :=
    productLittleNorm.of_norm_right
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [zero_add, firstZero, secondZero, mul_zero, zero_apply,
    sub_zero] using productLittleVector

private theorem coherentProfileBFMomentumCorrection_hasFDerivAt_zero
    (direction : PhysicalBivector) :
    HasFDerivAt
      (fun point =>
        canonicalTimeProjection point *
          coherentProfileBFMomentumCorrectionCoefficient direction point)
      (0 : BasePoint →L[ℝ] ℝ) 0 := by
  exact hasFDerivAt_mul_zero_of_first_zero_second_continuous
    canonicalTimeProjection.hasFDerivAt canonicalTimeProjection.map_zero
    (coherentProfileBFMomentumCorrectionCoefficient_continuous
      direction).continuousAt
    (coherentProfileBFMomentumCorrectionCoefficient_origin direction)

/-- The coherent BF momentum is genuinely differentiable at the canonical
origin.  Its derivative is the profile derivative restricted to the fixed
zero-slice projection; the response correction contributes zero there. -/
theorem coherentProfileActual_BFMomentum_hasFDerivAt_origin
    (direction : PhysicalBivector) :
    HasFDerivAt
      (lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction)
      ((fderiv ℝ
        (lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction) 0).comp
        canonicalZeroSliceProjection)
      0 := by
  rw [show
    lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction =
      fun point =>
        lorentzConnectionBFDifferentialMomentum
            preContorsionSpatialProfileActual direction
            (canonicalZeroSliceProjection point) +
          canonicalTimeProjection point *
            coherentProfileBFMomentumCorrectionCoefficient direction point by
    funext point
    exact coherentProfileActual_BFMomentum_normalForm direction point]
  have profileDerivative :
      HasFDerivAt
        (lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction)
        (fderiv ℝ
          (lorentzConnectionBFDifferentialMomentum
            preContorsionSpatialProfileActual direction) 0)
        0 :=
    ((lorentzConnectionBFDifferentialMomentum_contDiff
      preContorsionSpatialProfileActual
      preContorsionSpatialProfileActual_smooth
      preContorsionSpatialProfileActual_nondegenerate
      direction).differentiable (by simp)).differentiableAt.hasFDerivAt
  have projectionDerivative :
      HasFDerivAt
        (fun point : BasePoint => canonicalZeroSliceProjection point)
        canonicalZeroSliceProjection 0 :=
    canonicalZeroSliceProjection.hasFDerivAt
  have profileDerivativeAtProjection :
      HasFDerivAt
        (lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction)
        (fderiv ℝ
          (lorentzConnectionBFDifferentialMomentum
            preContorsionSpatialProfileActual direction) 0)
        (canonicalZeroSliceProjection 0) := by
    rw [canonicalZeroSliceProjection.map_zero]
    exact profileDerivative
  have pulledBackDerivative :=
    HasFDerivAt.comp
      (f := fun point : BasePoint => canonicalZeroSliceProjection point)
      0 profileDerivativeAtProjection projectionDerivative
  have combinedDerivative := pulledBackDerivative.add
    (coherentProfileBFMomentumCorrection_hasFDerivAt_zero direction)
  have combinedDerivative' :
      HasFDerivAt
        ((lorentzConnectionBFDifferentialMomentum
            preContorsionSpatialProfileActual direction ∘
          fun point : BasePoint => canonicalZeroSliceProjection point) +
          fun point =>
            canonicalTimeProjection point *
              coherentProfileBFMomentumCorrectionCoefficient direction point)
        ((fderiv ℝ
          (lorentzConnectionBFDifferentialMomentum
            preContorsionSpatialProfileActual direction) 0).comp
          canonicalZeroSliceProjection)
        0 := by
    simpa only [add_zero] using combinedDerivative
  apply combinedDerivative'.congr_of_eventuallyEq
  filter_upwards with point
  simp only [Function.comp_apply, Pi.add_apply,
    canonicalZeroSliceProjection_apply]

theorem coherentProfileActual_BFMomentum_differentiableAt_origin
    (direction : PhysicalBivector) :
    DifferentiableAt ℝ
      (lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction) 0 :=
  (coherentProfileActual_BFMomentum_hasFDerivAt_origin direction
    ).differentiableAt

/-- Each of the three spatial momentum derivatives is transported to the
same coherent actual.  This is the reusable per-axis bridge; downstream
Cauchy split namespaces may sum it without changing its meaning. -/
theorem coherentProfileActual_BFMomentum_spatialDerivative_eq_profile
    (axis : Fin 3) (direction : PhysicalBivector) :
    fieldDirectionalDerivative
        (lorentzConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
          direction)
        0 axis.succ =
      fieldDirectionalDerivative
        (lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual direction)
        0 axis.succ := by
  unfold fieldDirectionalDerivative
  rw [(coherentProfileActual_BFMomentum_hasFDerivAt_origin direction).fderiv]
  rw [ContinuousLinearMap.comp_apply,
    canonicalZeroSliceProjection_coordinateSpatial]

/-- The zero-slice pullback has no temporal BF-momentum derivative.  The
coherent response correction also has zero first derivative at the common
contact, so the temporal term agrees with the generated spatial profile's
forced zero temporal input. -/
theorem coherentProfileActual_BFMomentum_timeDerivative_eq_profile
    (direction : LorentzBivectorOneForm) :
    fieldDirectionalDerivative
        (lorentzConnectionBFDifferentialMomentum
          positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection direction))
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
        (lorentzConnectionBFDifferentialMomentum
          preContorsionSpatialProfileActual
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection direction))
        0 canonicalLorentzianTimeDirection := by
  have coherentZero :
      fieldDirectionalDerivative
          (lorentzConnectionBFDifferentialMomentum
            positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
            (lorentzConnectionExteriorDerivativeDirection
              canonicalLorentzianTimeDirection direction))
          0 canonicalLorentzianTimeDirection = 0 := by
    unfold fieldDirectionalDerivative
    rw [(coherentProfileActual_BFMomentum_hasFDerivAt_origin
      (lorentzConnectionExteriorDerivativeDirection
        canonicalLorentzianTimeDirection direction)).fderiv]
    rw [ContinuousLinearMap.comp_apply,
      canonicalZeroSliceProjection_coordinateTime]
    exact map_zero _
  rw [coherentZero]
  change 0 =
    fieldDirectionalDerivative
      (lorentzConnectionBFDifferentialMomentum
        (spatialSkewCoframeActualOn PreContorsionP286Actual
          generatedSpatialSkewCoframeJet)
        (lorentzConnectionExteriorDerivativeDirection
          canonicalLorentzianTimeDirection direction))
      0 canonicalLorentzianTimeDirection
  rw [spatialSkewCoframeActualOn_BFMomentum_timeDerivative_zero]

/-- Complete four-direction BF divergence is transported to the coherent
actual.  This is stronger than the spatial Cauchy readout: the temporal row
is included as the profile producer's forced output, not supplied as an
extra target. -/
theorem coherentProfileActual_fullBFMomentumDivergence_eq_profile
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction 0 =
      lorentzConnectionBFDifferentialMomentumDivergence
        preContorsionSpatialProfileActual direction 0 := by
  unfold lorentzConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  fin_cases derivativeDirection
  · exact coherentProfileActual_BFMomentum_timeDerivative_eq_profile direction
  · exact coherentProfileActual_BFMomentum_spatialDerivative_eq_profile
      (0 : Fin 3)
      (lorentzConnectionExteriorDerivativeDirection 1 direction)
  · exact coherentProfileActual_BFMomentum_spatialDerivative_eq_profile
      (1 : Fin 3)
      (lorentzConnectionExteriorDerivativeDirection 2 direction)
  · simpa [Fin.succ] using
      coherentProfileActual_BFMomentum_spatialDerivative_eq_profile
        (2 : Fin 3)
        (lorentzConnectionExteriorDerivativeDirection 3 direction)

/-- Summed spatial BF-momentum divergence on the common coherent actual is
exactly the generated C3h200i profile divergence at the canonical contact. -/
theorem coherentProfileActual_spatialBFMomentumDivergence_eq_profile
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionSpatialBFMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction 0 =
      lorentzConnectionSpatialBFMomentumDivergence
        preContorsionSpatialProfileActual direction 0 := by
  rw [lorentzConnectionSpatialBFMomentumDivergence_eq_sum,
    lorentzConnectionSpatialBFMomentumDivergence_eq_sum]
  apply Finset.sum_congr rfl
  intro axis _
  exact coherentProfileActual_BFMomentum_spatialDerivative_eq_profile axis
    (lorentzConnectionExteriorDerivativeDirection axis.succ direction)

/-- The same per-axis result also supplies the explicit three-term Cauchy
split used by temporal Lorentz Gauss.  The qualification is intentional:
the canonical-pair and Cauchy-split modules retain two historical names for
the same three spatial axes. -/
theorem coherentProfileActual_cauchySpatialBFMomentumDivergence_eq_profile
    (direction : LorentzBivectorOneForm) :
    StageNineLorentzActionCauchySplit.lorentzConnectionSpatialBFMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction 0 =
      StageNineLorentzActionCauchySplit.lorentzConnectionSpatialBFMomentumDivergence
        preContorsionSpatialProfileActual direction 0 := by
  unfold
    StageNineLorentzActionCauchySplit.lorentzConnectionSpatialBFMomentumDivergence
  have firstAxis :=
    coherentProfileActual_BFMomentum_spatialDerivative_eq_profile
      (0 : Fin 3)
      (lorentzConnectionExteriorDerivativeDirection 1 direction)
  have secondAxis :=
    coherentProfileActual_BFMomentum_spatialDerivative_eq_profile
      (1 : Fin 3)
      (lorentzConnectionExteriorDerivativeDirection 2 direction)
  have thirdAxis :=
    coherentProfileActual_BFMomentum_spatialDerivative_eq_profile
      (2 : Fin 3)
      (lorentzConnectionExteriorDerivativeDirection 3 direction)
  norm_num at firstAxis secondAxis
  simp [Fin.succ] at thirdAxis
  rw [firstAxis, secondAxis, thirdAxis]

/-! ## Checkpoint law -/

structure PositiveP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularityLaw :
    Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  endpointEleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos = 11
  responseContinuous :
    Continuous
      (currentCanonicalFullActionLorentzAuxiliaryVelocity
        positiveSmoothUnifiedSource PreContorsionSpatialProfileCurrent)
  momentumDifferentiableAtOrigin : ∀ direction,
    DifferentiableAt ℝ
      (lorentzConnectionBFDifferentialMomentum
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction) 0
  spatialMomentumTransport : ∀ direction,
    lorentzConnectionSpatialBFMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction 0 =
      lorentzConnectionSpatialBFMomentumDivergence
        preContorsionSpatialProfileActual direction 0
  fullMomentumTransport : ∀ direction,
    lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterPreContorsionSpatialProfileCoherentFirstGermActual
        direction 0 =
      lorentzConnectionBFDifferentialMomentumDivergence
        preContorsionSpatialProfileActual direction 0

theorem
    positiveP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularity_realizes_C3h200m :
    PositiveP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularityLaw := by
  exact
    { exactP506L0Lineage :=
        positiveSmoothUnifiedSource_generates_exactP506L0Lineage
      endpointEleven := positiveSmoothUnifiedSource_generates_endpoint_eleven
      responseContinuous :=
        preContorsionSpatialProfileCurrent_auxiliaryVelocity_continuous
      momentumDifferentiableAtOrigin :=
        coherentProfileActual_BFMomentum_differentiableAt_origin
      spatialMomentumTransport :=
        coherentProfileActual_spatialBFMomentumDivergence_eq_profile
      fullMomentumTransport :=
        coherentProfileActual_fullBFMomentumDivergence_eq_profile }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCoherentBFMomentumRegularity
