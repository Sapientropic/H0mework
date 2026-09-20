import H0mework.Physics.CurrentAction.LorentzCoherentDiagonalActualCore
import H0mework.Physics.GaugeAction.P286GaugeConnectionAlgebraicCurrentRegularity

/-!
# Canonical-restriction P286 action regularity

This dependency-light module closes the regularity seam needed when a
source/action-generated holonomic actual is restricted to Cauchy data and
then fed back into the existing current-state response:

```text
smooth actual U
→ canonical Cauchy restriction C(U)
→ contact-local action actual G(C(U), x)
→ the P286 spatial action target of G is the zero-slice current of U
→ the uniquely generated BF-Legendre velocity varies smoothly with x.
```

The theorem mouth accepts only regularity and nondegeneracy of the already
generated actual.  It accepts no Gauss equation, residual zero, response
field, branch receipt, target endpoint, or constraint certificate.  The
result is a producer-regularity bridge; it is not itself Gauss propagation.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCanonicalRestrictionP286CoherentRegularity

open Filter Asymptotics
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineMatterVariation
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

open scoped ContDiff Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance canonicalRestrictionP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance canonicalRestrictionP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance canonicalRestrictionP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Canonical-slice first-jet fidelity -/

private theorem fderiv_canonicalCauchySlicePoint_spatial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (derivativeDirection : Fin 3)
    (differentiable : DifferentiableAt ℝ field
      (canonicalCauchySlicePoint time space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint time) space
        (canonicalSpatialCoordinateDirection derivativeDirection) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time space)
        derivativeDirection.succ := by
  have derivative := differentiable.hasFDerivAt.comp space
    (canonicalCauchySlicePoint_hasFDerivAt time space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

/-- The scalar jet reconstructed from the canonical restriction is the
actual scalar first jet at the matching spacetime contact. -/
theorem canonicalCauchyRestriction_scalarLocalJetCoordinate
    (actual : StageNineHolonomicConfiguration)
    (scalarSmooth : ContDiff ℝ ∞ actual.scalar)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    actionGeneratedScalarLocalJetCoordinate
        (canonicalCauchyRestriction 0 actual) space direction =
      fieldDirectionalDerivative actual.scalar
        (canonicalCauchySlicePoint 0 space) direction := by
  fin_cases direction
  · rfl
  · change
      fderiv ℝ (actual.scalar ∘ canonicalCauchySlicePoint 0) space
          (canonicalSpatialCoordinateDirection 0) =
        fieldDirectionalDerivative actual.scalar
          (canonicalCauchySlicePoint 0 space) 1
    exact fderiv_canonicalCauchySlicePoint_spatial actual.scalar 0 space 0
      ((scalarSmooth.differentiable (by simp)).differentiableAt)
  · change
      fderiv ℝ (actual.scalar ∘ canonicalCauchySlicePoint 0) space
          (canonicalSpatialCoordinateDirection 1) =
        fieldDirectionalDerivative actual.scalar
          (canonicalCauchySlicePoint 0 space) 2
    exact fderiv_canonicalCauchySlicePoint_spatial actual.scalar 0 space 1
      ((scalarSmooth.differentiable (by simp)).differentiableAt)
  · change
      fderiv ℝ (actual.scalar ∘ canonicalCauchySlicePoint 0) space
          (canonicalSpatialCoordinateDirection 2) =
        fieldDirectionalDerivative actual.scalar
          (canonicalCauchySlicePoint 0 space) 3
    exact fderiv_canonicalCauchySlicePoint_spatial actual.scalar 0 space 2
      ((scalarSmooth.differentiable (by simp)).differentiableAt)

/-! ## Contact locality across different named points -/

/-- The P286 algebraic current is local in the listed primitive contact
data even when the two contacts have different coordinates. -/
theorem p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contacts
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (coframeEq : first.coframe firstPoint = second.coframe secondPoint)
    (gaugeConnectionEq :
      first.gaugeConnection firstPoint = second.gaugeConnection secondPoint)
    (gaugeAuxiliaryEq :
      first.gaugeAuxiliary firstPoint = second.gaugeAuxiliary secondPoint)
    (scalarEq : first.scalar firstPoint = second.scalar secondPoint)
    (scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative first firstPoint =
        holonomicScalarCovariantDerivative second secondPoint)
    (matterEq : first.matter firstPoint = second.matter secondPoint)
    (conjugateEq :
      first.conjugateMatter firstPoint = second.conjugateMatter secondPoint)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source first direction
        firstPoint =
      p286GaugeConnectionAlgebraicCurrentCoefficient source second direction
        secondPoint := by
  have curvatureVariationEq :
      p286GaugeConnectionAlgebraicCurvatureDirection first direction
          firstPoint =
        p286GaugeConnectionAlgebraicCurvatureDirection second direction
          secondPoint := by
    unfold p286GaugeConnectionAlgebraicCurvatureDirection
      p286GaugeConnectionAlgebraicCurvatureVariation
      holonomicP286GaugeConnectionCoordinate
    rw [gaugeConnectionEq]
  have scalarVariationEq :
      holonomicScalarGaugeConnectionVariation first (fun _ => direction)
          firstPoint =
        holonomicScalarGaugeConnectionVariation second (fun _ => direction)
          secondPoint := by
    unfold holonomicScalarGaugeConnectionVariation
      p286GaugeConnectionMotherVariation
    rw [scalarEq]
  have matterVariationEq :
      holonomicMatterGaugeConnectionVariation first (fun _ => direction)
          firstPoint =
        holonomicMatterGaugeConnectionVariation second (fun _ => direction)
          secondPoint := by
    unfold holonomicMatterGaugeConnectionVariation
      p286GaugeConnectionMotherVariation
    rw [matterEq]
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionFirstVariationDensity generatedVolumeDensity
    p286AuxiliaryCoordinate
    scalarGaugeConnectionKineticFirstVariationDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  rw [curvatureVariationEq, scalarVariationEq, matterVariationEq]
  simp only [toContinuumPointField,
    scalarFrameRelativeCovariantDerivative,
    scalarFrameRelativeCoordinates_zeroChart,
    matterDerivativeFrameRelative_zeroChart,
    matterDualFrameRelative_zeroChart]
  rw [coframeEq, gaugeAuxiliaryEq, scalarCovariantDerivativeEq, conjugateEq]

/-- The contact-local action actual reconstructed from a smooth actual's
canonical Cauchy restriction reads exactly the original actual's P286
algebraic current at the matching zero-slice contact. -/
theorem canonicalCauchyRestriction_baseP286AlgebraicCurrent_eq_slice
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual) space)
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient source actual direction
        (canonicalCauchySlicePoint 0 space) := by
  let current := canonicalCauchyRestriction 0 actual
  let base := currentCanonicalFullActionBaseActual source current space
  let slice := canonicalCauchySlicePoint 0 space
  rcases actualSmooth with
    ⟨_coframeSmooth, _gravityConnectionSmooth, _gravityAuxiliarySmooth,
      _multiplierSmooth, _gaugeConnectionSmooth, _gaugeAuxiliarySmooth,
      scalarSmooth, _matterSmooth, _conjugateMatterSmooth⟩
  have coframeEq : base.coframe 0 = actual.coframe slice := by
    rfl
  have gaugeConnectionEq :
      base.gaugeConnection 0 = actual.gaugeConnection slice := by
    change
      sourceGeneratedP286ActionLocalConnection source current space 0 =
        actual.gaugeConnection slice
    funext formDirection
    rw [sourceGeneratedP286ActionLocalConnection_origin]
    rfl
  have gaugeAuxiliaryEq :
      base.gaugeAuxiliary 0 = actual.gaugeAuxiliary slice := by
    rfl
  have scalarEq : base.scalar 0 = actual.scalar slice := by
    change actionGeneratedScalarLocalField current space 0 =
      actual.scalar slice
    rw [actionGeneratedScalarLocalField_origin]
    rfl
  have scalarDerivativeEq (derivativeDirection : LorentzianIndex) :
      fieldDirectionalDerivative base.scalar 0 derivativeDirection =
        fieldDirectionalDerivative actual.scalar slice
          derivativeDirection := by
    change
      fieldDirectionalDerivative
          (actionGeneratedScalarLocalField current space)
          0 derivativeDirection =
        fieldDirectionalDerivative actual.scalar slice derivativeDirection
    rw [actionGeneratedScalarLocalField_derivative]
    exact canonicalCauchyRestriction_scalarLocalJetCoordinate actual
      scalarSmooth space derivativeDirection
  have scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative base 0 =
        holonomicScalarCovariantDerivative actual slice := by
    funext derivativeDirection
    unfold holonomicScalarCovariantDerivative
    rw [scalarDerivativeEq derivativeDirection, gaugeConnectionEq, scalarEq]
  have matterEq : base.matter 0 = actual.matter slice := by
    change
      (sourceActionGeneratedJointLocalActualLift source current space).matter
          0 =
        actual.matter slice
    rw [sourceActionGeneratedJointLocalActualLift_initialMatter]
    rfl
  have conjugateMatterEq :
      base.conjugateMatter 0 = actual.conjugateMatter slice := by
    change
      (sourceActionGeneratedJointLocalActualLift source current
        space).conjugateMatter 0 =
        actual.conjugateMatter slice
    rw [sourceActionGeneratedJointLocalActualLift_initialConjugateMatter]
    rfl
  exact p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contacts
    source base actual 0 slice coframeEq gaugeConnectionEq gaugeAuxiliaryEq
    scalarEq scalarCovariantDerivativeEq matterEq conjugateMatterEq direction

/-- Coordinate form consumed by the fixed P286 BF-Legendre inverse. -/
theorem canonicalCauchyRestriction_p286SpatialActionTarget_apply_eq_slice
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    currentP286SpatialActionTarget source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual) space)
        direction =
      p286GaugeConnectionAlgebraicCurrentCoefficient source actual
        (canonicalP286SpatialGaugeOneForm direction)
        (canonicalCauchySlicePoint 0 space) := by
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual) space)
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      _
  exact canonicalCauchyRestriction_baseP286AlgebraicCurrent_eq_slice
    source actual actualSmooth space
    (canonicalP286SpatialGaugeOneForm direction)

private theorem canonicalZeroSliceEmbedding_contDiff :
    ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
    funext space
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    simp]
  exact canonicalSpatialInclusion.contDiff

private theorem
    canonicalCauchyRestriction_p286SpatialActionTarget_coefficient_contDiff
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (actualNondegenerate : actual.Nondegenerate)
    (direction : P286SpatialGaugeDirection) :
    ContDiff ℝ ∞ fun space =>
      currentP286SpatialActionTarget source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual) space)
        direction := by
  rw [show (fun space =>
      currentP286SpatialActionTarget source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual) space)
        direction) =
    fun space =>
      p286GaugeConnectionAlgebraicCurrentCoefficient source actual
        (canonicalP286SpatialGaugeOneForm direction)
        (canonicalCauchySlicePoint 0 space) by
    funext space
    exact
      canonicalCauchyRestriction_p286SpatialActionTarget_apply_eq_slice
        source actual actualSmooth space direction]
  exact
    (p286GaugeConnectionAlgebraicCurrentCoefficient_contDiff source actual
      actualSmooth actualNondegenerate
      (canonicalP286SpatialGaugeOneForm direction)).comp
        canonicalZeroSliceEmbedding_contDiff

/-- The branch-free P286 auxiliary velocity generated from a canonical
restriction varies smoothly with the source-owned spatial contact. -/
theorem canonicalCauchyRestriction_p286AuxiliaryVelocity_contDiff
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (actualNondegenerate : actual.Nondegenerate) :
    ContDiff ℝ ∞ fun space =>
      currentP286SpatialAuxiliaryVelocity source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual) space) := by
  let basis := Module.finBasis ℝ P286SpatialGaugeDirection
  let coordinates := fun space =>
    basis.dualBasis.equivFun
      (currentP286SpatialActionTarget source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual) space))
  have coordinatesContDiff : ContDiff ℝ ∞ coordinates := by
    apply contDiff_pi'
    intro index
    rw [show (fun space => coordinates space index) =
      fun space =>
        currentP286SpatialActionTarget source
          (currentCanonicalFullActionBaseActual source
            (canonicalCauchyRestriction 0 actual) space)
          (basis index) by
      funext space
      exact basis.dualBasis_equivFun _ index]
    exact
      canonicalCauchyRestriction_p286SpatialActionTarget_coefficient_contDiff
        source actual actualSmooth actualNondegenerate (basis index)
  let reconstruct :=
    basis.dualBasis.equivFun.symm.trans p286SpatialBFLegendreEquiv.symm
  let reconstructCLM : _ →L[ℝ] P286SpatialGaugeDirection :=
    ⟨reconstruct.toLinearMap,
      reconstruct.toLinearMap.continuous_of_finiteDimensional⟩
  rw [show (fun space =>
      currentP286SpatialAuxiliaryVelocity source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual) space)) =
    fun space => reconstructCLM (coordinates space) by
    funext space
    change
      p286SpatialBFLegendreEquiv.symm
          (currentP286SpatialActionTarget source
            (currentCanonicalFullActionBaseActual source
              (canonicalCauchyRestriction 0 actual) space)) =
        p286SpatialBFLegendreEquiv.symm
          (basis.dualBasis.equivFun.symm
            (basis.dualBasis.equivFun
              (currentP286SpatialActionTarget source
                (currentCanonicalFullActionBaseActual source
                  (canonicalCauchyRestriction 0 actual) space))))
    rw [LinearEquiv.symm_apply_apply]]
  exact reconstructCLM.contDiff.comp coordinatesContDiff

/-! ## Coherent BF-momentum partial regularity -/

/-- Linear projection onto the zero-time slice.  This is defined locally
to keep the regularity bridge independent of historical profile carriers. -/
def canonicalRestrictionZeroSliceProjection : BasePoint →L[ℝ] BasePoint :=
  canonicalSpatialInclusion.comp canonicalSpatialProjection

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

@[simp] theorem canonicalRestrictionZeroSliceProjection_apply
    (point : BasePoint) :
    canonicalRestrictionZeroSliceProjection point =
      canonicalCauchySlicePoint 0 (canonicalSpatialProjection point) := by
  unfold canonicalRestrictionZeroSliceProjection
  rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
  simp

@[simp] theorem canonicalRestrictionZeroSliceProjection_coordinateSpatial
    (axis : Fin 3) :
    canonicalRestrictionZeroSliceProjection
        (coordinateDirection axis.succ) =
      coordinateDirection axis.succ := by
  have spatialProjection :
      canonicalSpatialProjection (coordinateDirection axis.succ) =
        canonicalSpatialCoordinateDirection axis := by
    apply PiLp.ext
    intro component
    fin_cases axis <;> fin_cases component <;>
      simp [canonicalSpatialProjection, canonicalSpatialCoordinateDirection,
        localBaseCoordinate_apply, coordinateDirection]
  unfold canonicalRestrictionZeroSliceProjection
  rw [ContinuousLinearMap.comp_apply, spatialProjection,
    canonicalSpatialInclusion_coordinateDirection]

@[simp] theorem canonicalRestrictionZeroSliceProjection_coordinateTime :
    canonicalRestrictionZeroSliceProjection
        (coordinateDirection canonicalLorentzianTimeDirection) =
      0 := by
  unfold canonicalRestrictionZeroSliceProjection
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

/-- The coherent diagonal keeps the canonical restriction's coframe fixed,
so its spacetime coframe is the original actual pulled back to time zero. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_coframe_normalForm
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).coframe point =
      actual.coframe (canonicalRestrictionZeroSliceProjection point) := by
  rw [canonicalRestrictionZeroSliceProjection_apply]
  change
    (currentCanonicalFullActionLorentzStateResponseUpdate source
      (canonicalCauchyRestriction 0 actual)
      (canonicalTimeProjection point)).coframe
        (canonicalSpatialProjection point) =
      actual.coframe
        (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))
  rfl

/-- The coherent scalar is the canonical zero-slice field plus its
source-owned Cauchy time jet.  No scalar equation is assumed. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_scalar_normalForm
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).scalar point =
      actual.scalar (canonicalRestrictionZeroSliceProjection point) +
        canonicalTimeProjection point •
          fieldDirectionalDerivative actual.scalar
            (canonicalRestrictionZeroSliceProjection point)
            canonicalLorentzianTimeDirection := by
  change
    actionGeneratedScalarLocalField (canonicalCauchyRestriction 0 actual)
        (canonicalSpatialProjection point)
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) =
      _
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    canonicalCauchyRestriction,
    canonicalRestrictionZeroSliceProjection_apply,
    canonicalCauchySlicePoint, canonicalTimeProjection,
    localBaseCoordinate_apply, canonicalLorentzianTimeDirection,
    Fin.sum_univ_four]

private theorem scalarFieldDirectionalDerivative_contDiff
    (field : BasePoint → ScalarCoordinateCarrier)
    (smooth : ContDiff ℝ ∞ field)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      fieldDirectionalDerivative field point direction := by
  unfold fieldDirectionalDerivative
  simpa [Function.comp_def] using
    (smooth.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_prodMk_left (coordinateDirection direction))

/-- The scalar normal form is genuinely Fréchet differentiable at the
common contact with the full owning-actual first jet. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_scalar_hasFDerivAt_origin
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth) :
    HasFDerivAt
      (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).scalar
      (((fderiv ℝ actual.scalar 0).comp
          canonicalRestrictionZeroSliceProjection) +
        canonicalTimeProjection.smulRight
          (fieldDirectionalDerivative actual.scalar 0
            canonicalLorentzianTimeDirection))
      0 := by
  rcases actualSmooth with
    ⟨_coframeSmooth, _gravityConnectionSmooth, _gravityAuxiliarySmooth,
      _multiplierSmooth, _gaugeConnectionSmooth, _gaugeAuxiliarySmooth,
      scalarSmooth, _matterSmooth, _conjugateMatterSmooth⟩
  let velocity : BasePoint → ScalarCoordinateCarrier := fun point =>
    fieldDirectionalDerivative actual.scalar
      (canonicalRestrictionZeroSliceProjection point)
      canonicalLorentzianTimeDirection
  have scalarDerivative :
      HasFDerivAt actual.scalar (fderiv ℝ actual.scalar 0) 0 :=
    (scalarSmooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have baseDerivative :
      HasFDerivAt
        (fun point => actual.scalar
          (canonicalRestrictionZeroSliceProjection point))
        ((fderiv ℝ actual.scalar 0).comp
          canonicalRestrictionZeroSliceProjection)
        0 := by
    have derivativeAtProjection :
        HasFDerivAt actual.scalar (fderiv ℝ actual.scalar 0)
          (canonicalRestrictionZeroSliceProjection 0) := by
      rw [canonicalRestrictionZeroSliceProjection.map_zero]
      exact scalarDerivative
    exact derivativeAtProjection.comp 0
      canonicalRestrictionZeroSliceProjection.hasFDerivAt
  have velocitySmooth : ContDiff ℝ ∞ velocity :=
    (scalarFieldDirectionalDerivative_contDiff actual.scalar scalarSmooth
      canonicalLorentzianTimeDirection).comp
        canonicalRestrictionZeroSliceProjection.contDiff
  have velocityDerivative :
      HasFDerivAt velocity (fderiv ℝ velocity 0) 0 :=
    (velocitySmooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have linearDerivative :=
    canonicalTimeProjection.hasFDerivAt.smul velocityDerivative
  have totalDerivative := baseDerivative.add linearDerivative
  rw [show
      (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).scalar =
        (fun point =>
          actual.scalar (canonicalRestrictionZeroSliceProjection point)) +
          (fun point => canonicalTimeProjection point) • velocity by
    funext point
    exact
      canonicalCauchyRestriction_coherentDiagonalActual_scalar_normalForm
        source actual point]
  simpa [velocity, canonicalCauchySlicePoint_zero_zero] using totalDerivative

/-- All four scalar first-jet coordinates of the coherent carrier agree
with the owning actual at the common contact. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_scalarDerivative_eq_actual
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (currentCanonicalFullActionLorentzCoherentDiagonalActual source
          (canonicalCauchyRestriction 0 actual)).scalar
        0 direction =
      fieldDirectionalDerivative actual.scalar 0 direction := by
  unfold fieldDirectionalDerivative
  rw [
    (canonicalCauchyRestriction_coherentDiagonalActual_scalar_hasFDerivAt_origin
      source actual actualSmooth).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply]
  refine Fin.cases ?_ (fun axis => ?_) direction
  · have zeroSliceTime :
        canonicalRestrictionZeroSliceProjection
            (coordinateDirection (0 : LorentzianIndex)) =
          0 := by
      simpa [canonicalLorentzianTimeDirection] using
        canonicalRestrictionZeroSliceProjection_coordinateTime
    have timeProjectionTime :
        canonicalTimeProjection
            (coordinateDirection (0 : LorentzianIndex)) =
          1 := by
      simp [canonicalTimeProjection, localBaseCoordinate_apply,
        coordinateDirection, canonicalLorentzianTimeDirection]
    rw [zeroSliceTime, timeProjectionTime]
    simp [fieldDirectionalDerivative, canonicalLorentzianTimeDirection]
  · have timeProjectionSpatial :
        canonicalTimeProjection (coordinateDirection axis.succ) = 0 := by
      fin_cases axis <;>
        simp [canonicalTimeProjection, localBaseCoordinate_apply,
          coordinateDirection, canonicalLorentzianTimeDirection]
    rw [canonicalRestrictionZeroSliceProjection_coordinateSpatial,
      timeProjectionSpatial]
    simp

/-- The coherent diagonal and its owning actual have the same P286
algebraic current at the common contact.  The scalar first jet is supplied
by the theorem immediately above, not inferred from point-value fidelity. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_p286AlgebraicCurrent_origin_eq_actual
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source
        (currentCanonicalFullActionLorentzCoherentDiagonalActual source
          (canonicalCauchyRestriction 0 actual))
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient source actual
        direction 0 := by
  let coherent :=
    currentCanonicalFullActionLorentzCoherentDiagonalActual source
      (canonicalCauchyRestriction 0 actual)
  have coframeEq : coherent.coframe 0 = actual.coframe 0 := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).coframe 0 =
      actual.coframe 0
    rw [
      canonicalCauchyRestriction_coherentDiagonalActual_coframe_normalForm,
      canonicalRestrictionZeroSliceProjection.map_zero]
  have gaugeConnectionEq :
      coherent.gaugeConnection 0 = actual.gaugeConnection 0 := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).gaugeConnection 0 =
      actual.gaugeConnection 0
    rw [← canonicalCauchySlicePoint_zero_zero,
      coherentDiagonalActual_gaugeConnection_slice,
      currentCanonicalFullActionLorentzStateResponseUpdate_zero,
      currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState]
    rfl
  have gaugeAuxiliaryEq :
      coherent.gaugeAuxiliary 0 = actual.gaugeAuxiliary 0 := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).gaugeAuxiliary 0 =
      actual.gaugeAuxiliary 0
    rw [← canonicalCauchySlicePoint_zero_zero,
      coherentDiagonalActual_gaugeAuxiliary_slice,
      currentCanonicalFullActionLorentzStateResponseUpdate_zero,
      currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState]
    rfl
  have scalarEq : coherent.scalar 0 = actual.scalar 0 := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).scalar 0 =
      actual.scalar 0
    rw [
      canonicalCauchyRestriction_coherentDiagonalActual_scalar_normalForm,
      canonicalRestrictionZeroSliceProjection.map_zero]
    simp
  have scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative coherent 0 =
        holonomicScalarCovariantDerivative actual 0 := by
    funext derivativeDirection
    unfold holonomicScalarCovariantDerivative
    rw [show
        fieldDirectionalDerivative coherent.scalar 0 derivativeDirection =
          fieldDirectionalDerivative actual.scalar 0 derivativeDirection by
      change
        fieldDirectionalDerivative
            (currentCanonicalFullActionLorentzCoherentDiagonalActual source
              (canonicalCauchyRestriction 0 actual)).scalar
            0 derivativeDirection =
          _
      exact
        canonicalCauchyRestriction_coherentDiagonalActual_scalarDerivative_eq_actual
          source actual actualSmooth derivativeDirection,
      gaugeConnectionEq, scalarEq]
  have matterEq : coherent.matter 0 = actual.matter 0 := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).matter 0 =
      actual.matter 0
    rw [← canonicalCauchySlicePoint_zero_zero,
      coherentDiagonalActual_matter_slice,
      currentCanonicalFullActionLorentzStateResponseUpdate_zero,
      currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState]
    rfl
  have conjugateMatterEq :
      coherent.conjugateMatter 0 = actual.conjugateMatter 0 := by
    change
      (currentCanonicalFullActionLorentzCoherentDiagonalActual source
        (canonicalCauchyRestriction 0 actual)).conjugateMatter 0 =
      actual.conjugateMatter 0
    rw [← canonicalCauchySlicePoint_zero_zero,
      coherentDiagonalActual_conjugateMatter_slice,
      currentCanonicalFullActionLorentzStateResponseUpdate_zero,
      currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState]
    rfl
  exact p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contacts
    source coherent actual 0 0 coframeEq gaugeConnectionEq gaugeAuxiliaryEq
    scalarEq scalarCovariantDerivativeEq matterEq conjugateMatterEq direction

/-- Exact P286 auxiliary normal form on the coherent diagonal.  The origin
is the supplied actual's zero slice; the slope is regenerated from the
current contact by the fixed BF-Legendre inverse. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_p286Auxiliary_normalForm
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (currentCanonicalFullActionLorentzCoherentDiagonalActual source
          (canonicalCauchyRestriction 0 actual))
        point =
      holonomicP286GaugeAuxiliaryCoordinate actual
          (canonicalRestrictionZeroSliceProjection point) +
        canonicalTimeProjection point •
          p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity source
              (currentCanonicalFullActionBaseActual source
                (canonicalCauchyRestriction 0 actual)
                (canonicalSpatialProjection point))) := by
  funext pair
  change
    p286CoordinateEquiv
        ((currentCanonicalFullActionLorentzStateResponseUpdate source
          (canonicalCauchyRestriction 0 actual)
          (canonicalTimeProjection point)).gaugeAuxiliary
          (canonicalSpatialProjection point) pair) = _
  rw [
    currentCanonicalFullActionLorentzStateResponseUpdate_p286Auxiliary_normalForm]
  have zeroStepNormalForm :=
    currentCanonicalFullActionLorentzStateResponseUpdate_p286Auxiliary_normalForm
      source (canonicalCauchyRestriction 0 actual)
      (canonicalSpatialProjection point) 0 pair
  have zeroStepAuxiliary :
      (currentCanonicalFullActionLorentzStateResponseUpdate source
        (canonicalCauchyRestriction 0 actual) 0).gaugeAuxiliary
          (canonicalSpatialProjection point) pair =
        (canonicalCauchyRestriction 0 actual).gaugeAuxiliary
          (canonicalSpatialProjection point) pair := by
    rw [currentCanonicalFullActionLorentzStateResponseUpdate_zero,
      currentCanonicalFullActionLorentzPreparedOrigin_eq_actionInitialState]
    rfl
  rw [zeroStepAuxiliary] at zeroStepNormalForm
  simp only [zero_smul, add_zero] at zeroStepNormalForm
  rw [zeroStepNormalForm.symm,
    canonicalRestrictionZeroSliceProjection_apply]
  rfl

/-- Coefficient of the coherent diagonal's P286 BF-momentum correction.
It contains only the fixed action velocity regenerated at the matching
source-owned contact. -/
def canonicalRestrictionCoherentP286BFMomentumCorrection
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (direction : P286GaugeTwoForm)
    (point : BasePoint) : ℝ :=
  generatedVolumeDensity
      (toContinuumPointField actual
        (canonicalRestrictionZeroSliceProjection point)) *
    p286GaugeAuxiliaryHodgePairingPolynomial
      (actual.coframe (canonicalRestrictionZeroSliceProjection point))
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentCanonicalFullActionBaseActual source
            (canonicalCauchyRestriction 0 actual)
            (canonicalSpatialProjection point))))
      direction

/-- The action-generated BF correction coefficient is smooth without a
whole-coherent-actual smoothness certificate. -/
theorem canonicalRestrictionCoherentP286BFMomentumCorrection_contDiff
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (actualNondegenerate : actual.Nondegenerate)
    (direction : P286GaugeTwoForm) :
    ContDiff ℝ ∞
      (canonicalRestrictionCoherentP286BFMomentumCorrection source actual
        direction) := by
  let velocityField : BasePoint → P286GaugeTwoForm := fun point =>
    p286SpatialAuxiliaryVelocityEmbedding
      (currentP286SpatialAuxiliaryVelocity source
        (currentCanonicalFullActionBaseActual source
          (canonicalCauchyRestriction 0 actual)
          (canonicalSpatialProjection point)))
  have velocityEmbeddingSmooth : ContDiff ℝ ∞ fun space =>
      p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentCanonicalFullActionBaseActual source
            (canonicalCauchyRestriction 0 actual) space)) := by
    apply contDiff_pi'
    intro pair
    fin_cases pair
    · exact contDiff_const
    · exact contDiff_const
    · exact contDiff_const
    · simpa [p286SpatialAuxiliaryVelocityEmbedding] using
        (contDiff_pi.mp
          (canonicalCauchyRestriction_p286AuxiliaryVelocity_contDiff source
            actual actualSmooth actualNondegenerate) 0)
    · simpa [p286SpatialAuxiliaryVelocityEmbedding] using
        (contDiff_pi.mp
          (canonicalCauchyRestriction_p286AuxiliaryVelocity_contDiff source
            actual actualSmooth actualNondegenerate) 1)
    · simpa [p286SpatialAuxiliaryVelocityEmbedding] using
        (contDiff_pi.mp
          (canonicalCauchyRestriction_p286AuxiliaryVelocity_contDiff source
            actual actualSmooth actualNondegenerate) 2)
  have velocitySmooth : ContDiff ℝ ∞ velocityField :=
    velocityEmbeddingSmooth.comp canonicalSpatialProjection.contDiff
  have pairingSmooth : ContDiff ℝ ∞ fun point =>
      p286GaugeAuxiliaryHodgePairingPolynomial
        (actual.coframe point) (velocityField point) direction :=
    p286GaugeAuxiliaryHodgePairingPolynomial_variable_contDiff
      actual actualSmooth velocityField (fun _ => direction)
      velocitySmooth contDiff_const
  have volumeSmooth : ContDiff ℝ ∞ fun point =>
      generatedVolumeDensity (toContinuumPointField actual point) :=
    holonomicGeneratedVolumeDensity_contDiff
      actual actualSmooth actualNondegenerate
  have pulledSmooth :=
    (volumeSmooth.mul pairingSmooth).comp
      canonicalRestrictionZeroSliceProjection.contDiff
  rw [show
      canonicalRestrictionCoherentP286BFMomentumCorrection source actual
          direction =
        (fun point =>
          generatedVolumeDensity (toContinuumPointField actual point) *
            p286GaugeAuxiliaryHodgePairingPolynomial
              (actual.coframe point) (velocityField point) direction) ∘
          canonicalRestrictionZeroSliceProjection by
    funext point
    simp only [Function.comp_apply]
    unfold canonicalRestrictionCoherentP286BFMomentumCorrection
    dsimp [velocityField]
    rw [canonicalRestrictionZeroSliceProjection_apply,
      canonicalSpatialProjection_slice]]
  exact pulledSmooth

private theorem p286HodgePairing_smul_left
    (coframe : LorentzianCoframe)
    (parameter : ℝ)
    (first test : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial coframe
        (parameter • first) test =
      parameter *
        p286GaugeAuxiliaryHodgePairingPolynomial coframe first test := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [liftGaugeTwoFormOperator_smul_p286]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

private theorem p286HodgePairing_add_left
    (coframe : LorentzianCoframe)
    (first second test : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial coframe
        (first + second) test =
      p286GaugeAuxiliaryHodgePairingPolynomial coframe first test +
        p286GaugeAuxiliaryHodgePairingPolynomial coframe second test := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [liftGaugeTwoFormOperator_add_p286]
  simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_left]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/-- Exact P286 BF-momentum decomposition on the canonical-restriction
coherent carrier.  The correction is not assumed to vanish. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_normalForm
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (direction : P286GaugeTwoForm)
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum
        (currentCanonicalFullActionLorentzCoherentDiagonalActual source
          (canonicalCauchyRestriction 0 actual))
        direction point =
      p286GaugeConnectionBFDifferentialMomentum actual direction
          (canonicalRestrictionZeroSliceProjection point) +
        canonicalTimeProjection point *
          canonicalRestrictionCoherentP286BFMomentumCorrection source actual
            direction point := by
  unfold p286GaugeConnectionBFDifferentialMomentum
    canonicalRestrictionCoherentP286BFMomentumCorrection
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    canonicalCauchyRestriction_coherentDiagonalActual_coframe_normalForm,
    canonicalCauchyRestriction_coherentDiagonalActual_p286Auxiliary_normalForm,
    p286HodgePairing_add_left, p286HodgePairing_smul_left]
  ring

/-- Partial regularity of the coherent carrier sufficient for genuine
Fréchet derivatives of its P286 BF momentum. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_contDiff
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (actualNondegenerate : actual.Nondegenerate)
    (direction : P286GaugeTwoForm) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeConnectionBFDifferentialMomentum
        (currentCanonicalFullActionLorentzCoherentDiagonalActual source
          (canonicalCauchyRestriction 0 actual))
        direction point := by
  rw [show (fun point =>
      p286GaugeConnectionBFDifferentialMomentum
        (currentCanonicalFullActionLorentzCoherentDiagonalActual source
          (canonicalCauchyRestriction 0 actual))
        direction point) =
      fun point =>
        p286GaugeConnectionBFDifferentialMomentum actual direction
            (canonicalRestrictionZeroSliceProjection point) +
          canonicalTimeProjection point *
            canonicalRestrictionCoherentP286BFMomentumCorrection source actual
              direction point by
    funext point
    exact
      canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_normalForm
        source actual direction point]
  exact
    ((p286GaugeConnectionBFDifferentialMomentum_contDiff
      actual actualSmooth actualNondegenerate direction).comp
        canonicalRestrictionZeroSliceProjection.contDiff).add
      (canonicalTimeProjection.contDiff.mul
        (canonicalRestrictionCoherentP286BFMomentumCorrection_contDiff
          source actual actualSmooth actualNondegenerate direction))

private theorem hasFDerivAt_mul_zero_of_first_zero_second_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {first second : E → ℝ}
    {firstDerivative : E →L[ℝ] ℝ}
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

private theorem hasFDerivAt_mul_of_first_zero_second_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {first second : E → ℝ}
    {firstDerivative : E →L[ℝ] ℝ}
    (firstHasDerivative : HasFDerivAt first firstDerivative 0)
    (firstZero : first 0 = 0)
    (secondContinuous : ContinuousAt second 0) :
    HasFDerivAt (fun point => first point * second point)
      ((second 0) • firstDerivative) 0 := by
  let centered : E → ℝ := fun point => second point - second 0
  have centeredContinuous : ContinuousAt centered 0 :=
    secondContinuous.sub continuousAt_const
  have centeredZero : centered 0 = 0 := by
    simp [centered]
  have centeredDerivative :=
    hasFDerivAt_mul_zero_of_first_zero_second_continuous
      firstHasDerivative firstZero centeredContinuous centeredZero
  have constantDerivative := firstHasDerivative.mul_const (second 0)
  have combinedDerivative := constantDerivative.add centeredDerivative
  rw [show (fun point => first point * second point) =
      (fun point => first point * second 0) +
        (fun point => first point * centered point) by
    funext point
    change first point * second point =
      first point * second 0 + first point * (second point - second 0)
    ring]
  simpa only [add_zero] using combinedDerivative

private theorem
    canonicalRestrictionCoherentP286BFMomentumCorrection_hasFDerivAt_origin
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (actualNondegenerate : actual.Nondegenerate)
    (direction : P286GaugeTwoForm) :
    HasFDerivAt
      (fun point =>
        canonicalTimeProjection point *
          canonicalRestrictionCoherentP286BFMomentumCorrection source actual
            direction point)
      ((canonicalRestrictionCoherentP286BFMomentumCorrection source actual
        direction 0) • canonicalTimeProjection)
      0 := by
  exact hasFDerivAt_mul_of_first_zero_second_continuous
    canonicalTimeProjection.hasFDerivAt canonicalTimeProjection.map_zero
    ((canonicalRestrictionCoherentP286BFMomentumCorrection_contDiff
      source actual actualSmooth actualNondegenerate direction).continuous
        ).continuousAt

/-- The coherent momentum derivative at the common contact retains the full
time-response covector instead of silently discarding it. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_hasFDerivAt_origin
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (actualNondegenerate : actual.Nondegenerate)
    (direction : P286GaugeTwoForm) :
    HasFDerivAt
      (p286GaugeConnectionBFDifferentialMomentum
        (currentCanonicalFullActionLorentzCoherentDiagonalActual source
          (canonicalCauchyRestriction 0 actual))
        direction)
      (((fderiv ℝ
          (p286GaugeConnectionBFDifferentialMomentum actual direction) 0).comp
          canonicalRestrictionZeroSliceProjection) +
        (canonicalRestrictionCoherentP286BFMomentumCorrection source actual
          direction 0) • canonicalTimeProjection)
      0 := by
  rw [show
      p286GaugeConnectionBFDifferentialMomentum
          (currentCanonicalFullActionLorentzCoherentDiagonalActual source
            (canonicalCauchyRestriction 0 actual))
          direction =
        fun point =>
          p286GaugeConnectionBFDifferentialMomentum actual direction
              (canonicalRestrictionZeroSliceProjection point) +
            canonicalTimeProjection point *
              canonicalRestrictionCoherentP286BFMomentumCorrection source
                actual direction point by
    funext point
    exact
      canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_normalForm
        source actual direction point]
  have actualDerivative :
      HasFDerivAt
        (p286GaugeConnectionBFDifferentialMomentum actual direction)
        (fderiv ℝ
          (p286GaugeConnectionBFDifferentialMomentum actual direction) 0)
        0 :=
    ((p286GaugeConnectionBFDifferentialMomentum_contDiff actual actualSmooth
      actualNondegenerate direction).differentiable (by simp)
      ).differentiableAt.hasFDerivAt
  have actualDerivativeAtProjection :
      HasFDerivAt
        (p286GaugeConnectionBFDifferentialMomentum actual direction)
        (fderiv ℝ
          (p286GaugeConnectionBFDifferentialMomentum actual direction) 0)
        (canonicalRestrictionZeroSliceProjection 0) := by
    rw [canonicalRestrictionZeroSliceProjection.map_zero]
    exact actualDerivative
  have pulledBackDerivative :=
    HasFDerivAt.comp
      (f := fun point : BasePoint =>
        canonicalRestrictionZeroSliceProjection point)
      0 actualDerivativeAtProjection
      canonicalRestrictionZeroSliceProjection.hasFDerivAt
  have combinedDerivative := pulledBackDerivative.add
    (canonicalRestrictionCoherentP286BFMomentumCorrection_hasFDerivAt_origin
      source actual actualSmooth actualNondegenerate direction)
  exact combinedDerivative.congr_of_eventuallyEq (by
    filter_upwards with point
    rfl)

/-- Every spatial BF-momentum derivative of the coherent response equals
the owning actual's derivative.  Only the spatial contraction of the
time-response term vanishes. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_spatialDerivative_eq_actual
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (actualNondegenerate : actual.Nondegenerate)
    (axis : Fin 3)
    (direction : P286GaugeTwoForm) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          (currentCanonicalFullActionLorentzCoherentDiagonalActual source
            (canonicalCauchyRestriction 0 actual))
          direction)
        0 axis.succ =
      fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum actual direction)
        0 axis.succ := by
  unfold fieldDirectionalDerivative
  rw [
    (canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_hasFDerivAt_origin
      source actual actualSmooth actualNondegenerate direction).fderiv]
  rw [add_apply, ContinuousLinearMap.comp_apply,
    canonicalRestrictionZeroSliceProjection_coordinateSpatial]
  have timeZero :
      canonicalTimeProjection (coordinateDirection axis.succ) = 0 := by
    fin_cases axis <;>
      simp [canonicalTimeProjection, localBaseCoordinate_apply,
        coordinateDirection, canonicalLorentzianTimeDirection]
  rw [smul_apply, timeZero]
  simp

/-- The three-term P286 BF divergence on the coherent carrier is exactly the
owning actual's divergence at the common contact. -/
theorem
    canonicalCauchyRestriction_coherentDiagonalActual_p286SpatialBFDivergence_eq_actual
    (source : SmoothUnifiedSource)
    (actual : StageNineHolonomicConfiguration)
    (actualSmooth : actual.Smooth)
    (actualNondegenerate : actual.Nondegenerate)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        (currentCanonicalFullActionLorentzCoherentDiagonalActual source
          (canonicalCauchyRestriction 0 actual))
        direction 0 =
      p286GaugeConnectionSpatialBFMomentumDivergence actual direction 0 := by
  have axisZero :
      fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum
            (currentCanonicalFullActionLorentzCoherentDiagonalActual source
              (canonicalCauchyRestriction 0 actual))
            (p286GaugeExteriorDerivativeDirection 1 direction))
          0 1 =
        fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum actual
            (p286GaugeExteriorDerivativeDirection 1 direction))
          0 1 := by
    simpa using
      canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_spatialDerivative_eq_actual
        source actual actualSmooth actualNondegenerate (0 : Fin 3)
        (p286GaugeExteriorDerivativeDirection 1 direction)
  have axisOne :
      fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum
            (currentCanonicalFullActionLorentzCoherentDiagonalActual source
              (canonicalCauchyRestriction 0 actual))
            (p286GaugeExteriorDerivativeDirection 2 direction))
          0 2 =
        fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum actual
            (p286GaugeExteriorDerivativeDirection 2 direction))
          0 2 := by
    simpa using
      canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_spatialDerivative_eq_actual
        source actual actualSmooth actualNondegenerate (1 : Fin 3)
        (p286GaugeExteriorDerivativeDirection 2 direction)
  have axisTwo :
      fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum
            (currentCanonicalFullActionLorentzCoherentDiagonalActual source
              (canonicalCauchyRestriction 0 actual))
            (p286GaugeExteriorDerivativeDirection 3 direction))
          0 3 =
        fieldDirectionalDerivative
          (p286GaugeConnectionBFDifferentialMomentum actual
            (p286GaugeExteriorDerivativeDirection 3 direction))
          0 3 := by
    simpa [Fin.succ] using
      canonicalCauchyRestriction_coherentDiagonalActual_p286BFMomentum_spatialDerivative_eq_actual
        source actual actualSmooth actualNondegenerate (2 : Fin 3)
        (p286GaugeExteriorDerivativeDirection 3 direction)
  unfold p286GaugeConnectionSpatialBFMomentumDivergence
  rw [axisZero, axisOne, axisTwo]

end

end
  SaturationMonoid.PhysicsCore.StageNineCanonicalRestrictionP286CoherentRegularity
