import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermSupport
import H0mework.Physics.MatterPreparation.ContorsionCoherentDiracPrincipalGeometry
import H0mework.Physics.MatterPreparation.ContorsionCoherentP286BFMomentumBridge
import H0mework.Physics.MatterPreparation.ContorsionFreshMatterAdjointResponse

/-!
# S9-C3h201e: final coherent matter/adjoint regularity

C3h201d transported the geometric Dirac principal to the C3h200r whole-domain
actual.  The remaining first-germ bridge cannot be inferred from four path
derivatives alone: `fieldDirectionalDerivative` is a Fréchet derivative and
is totalized to zero when differentiability fails.

This module therefore starts from the actual diagonal constructor and proves
the missing component-level regularity:

```text
corrected final current Ufinal
→ action-generated adjoint response Vadj(Ufinal, x)
→ exact coherent dual-field normal form
→ smooth zero-slice provenance for Ufinal
→ genuine component-level Fréchet regularity.
```

The zero-slice regularity carrier is proof-only.  It is not a source datum,
solution candidate, equation receipt, branch choice, or physical endpoint.
No residual is inverted and no target derivative is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterAdjointRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286BFMomentumBridge
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzSameActualConstraints
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

private abbrev preContorsionFullLorentzRegularityState :
    StageNineCauchyState :=
  canonicalCauchyRestriction 0
    preContorsionFullLorentzZeroSliceRegularityActual

/-! ## Exact smooth zero-slice provenance -/

theorem
    preContorsionFullLorentzTriangularCurrent_gravityConnection_eq_regularityState :
    PreContorsionFullLorentzTriangularCurrent.gravityConnection =
      preContorsionFullLorentzRegularityState.gravityConnection := by
  rfl

theorem
    preContorsionFullLorentzTriangularCurrent_gaugeConnection_eq_regularityState :
    PreContorsionFullLorentzTriangularCurrent.gaugeConnection =
      preContorsionFullLorentzRegularityState.gaugeConnection := by
  rw [preContorsionFullLorentzTriangularCurrent_gaugeConnection_eq_profile]
  rfl

theorem
    preContorsionFullLorentzTriangularCurrent_matter_eq_regularityState :
    PreContorsionFullLorentzTriangularCurrent.matter =
      preContorsionFullLorentzRegularityState.matter := by
  rw [preContorsionFullLorentzTriangularCurrent_matter_eq_profile]
  rfl

theorem
    preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_regularityState :
    PreContorsionFullLorentzTriangularCurrent.conjugateMatter =
      preContorsionFullLorentzRegularityState.conjugateMatter := by
  rw [preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_profile]
  rfl

theorem
    preContorsionFullLorentzTriangularCurrent_scalar_eq_regularityState :
    PreContorsionFullLorentzTriangularCurrent.scalar =
      preContorsionFullLorentzRegularityState.scalar := by
  rw [preContorsionFullLorentzTriangularCurrent_scalar_vacuum]
  funext space
  change
    sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource =
      preContorsionSpatialProfileActual.scalar
        (canonicalCauchySlicePoint 0 space)
  rw [preContorsionSpatialProfileActual_scalar_vacuum]

/-! ## Coherent dual-field normal form -/

private theorem canonicalCauchySlicePoint_zeroSpace_eq_timeLine
    (time : ℝ) :
    canonicalCauchySlicePoint time (0 : StageNineSpatialPoint) =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-- The whole-domain coherent dual field is exactly the corrected current's
zero-slice dual plus canonical time times the action-generated adjoint
response at the matching contact. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_apply_normalForm
    (point : BasePoint) (matter : DiracExteriorMatterCarrier) :
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
        point matter =
      PreContorsionFullLorentzTriangularCurrent.conjugateMatter
          (canonicalSpatialProjection point) matter +
        canonicalTimeProjection point •
          currentCanonicalFullActionLorentzStateAdjointResponse
            PreContorsionFullLorentzTriangularCurrent
            (canonicalSpatialProjection point) matter := by
  change
    (currentCanonicalFullActionLorentzActualFirstJetLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      (canonicalSpatialProjection point)).conjugateMatter
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) matter =
      _
  change
    actionGeneratedConjugateMatterLocalField
        PreContorsionFullLorentzTriangularCurrent
        (canonicalSpatialProjection point)
        (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
        matter =
      _
  rw [actionGeneratedConjugateMatterLocalField_apply,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine, map_smul,
    actionGeneratedConjugateMatterLocalEvaluationIncrement_coordinateDirection]
  rfl

/-! ## Smooth adjoint response on the generated final current -/

private theorem canonicalCauchySlicePoint_zero_contDiff :
    ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show
    canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
    funext space
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    simp]
  exact canonicalSpatialInclusion.contDiff

/-- Spatial differentiation of the conjugate field after a genuine smooth
Cauchy restriction is the matching spacetime derivative. -/
private theorem
    canonicalCauchyRestriction_conjugateMatterSpatialDerivative_eq_holonomic
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    cauchyConjugateMatterSpatialDerivative
        (canonicalCauchyRestriction 0 configuration) space axis =
      holonomicConjugateMatterDerivativeDual configuration
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  unfold cauchyConjugateMatterSpatialDerivative
    holonomicConjugateMatterDerivativeDual
  apply congrArg matterDualOfCoordinates
  unfold cauchyConjugateMatterSpatialDerivativeCoordinate
    holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  change
    fderiv ℝ
        (holonomicConjugateMatterCoordinates configuration ∘
          canonicalCauchySlicePoint 0)
        space (canonicalSpatialCoordinateDirection axis) =
      fderiv ℝ (holonomicConjugateMatterCoordinates configuration)
        (canonicalCauchySlicePoint 0 space)
        (coordinateDirection axis.succ)
  have outer :
      DifferentiableAt ℝ
        (holonomicConjugateMatterCoordinates configuration)
        (canonicalCauchySlicePoint 0 space) :=
    ((holonomicConjugateMatterCoordinates_contDiff configuration smooth)
      |>.differentiable (by simp)).differentiableAt
  have composed := outer.hasFDerivAt.comp space
    (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  rw [composed.fderiv]
  simp [ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

private theorem
    actionGeneratedMatterAlgebraicOperator_canonicalCauchyRestriction
    (configuration : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterAlgebraicOperator
        (canonicalCauchyRestriction 0 configuration) space =
      holonomicIdentityCoframeMatterAlgebraicOperator configuration
        (canonicalCauchySlicePoint 0 space) := by
  rfl

private theorem
    actionGeneratedConjugateMatterSpatialTransport_canonicalCauchyRestriction
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterSpatialTransport
        (canonicalCauchyRestriction 0 configuration) space =
      holonomicIdentityCoframeConjugateMatterSpatialTransport configuration
        (canonicalCauchySlicePoint 0 space) := by
  unfold actionGeneratedConjugateMatterSpatialTransport
    holonomicIdentityCoframeConjugateMatterSpatialTransport
  apply Finset.sum_congr rfl
  intro axis _
  rw [
    canonicalCauchyRestriction_conjugateMatterSpatialDerivative_eq_holonomic
      configuration smooth space axis]

/-- The Cauchy adjoint response of a genuinely smooth restricted actual is
the holonomic adjoint action velocity of that actual at the same point. -/
theorem
    actionGeneratedConjugateMatterTimeDerivative_canonicalCauchyRestriction
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterTimeDerivative
        (canonicalCauchyRestriction 0 configuration) space =
      holonomicIdentityCoframeConjugateMatterActionVelocity configuration
        (canonicalCauchySlicePoint 0 space) := by
  unfold actionGeneratedConjugateMatterTimeDerivative
    actionGeneratedConjugateMatterKnownDual
    holonomicIdentityCoframeConjugateMatterActionVelocity
    holonomicIdentityCoframeConjugateMatterKnownDual
  rw [
    actionGeneratedMatterAlgebraicOperator_canonicalCauchyRestriction,
    actionGeneratedConjugateMatterSpatialTransport_canonicalCauchyRestriction
      configuration smooth]
  rfl

private theorem
    actionGeneratedConjugateMatterTimeDerivative_eq_of_fields
    (first second : StageNineCauchyState)
    (gravityConnection :
      first.gravityConnection = second.gravityConnection)
    (gaugeConnection : first.gaugeConnection = second.gaugeConnection)
    (scalar : first.scalar = second.scalar)
    (conjugateMatter : first.conjugateMatter = second.conjugateMatter)
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterTimeDerivative first space =
      actionGeneratedConjugateMatterTimeDerivative second space := by
  unfold actionGeneratedConjugateMatterTimeDerivative
    actionGeneratedConjugateMatterKnownDual
    actionGeneratedConjugateMatterSpatialTransport
    actionGeneratedMatterAlgebraicOperator
    cauchyMatterVariationConnectionOperator
    cauchyConjugateMatterSpatialDerivative
    cauchyConjugateMatterSpatialDerivativeCoordinate
  rw [gravityConnection, gaugeConnection, scalar, conjugateMatter]

/-- The corrected-current adjoint response is read from one smooth
zero-slice carrier.  This is regularity provenance, not replacement of the
C3h200r actual by the proof-only carrier. -/
theorem
    preContorsionFullLorentzTriangularCurrent_adjointResponse_eq_regularityActual
    (space : StageNineSpatialPoint) :
    currentCanonicalFullActionLorentzStateAdjointResponse
        PreContorsionFullLorentzTriangularCurrent space =
      holonomicIdentityCoframeConjugateMatterActionVelocity
        preContorsionFullLorentzZeroSliceRegularityActual
        (canonicalCauchySlicePoint 0 space) := by
  unfold currentCanonicalFullActionLorentzStateAdjointResponse
  calc
    actionGeneratedConjugateMatterTimeDerivative
          PreContorsionFullLorentzTriangularCurrent space =
        actionGeneratedConjugateMatterTimeDerivative
          preContorsionFullLorentzRegularityState space := by
      exact actionGeneratedConjugateMatterTimeDerivative_eq_of_fields
        PreContorsionFullLorentzTriangularCurrent
        preContorsionFullLorentzRegularityState
        preContorsionFullLorentzTriangularCurrent_gravityConnection_eq_regularityState
        preContorsionFullLorentzTriangularCurrent_gaugeConnection_eq_regularityState
        preContorsionFullLorentzTriangularCurrent_scalar_eq_regularityState
        preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_regularityState
        space
    _ =
        holonomicIdentityCoframeConjugateMatterActionVelocity
          preContorsionFullLorentzZeroSliceRegularityActual
          (canonicalCauchySlicePoint 0 space) :=
      actionGeneratedConjugateMatterTimeDerivative_canonicalCauchyRestriction
        preContorsionFullLorentzZeroSliceRegularityActual
        preContorsionFullLorentzZeroSliceRegularityActual_smooth space

/-- The action-generated adjoint response varies smoothly across the
matching spatial contacts. -/
theorem
    preContorsionFullLorentzTriangularCurrent_adjointResponse_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun space =>
      currentCanonicalFullActionLorentzStateAdjointResponse
        PreContorsionFullLorentzTriangularCurrent space matter := by
  rw [show
    (fun space =>
      currentCanonicalFullActionLorentzStateAdjointResponse
        PreContorsionFullLorentzTriangularCurrent space matter) =
      fun space =>
        holonomicIdentityCoframeConjugateMatterActionVelocity
          preContorsionFullLorentzZeroSliceRegularityActual
          (canonicalCauchySlicePoint 0 space) matter by
    funext space
    rw [
      preContorsionFullLorentzTriangularCurrent_adjointResponse_eq_regularityActual]]
  exact
    (holonomicIdentityCoframeConjugateMatterActionVelocity_apply_contDiff
      preContorsionFullLorentzZeroSliceRegularityActual
      preContorsionFullLorentzZeroSliceRegularityActual_smooth matter).comp
      canonicalCauchySlicePoint_zero_contDiff

/-! ## Genuine coherent dual-field regularity -/

private theorem
    preContorsionFullLorentzZeroSliceRegularityActual_conjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point =>
      preContorsionFullLorentzZeroSliceRegularityActual.conjugateMatter
        point matter := by
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterDualCoordinateEvaluation matter).restrictScalars ℝ
  have composed :
      ContDiff ℝ ∞ fun point =>
        evaluation
          (holonomicConjugateMatterCoordinates
            preContorsionFullLorentzZeroSliceRegularityActual point) :=
    evaluation.contDiff.comp
      (holonomicConjugateMatterCoordinates_contDiff
        preContorsionFullLorentzZeroSliceRegularityActual
        preContorsionFullLorentzZeroSliceRegularityActual_smooth)
  rw [show
    (fun point =>
      evaluation
        (holonomicConjugateMatterCoordinates
          preContorsionFullLorentzZeroSliceRegularityActual point)) =
      fun point =>
        preContorsionFullLorentzZeroSliceRegularityActual.conjugateMatter
          point matter by
    funext point
    dsimp only [evaluation]
    change
      matterDualCoordinateEvaluation matter
          (holonomicConjugateMatterCoordinates
            preContorsionFullLorentzZeroSliceRegularityActual point) =
        preContorsionFullLorentzZeroSliceRegularityActual.conjugateMatter
          point matter
    rw [matterDualCoordinateEvaluation_apply]
    unfold holonomicConjugateMatterCoordinates
    rw [matterDualOfCoordinates_surjective]]
    at composed
  exact composed

theorem
    preContorsionFullLorentzTriangularCurrent_conjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun space =>
      PreContorsionFullLorentzTriangularCurrent.conjugateMatter
        space matter := by
  rw [preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_regularityState]
  exact
    (preContorsionFullLorentzZeroSliceRegularityActual_conjugateMatter_apply_contDiff
      matter).comp canonicalCauchySlicePoint_zero_contDiff

/-- The C3h200r conjugate field is genuinely smooth in every fixed matter
direction.  Consequently its Fréchet derivative cannot collapse to the
totalized nondifferentiable zero. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point =>
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
        point matter := by
  rw [show
    (fun point =>
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
        point matter) =
      fun point =>
        PreContorsionFullLorentzTriangularCurrent.conjugateMatter
            (canonicalSpatialProjection point) matter +
          canonicalTimeProjection point •
            currentCanonicalFullActionLorentzStateAdjointResponse
              PreContorsionFullLorentzTriangularCurrent
              (canonicalSpatialProjection point) matter by
    funext point
    exact
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_apply_normalForm
        point matter]
  have baseSmooth :
      ContDiff ℝ ∞ fun point =>
        PreContorsionFullLorentzTriangularCurrent.conjugateMatter
          (canonicalSpatialProjection point) matter :=
    (preContorsionFullLorentzTriangularCurrent_conjugateMatter_apply_contDiff
      matter).comp canonicalSpatialProjection.contDiff
  have velocitySmooth :
      ContDiff ℝ ∞ fun point =>
        currentCanonicalFullActionLorentzStateAdjointResponse
          PreContorsionFullLorentzTriangularCurrent
          (canonicalSpatialProjection point) matter :=
    (preContorsionFullLorentzTriangularCurrent_adjointResponse_apply_contDiff
      matter).comp canonicalSpatialProjection.contDiff
  have timeVelocitySmooth :
      ContDiff ℝ ∞ fun point =>
        canonicalTimeProjection point •
          currentCanonicalFullActionLorentzStateAdjointResponse
            PreContorsionFullLorentzTriangularCurrent
            (canonicalSpatialProjection point) matter :=
    canonicalTimeProjection.contDiff.smul velocitySmooth
  exact baseSmooth.add timeVelocitySmooth

private theorem deriv_along_canonicalCauchyOrigin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V)
    (differentiable : DifferentiableAt ℝ field 0) :
    deriv
        (fun time : ℝ =>
          field (canonicalCauchySlicePoint time 0))
        0 =
      fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection := by
  let line := fun time : ℝ =>
    time • coordinateDirection canonicalLorentzianTimeDirection
  have lineDerivative :
      HasDerivAt line
        (coordinateDirection canonicalLorentzianTimeDirection) 0 := by
    simpa [line] using
      (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)
  have outerDerivative :
      HasFDerivAt field (fderiv ℝ field 0) (line 0) := by
    simpa [line] using differentiable.hasFDerivAt
  have composed :=
    outerDerivative.comp_hasDerivAt 0 lineDerivative
  unfold fieldDirectionalDerivative
  rw [show
    (fun time : ℝ =>
      field (canonicalCauchySlicePoint time 0)) =
        field ∘ line by
    funext time
    simp only [Function.comp_apply, line,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine]]
  exact composed.deriv

/-- The actual C3h200r temporal Fréchet derivative is the unique
action-generated adjoint response of the corrected current. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_timeDerivative
    (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point =>
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
            point matter)
        0 canonicalLorentzianTimeDirection =
      currentCanonicalFullActionLorentzStateAdjointResponse
        PreContorsionFullLorentzTriangularCurrent 0 matter := by
  calc
    _ =
        deriv
          (fun time : ℝ =>
            positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
              (canonicalCauchySlicePoint time 0) matter)
          0 :=
      (deriv_along_canonicalCauchyOrigin _
        ((positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_apply_contDiff
          matter).differentiable (by simp) |>.differentiableAt)).symm
    _ =
        (currentCanonicalFullActionLorentzStateResponse
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent 0).conjugateMatter
          matter :=
      coherentDiagonalActual_conjugateMatter_originTangent
        positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0 matter
    _ =
        currentCanonicalFullActionLorentzStateAdjointResponse
          PreContorsionFullLorentzTriangularCurrent 0 matter := by
      rw [currentCanonicalFullActionLorentzStateResponse_conjugateMatter]

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterAdjointRegularity
