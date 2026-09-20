import H0mework.Physics.MatterPreparation.ContorsionCoherentMatterAdjointRegularity

/-!
# S9-C3h201f: coherent adjoint complete first germ

C3h201e proved genuine component-level smoothness and identified the temporal
Fréchet derivative of the C3h200r whole-domain dual field with the freshly
recomputed corrected-current adjoint response.

This module closes the remaining three components without reconstructing an
endpoint from residual fields:

```text
whole-domain action-generated dual normal form
→ differentiate the current-owned zero slice
→ the time-response product has zero spatial first derivative at time zero
→ all four components equal the primitive action-generated local jet.
```

The result is a same-actual first-germ realization.  The temporal action law
is still producer soundness, while the spatial components are primitive
Cauchy derivatives carried by the corrected current.  No extra equation
receipt, branch choice, or target jet is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterAdjointFullFirstGerm

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterAdjointRegularity
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

private theorem canonicalCauchySlicePoint_zero_contDiff :
    ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show
    canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
    funext space
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    simp]
  exact canonicalSpatialInclusion.contDiff

private theorem canonicalTimeProjection_coordinateSpatial
    (axis : Fin 3) :
    canonicalTimeProjection (coordinateDirection axis.succ) = 0 := by
  fin_cases axis <;>
    simp [canonicalTimeProjection, localBaseCoordinate_apply,
      coordinateDirection, canonicalLorentzianTimeDirection]

private theorem canonicalSpatialProjection_coordinateSpatial
    (axis : Fin 3) :
    canonicalSpatialProjection (coordinateDirection axis.succ) =
      canonicalSpatialCoordinateDirection axis := by
  apply PiLp.ext
  intro component
  fin_cases axis <;> fin_cases component <;>
    simp [canonicalSpatialProjection, canonicalSpatialCoordinateDirection,
      localBaseCoordinate_apply, coordinateDirection]

/-! ## Evaluation of a genuine Cauchy dual derivative -/

/-- For a coordinate-regular Cauchy dual field, reconstructing its spatial
coordinate derivative and then evaluating it is exactly the scalar Fréchet
derivative of the evaluated dual field. -/
private theorem
    cauchyConjugateMatterSpatialDerivative_apply_eq_fderiv
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (matter : DiracExteriorMatterCarrier)
    (regular :
      DifferentiableAt ℝ
        (fun candidate =>
          matterDualCoordinates (state.conjugateMatter candidate))
        space) :
    cauchyConjugateMatterSpatialDerivative state space axis matter =
      fderiv ℝ
        (fun candidate => state.conjugateMatter candidate matter)
        space (canonicalSpatialCoordinateDirection axis) := by
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterDualCoordinateEvaluation matter).restrictScalars ℝ
  have evaluationIdentity :
      (fun candidate => state.conjugateMatter candidate matter) =
        fun candidate =>
          evaluation
            (matterDualCoordinates (state.conjugateMatter candidate)) := by
    funext candidate
    dsimp only [evaluation]
    change
      state.conjugateMatter candidate matter =
        matterDualCoordinateEvaluation matter
          (matterDualCoordinates (state.conjugateMatter candidate))
    rw [matterDualCoordinateEvaluation_apply,
      matterDualOfCoordinates_surjective]
  have derivative :=
    evaluation.hasFDerivAt.comp space regular.hasFDerivAt
  unfold cauchyConjugateMatterSpatialDerivative
    cauchyConjugateMatterSpatialDerivativeCoordinate
  rw [evaluationIdentity]
  change
    matterDualOfCoordinates
          (fderiv ℝ
            (fun candidate =>
              matterDualCoordinates (state.conjugateMatter candidate))
            space (canonicalSpatialCoordinateDirection axis))
          matter =
      fderiv ℝ
        (evaluation ∘
          fun candidate =>
            matterDualCoordinates (state.conjugateMatter candidate))
        space (canonicalSpatialCoordinateDirection axis)
  rw [derivative.fderiv]
  change
    matterDualOfCoordinates
          (fderiv ℝ
            (fun candidate =>
              matterDualCoordinates (state.conjugateMatter candidate))
            space (canonicalSpatialCoordinateDirection axis))
          matter =
      matterDualCoordinateEvaluation matter
        (fderiv ℝ
          (fun candidate =>
            matterDualCoordinates (state.conjugateMatter candidate))
          space (canonicalSpatialCoordinateDirection axis))
  rw [matterDualCoordinateEvaluation_apply]

theorem
    preContorsionFullLorentzTriangularCurrent_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞ fun space =>
      matterDualCoordinates
        (PreContorsionFullLorentzTriangularCurrent.conjugateMatter space) := by
  rw [preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_regularityState]
  change
    ContDiff ℝ ∞ fun space =>
      holonomicConjugateMatterCoordinates
        preContorsionFullLorentzZeroSliceRegularityActual
        (canonicalCauchySlicePoint 0 space)
  exact
    (holonomicConjugateMatterCoordinates_contDiff
      preContorsionFullLorentzZeroSliceRegularityActual
      preContorsionFullLorentzZeroSliceRegularityActual_smooth).comp
      canonicalCauchySlicePoint_zero_contDiff

private theorem actionGeneratedConjugateMatterLocalJet_spatial
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    actionGeneratedConjugateMatterLocalJet state space axis.succ =
      cauchyConjugateMatterSpatialDerivative state space axis := by
  fin_cases axis <;> rfl

/-! ## The three spatial components -/

/-- On the generated time-zero slice, the spatial derivative of the coherent
dual field is exactly the corrected current's primitive Cauchy derivative.
The action-generated time-response term contributes no spatial first-order
piece because its scalar time factor vanishes at the slice. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_spatialDerivative
    (axis : Fin 3)
    (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point =>
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
            point matter)
        0 axis.succ =
      actionGeneratedConjugateMatterLocalJet
        PreContorsionFullLorentzTriangularCurrent 0 axis.succ matter := by
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
  unfold fieldDirectionalDerivative
  have baseDerivative :
      HasFDerivAt
        (fun space =>
          PreContorsionFullLorentzTriangularCurrent.conjugateMatter
            space matter)
        (fderiv ℝ
          (fun space =>
            PreContorsionFullLorentzTriangularCurrent.conjugateMatter
              space matter)
          (canonicalSpatialProjection (0 : BasePoint)))
        (canonicalSpatialProjection (0 : BasePoint)) :=
    ((preContorsionFullLorentzTriangularCurrent_conjugateMatter_apply_contDiff
      matter).differentiable (by simp) |>.differentiableAt).hasFDerivAt
  have composedBaseDerivative :=
    baseDerivative.comp (0 : BasePoint)
      canonicalSpatialProjection.hasFDerivAt
  have velocityDerivative :
      HasFDerivAt
        (fun space =>
          currentCanonicalFullActionLorentzStateAdjointResponse
            PreContorsionFullLorentzTriangularCurrent space matter)
        (fderiv ℝ
          (fun space =>
            currentCanonicalFullActionLorentzStateAdjointResponse
              PreContorsionFullLorentzTriangularCurrent space matter)
          (canonicalSpatialProjection (0 : BasePoint)))
        (canonicalSpatialProjection (0 : BasePoint)) :=
    ((preContorsionFullLorentzTriangularCurrent_adjointResponse_apply_contDiff
      matter).differentiable (by simp) |>.differentiableAt).hasFDerivAt
  have composedVelocityDerivative :=
    velocityDerivative.comp (0 : BasePoint)
      canonicalSpatialProjection.hasFDerivAt
  have productDerivative :=
    canonicalTimeProjection.hasFDerivAt.smul composedVelocityDerivative
  have totalDerivative :=
    composedBaseDerivative.add productDerivative
  have functionEquality :
      (fun point =>
        PreContorsionFullLorentzTriangularCurrent.conjugateMatter
            (canonicalSpatialProjection point) matter +
          canonicalTimeProjection point •
            currentCanonicalFullActionLorentzStateAdjointResponse
              PreContorsionFullLorentzTriangularCurrent
              (canonicalSpatialProjection point) matter) =
      ((fun space =>
        PreContorsionFullLorentzTriangularCurrent.conjugateMatter
          space matter) ∘ canonicalSpatialProjection) +
        (fun point : BasePoint => canonicalTimeProjection point) •
          ((fun space =>
            currentCanonicalFullActionLorentzStateAdjointResponse
              PreContorsionFullLorentzTriangularCurrent space matter) ∘
            canonicalSpatialProjection) := by
    funext point
    rfl
  rw [functionEquality, totalDerivative.fderiv,
    actionGeneratedConjugateMatterLocalJet_spatial]
  simp [canonicalSpatialProjection_coordinateSpatial,
    canonicalTimeProjection_coordinateSpatial]
  exact
    (cauchyConjugateMatterSpatialDerivative_apply_eq_fderiv
      PreContorsionFullLorentzTriangularCurrent 0 axis matter
      ((preContorsionFullLorentzTriangularCurrent_conjugateMatterCoordinates_contDiff
        ).differentiable (by simp) |>.differentiableAt)).symm

/-! ## Complete four-component dual germ -/

/-- The same generated C3h200r actual realizes the complete action-generated
dual first jet at the origin. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_completeFirstGerm
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point =>
          positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.conjugateMatter
            point matter)
        0 direction =
      actionGeneratedConjugateMatterLocalJet
        PreContorsionFullLorentzTriangularCurrent 0 direction matter := by
  fin_cases direction
  · simpa [canonicalLorentzianTimeDirection,
      actionGeneratedConjugateMatterLocalJet,
      currentCanonicalFullActionLorentzStateAdjointResponse] using
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_timeDerivative
        matter
  · simpa using
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_spatialDerivative
        (0 : Fin 3) matter
  · simpa using
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_spatialDerivative
        (1 : Fin 3) matter
  · simpa [Fin.succ] using
      positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_conjugateMatter_spatialDerivative
        (2 : Fin 3) matter

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterAdjointFullFirstGerm
