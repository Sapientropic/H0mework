import H0mework.Physics.MatterPreparation.ContorsionCoherentMatterAdjointFullFirstGerm

/-!
# S9-C3h201g: coherent primal-matter normal form

The C3h200r whole-domain actual is assembled contact by contact from the
complete action actual.  Its primal matter field therefore contains both the
primitive first jet and the internally generated temporal/complete
second-jet corrections.

This module exposes that exact dependence before proving regularity:

```text
matter coordinate on C3h200r
= corrected-current slice M(x)
 + t · raw action velocity Vraw(x)
 + (t² / 2) · Q(x).
```

`Q` is not supplied.  It is the sum of the temporal acceleration and the
time--time component of the complete Hessian generated internally from the
same current/action graph.  Mixed time--space corrections vanish on the
diagonal constructor's local zero-space line.  This normal form isolates the
remaining genuine regularity obligation without changing the producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterNormalForm

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeScalarMatterRegularity
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterActionTimeVelocity
open StageNineMatterCompleteFirstGermPrincipal
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineScalarActionSecondJetLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentActual
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentBFMomentumRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterAdjointRegularity
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra
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

private abbrev finalCurrentP286Actual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  currentCanonicalGravityPreservingP286Actual positiveSmoothUnifiedSource
    PreContorsionFullLorentzTriangularCurrent space

private abbrev finalCurrentTemporalMatterActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  currentCanonicalGravityPreservingTemporalMatterActual
    positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent space

private abbrev finalCurrentRegularityState : StageNineCauchyState :=
  canonicalCauchyRestriction 0
    preContorsionFullLorentzZeroSliceRegularityActual

/-- The temporal acceleration internally generated at each corrected-current
contact.  It is an action readout, not source data. -/
def preContorsionFullLorentzCoherentTemporalAcceleration
    (space : StageNineSpatialPoint) : DiracExteriorMatterCarrier :=
  actionGeneratedMatterTemporalFirstGermAcceleration
    positiveSmoothUnifiedSource (finalCurrentP286Actual space)

/-- The complete temporal-pivot Hessian internally generated after installing
the temporal response at the same contact. -/
def preContorsionFullLorentzCoherentCompleteHessian
    (space : StageNineSpatialPoint) : TemporalPivotMatterHessian :=
  actionGeneratedMatterCompleteFirstGermHessian
    positiveSmoothUnifiedSource (finalCurrentTemporalMatterActual space)

/-- The only second-order matter coordinate that survives the coherent
diagonal's local zero-space evaluation. -/
def preContorsionFullLorentzCoherentMatterQuadraticResponse
    (space : StageNineSpatialPoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv
      (preContorsionFullLorentzCoherentTemporalAcceleration space) +
    matterCoordinateEquiv
      ((preContorsionFullLorentzCoherentCompleteHessian space).timeTime)

/-! ## Regular primitive and linear-response terms -/

/-- The corrected current's primitive matter slice has genuine smooth finite
coordinates inherited from the proof-only smooth zero-slice carrier. -/
theorem
    preContorsionFullLorentzTriangularCurrent_matterCoordinates_contDiff :
    ContDiff ℝ ∞ fun space =>
      matterCoordinateEquiv
        (PreContorsionFullLorentzTriangularCurrent.matter space) := by
  rw [preContorsionFullLorentzTriangularCurrent_matter_eq_regularityState]
  exact
    preContorsionFullLorentzZeroSliceRegularityActual_smooth
      |>.2.2.2.2.2.2.2.1
      |>.comp canonicalCauchySlicePoint_zero_contDiff

private theorem
    canonicalCauchyRestriction_matterSpatialDerivative_eq_holonomic
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    cauchyMatterSpatialDerivativeCoordinate
        (canonicalCauchyRestriction 0 configuration) space axis =
      fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv (configuration.matter point))
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  unfold cauchyMatterSpatialDerivativeCoordinate
    fieldDirectionalDerivative
  change
    fderiv ℝ
        ((fun point =>
          matterCoordinateEquiv (configuration.matter point)) ∘
            canonicalCauchySlicePoint 0)
        space (canonicalSpatialCoordinateDirection axis) =
      fderiv ℝ
        (fun point =>
          matterCoordinateEquiv (configuration.matter point))
        (canonicalCauchySlicePoint 0 space)
        (coordinateDirection axis.succ)
  have outer :
      DifferentiableAt ℝ
        (fun point =>
          matterCoordinateEquiv (configuration.matter point))
        (canonicalCauchySlicePoint 0 space) :=
    (smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have composed := outer.hasFDerivAt.comp space
    (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  rw [composed.fderiv]
  simp [ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

private theorem
    cauchyMatterSpatialCovariantDerivative_canonicalCauchyRestriction
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    cauchyMatterSpatialCovariantDerivative
        (canonicalCauchyRestriction 0 configuration) space axis =
      holonomicMatterCovariantDerivative configuration
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  unfold cauchyMatterSpatialCovariantDerivative
    holonomicMatterCovariantDerivative cauchyMatterConnectionAction
  rw [
    canonicalCauchyRestriction_matterSpatialDerivative_eq_holonomic
      configuration smooth space axis]
  simp only [canonicalCauchyRestriction]
  module

def holonomicIdentityCoframeMatterKnownVector
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : Fin 3,
        diracMatrixMatterAction (diracGamma direction.succ)
          (holonomicMatterCovariantDerivative configuration point
            direction.succ) +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point))
      (configuration.matter point)

def holonomicMatterConnectionAction
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
      (diracSpinConnectionLift
        (configuration.gravityConnection point) direction)
      (configuration.matter point) +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed
        (configuration.gaugeConnection point direction))
      (configuration.matter point)

def holonomicIdentityCoframeMatterRawTimeVelocity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  -identityCoframeMatterTimePrincipal
      (holonomicIdentityCoframeMatterKnownVector configuration point) -
    holonomicMatterConnectionAction configuration point
      canonicalLorentzianTimeDirection

theorem
    actionGeneratedMatterRawTimeVelocity_canonicalCauchyRestriction
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterRawTimeVelocity
        (canonicalCauchyRestriction 0 configuration) space =
      holonomicIdentityCoframeMatterRawTimeVelocity configuration
        (canonicalCauchySlicePoint 0 space) := by
  unfold actionGeneratedMatterRawTimeVelocity
    actionGeneratedMatterTimeCovariantDerivative
    actionGeneratedMatterKnownVector
    holonomicIdentityCoframeMatterRawTimeVelocity
    holonomicIdentityCoframeMatterKnownVector
    cauchyMatterConnectionAction holonomicMatterConnectionAction
  simp_rw [
    cauchyMatterSpatialCovariantDerivative_canonicalCauchyRestriction
      configuration smooth]
  rfl

private theorem
    holonomicIdentityCoframeMatterKnownVector_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (holonomicIdentityCoframeMatterKnownVector configuration point) := by
  have kineticDirectionSmooth : ∀ direction : Fin 3,
      ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction.succ)
            (holonomicMatterCovariantDerivative configuration point
              direction.succ)) := by
    intro direction
    let actionLinear : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
      (diracMatrixMatterCoordinateRealBilinear
        (diracGamma direction.succ)).toContinuousLinearMap
    have actual := actionLinear.contDiff.comp
      (holonomicMatterCovariantDerivative_coordinate_contDiff_local
        configuration smooth direction.succ)
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma direction.succ)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicMatterCovariantDerivative configuration point
                direction.succ)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have kineticSumSmooth : ContDiff ℝ ∞ fun point =>
      ∑ direction : Fin 3,
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction.succ)
            (holonomicMatterCovariantDerivative configuration point
              direction.succ)) := by
    exact ContDiff.sum fun direction _ => kineticDirectionSmooth direction
  have kineticSmooth : ContDiff ℝ ∞ fun point =>
      Complex.I •
        ∑ direction : Fin 3,
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma direction.succ)
              (holonomicMatterCovariantDerivative configuration point
                direction.succ)) := by
    have iSmooth : ContDiff ℝ ∞ fun _ : BasePoint =>
        (Complex.I : ℂ) := contDiff_const
    exact iSmooth.smul kineticSumSmooth
  have yukawaSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (configuration.matter point)) := by
    have actual :=
      (chiralExteriorYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        smooth.2.2.2.2.2.2.1).clm_apply
          smooth.2.2.2.2.2.2.2.1
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (configuration.matter point)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicIdentityCoframeMatterKnownVector
  simp only [map_add, map_smul, map_sum]
  exact kineticSmooth.add yukawaSmooth

private theorem
    holonomicMatterConnectionAction_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (holonomicMatterConnectionAction configuration point direction) := by
  rw [show
    (fun point =>
      matterCoordinateEquiv
        (holonomicMatterConnectionAction configuration point direction)) =
      fun point =>
        matterCoordinateEquiv
            (holonomicMatterCovariantDerivative configuration point
              direction) -
          fieldDirectionalDerivative
            (fun candidate =>
              matterCoordinateEquiv (configuration.matter candidate))
            point direction by
    funext point
    unfold holonomicMatterConnectionAction
      holonomicMatterCovariantDerivative
    simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
    module]
  exact
    (holonomicMatterCovariantDerivative_coordinate_contDiff_local
      configuration smooth direction).sub
      (holonomicMatterCoordinateDerivative_contDiff_local
        configuration smooth direction)

theorem
    holonomicIdentityCoframeMatterRawTimeVelocity_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (holonomicIdentityCoframeMatterRawTimeVelocity configuration point) := by
  have knownSmooth :=
    holonomicIdentityCoframeMatterKnownVector_coordinate_contDiff
      configuration smooth
  let actionLinear : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
    (diracMatrixMatterCoordinateRealBilinear
      (diracGamma canonicalLorentzianTimeDirection)).toContinuousLinearMap
  have actionSmooth := actionLinear.contDiff.comp knownSmooth
  have principalSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (identityCoframeMatterTimePrincipal
          (holonomicIdentityCoframeMatterKnownVector configuration point)) := by
    have iSmooth : ContDiff ℝ ∞ fun _ : BasePoint =>
        (Complex.I : ℂ) := contDiff_const
    have actionSmooth' : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracGamma canonicalLorentzianTimeDirection)
            (holonomicIdentityCoframeMatterKnownVector
              configuration point)) := by
      change ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracGamma canonicalLorentzianTimeDirection)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                (holonomicIdentityCoframeMatterKnownVector
                  configuration point)))) at actionSmooth
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actionSmooth
    unfold identityCoframeMatterTimePrincipal
    simp only [map_smul]
    exact iSmooth.smul actionSmooth'
  unfold holonomicIdentityCoframeMatterRawTimeVelocity
  simp only [map_sub, map_neg]
  exact principalSmooth.neg.sub
    (holonomicMatterConnectionAction_coordinate_contDiff configuration smooth
      canonicalLorentzianTimeDirection)

private theorem
    actionGeneratedMatterRawTimeVelocity_eq_of_fields
    (first second : StageNineCauchyState)
    (gravityConnection :
      first.gravityConnection = second.gravityConnection)
    (gaugeConnection :
      first.gaugeConnection = second.gaugeConnection)
    (scalar : first.scalar = second.scalar)
    (matter : first.matter = second.matter)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterRawTimeVelocity first space =
      actionGeneratedMatterRawTimeVelocity second space := by
  unfold actionGeneratedMatterRawTimeVelocity
    actionGeneratedMatterTimeCovariantDerivative
    actionGeneratedMatterKnownVector
    cauchyMatterSpatialCovariantDerivative
    cauchyMatterConnectionAction
    cauchyMatterSpatialDerivativeCoordinate
  rw [gravityConnection, gaugeConnection, scalar, matter]

/-- The raw primal response varies smoothly across the matching corrected
current contacts.  The proof-only carrier supplies only regularity
provenance; the response remains generated by the actual current/action
mouth. -/
theorem
    preContorsionFullLorentzTriangularCurrent_rawMatterVelocityCoordinates_contDiff :
    ContDiff ℝ ∞ fun space =>
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity
          PreContorsionFullLorentzTriangularCurrent space) := by
  rw [show
    (fun space =>
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity
          PreContorsionFullLorentzTriangularCurrent space)) =
      fun space =>
        matterCoordinateEquiv
          (holonomicIdentityCoframeMatterRawTimeVelocity
            preContorsionFullLorentzZeroSliceRegularityActual
            (canonicalCauchySlicePoint 0 space)) by
    funext space
    rw [
      actionGeneratedMatterRawTimeVelocity_eq_of_fields
        PreContorsionFullLorentzTriangularCurrent
        finalCurrentRegularityState
        preContorsionFullLorentzTriangularCurrent_gravityConnection_eq_regularityState
        preContorsionFullLorentzTriangularCurrent_gaugeConnection_eq_regularityState
        preContorsionFullLorentzTriangularCurrent_scalar_eq_regularityState
        preContorsionFullLorentzTriangularCurrent_matter_eq_regularityState,
      actionGeneratedMatterRawTimeVelocity_canonicalCauchyRestriction
        preContorsionFullLorentzZeroSliceRegularityActual
        preContorsionFullLorentzZeroSliceRegularityActual_smooth]]
  exact
    (holonomicIdentityCoframeMatterRawTimeVelocity_coordinate_contDiff
      preContorsionFullLorentzZeroSliceRegularityActual
      preContorsionFullLorentzZeroSliceRegularityActual_smooth).comp
      canonicalCauchySlicePoint_zero_contDiff

private theorem actionGeneratedMatterLocalIncrement_timeLine
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    actionGeneratedMatterLocalIncrement state space
        (canonicalCauchySlicePoint time 0) =
      time • matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity state space) := by
  unfold actionGeneratedMatterLocalIncrement
    actionGeneratedMatterLocalJetCoordinate
  rw [Fin.sum_univ_four]
  simp [canonicalCauchySlicePoint, localBaseCoordinate_apply,
    canonicalLorentzianTimeDirection]

private theorem matterCompleteQuadraticCoordinateCorrection_timeLine
    (hessian : TemporalPivotMatterHessian)
    (time : ℝ) :
    matterCompleteQuadraticCoordinateCorrection hessian
        (canonicalCauchySlicePoint time 0) =
      scalarQuadraticTimeCoefficient
          (canonicalCauchySlicePoint time 0) •
        matterCoordinateEquiv hessian.timeTime := by
  unfold matterCompleteQuadraticCoordinateCorrection
  have mixedZero (axis : Fin 3) :
      matterMixedTimeSpatialCoordinateCorrection axis
          (hessian.timeSpatial axis)
          (canonicalCauchySlicePoint time 0) =
        0 := by
    simp [matterMixedTimeSpatialCoordinateCorrection,
      matterMixedTimeSpatialCoefficient, canonicalCauchySlicePoint,
      localBaseCoordinate_apply, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]
  simp_rw [mixedZero]
  simp [matterQuadraticTimeCoordinateCorrection]

/-- Exact primal coordinate normal form on the C3h200r whole-domain actual.
Both second-order responses are generated from the same corrected current;
no coefficient or response witness is accepted as input. -/
theorem
    positiveP506MatterPreContorsionFullLorentzFreshCoherentActual_matterCoordinate_normalForm
    (point : BasePoint) :
    matterCoordinateEquiv
        (positiveP506MatterPreContorsionFullLorentzFreshCoherentActual.matter
          point) =
      matterCoordinateEquiv
          (PreContorsionFullLorentzTriangularCurrent.matter
            (canonicalSpatialProjection point)) +
        canonicalTimeProjection point •
          matterCoordinateEquiv
            (actionGeneratedMatterRawTimeVelocity
              PreContorsionFullLorentzTriangularCurrent
              (canonicalSpatialProjection point)) +
        scalarQuadraticTimeCoefficient
            (canonicalCauchySlicePoint
              (canonicalTimeProjection point) 0) •
          preContorsionFullLorentzCoherentMatterQuadraticResponse
            (canonicalSpatialProjection point) := by
  let space := canonicalSpatialProjection point
  let time := canonicalTimeProjection point
  let localPoint := canonicalCauchySlicePoint time 0
  change
    matterCoordinateEquiv
        ((currentCanonicalGravityPreservingActual
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent space).matter
            localPoint) =
      _
  unfold currentCanonicalGravityPreservingActual
    actionGeneratedMatterCompleteFirstGermActual
  rw [installMatterCompleteFirstGermResponse_matter_coordinate]
  unfold currentCanonicalGravityPreservingTemporalMatterActual
    actionGeneratedMatterTemporalFirstGermActual
  rw [installMatterTemporalFirstGermResponse_matter_coordinate]
  change
    matterCoordinateEquiv
        (actionGeneratedMatterLocalField
          PreContorsionFullLorentzTriangularCurrent space localPoint) +
      matterQuadraticTimeCoordinateCorrection
          (preContorsionFullLorentzCoherentTemporalAcceleration space)
          localPoint +
      matterCompleteQuadraticCoordinateCorrection
          (preContorsionFullLorentzCoherentCompleteHessian space)
          localPoint =
      _
  unfold actionGeneratedMatterLocalField actionGeneratedMatterLocalCoordinate
  rw [matterCoordinateEquiv.apply_symm_apply,
    actionGeneratedMatterLocalIncrement_timeLine,
    matterCompleteQuadraticCoordinateCorrection_timeLine]
  unfold matterQuadraticTimeCoordinateCorrection
    preContorsionFullLorentzCoherentMatterQuadraticResponse
  dsimp only [space, time, localPoint]
  module

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterNormalForm
