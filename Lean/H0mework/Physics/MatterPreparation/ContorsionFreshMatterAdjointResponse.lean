import H0mework.Physics.MatterPreparation.ContorsionSpatialProfileFullLorentzCurrentResponseRestart

/-!
# S9-C3h201c: corrected-current local matter/adjoint response

C3h200p already generated a complete local actual from the corrected final
Lorentz current.  This module consumes that producer in the matter sectors:

```text
corrected final current
→ complete contact response and local actual
→ actual primal and adjoint time jets
→ branch-free action laws
→ Dirac and adjoint acceptance on that same local actual.
```

The comparison actual below is proof-only.  It exposes the independently
generated dual germ already contained in the final actual; it is never used
as the producer output.  Every outer installer changes only fields outside
the adjoint momentum, while the linear-Plebanski connection has the same
contact value consumed by the algebraic matter operator.

Both final equation equalities are producer-soundness checks.  The positive
content is the corrected-current provenance, faithful local actualization,
and unique primal/adjoint response.  No residual, target field, coefficient,
branch, endpoint receipt, or source slot is accepted.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshMatterAdjointResponse

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionLorentzContactResponse
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionLorentzStateResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTimeVelocity
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

private abbrev preContorsionFullLorentzFreshMatterComparisonActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedMatterDualLocalActualLift
    positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent 0

private abbrev preContorsionFullLorentzFreshLinearBase :
    StageNineHolonomicConfiguration :=
  currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
    PreContorsionFullLorentzTriangularCurrent 0

private abbrev preContorsionFullLorentzFreshP286Actual :
    StageNineHolonomicConfiguration :=
  currentCanonicalGravityPreservingP286Actual positiveSmoothUnifiedSource
    PreContorsionFullLorentzTriangularCurrent 0

private abbrev preContorsionFullLorentzFreshTemporalMatterActual :
    StageNineHolonomicConfiguration :=
  currentCanonicalGravityPreservingTemporalMatterActual
    positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent 0

private abbrev preContorsionFullLorentzFreshCompleteMatterActual :
    StageNineHolonomicConfiguration :=
  currentCanonicalGravityPreservingActual positiveSmoothUnifiedSource
    PreContorsionFullLorentzTriangularCurrent 0

/-! ## Generated response and actual time jets -/

theorem preContorsionFullLorentzFreshActual_primalResponse :
    IdentityCoframeMatterTimeActionLaw
      PreContorsionFullLorentzTriangularCurrent 0
      (currentCanonicalFullActionLorentzStateMatterCovariantResponse
        PreContorsionFullLorentzTriangularCurrent 0) :=
  preContorsionFullLorentzTriangularCurrent_contactResponse.primalResponse

theorem preContorsionFullLorentzFreshActual_primalUnique
    (candidate : DiracExteriorMatterCarrier)
    (candidateLaw :
      IdentityCoframeMatterTimeActionLaw
        PreContorsionFullLorentzTriangularCurrent 0 candidate) :
    candidate =
      currentCanonicalFullActionLorentzStateMatterCovariantResponse
        PreContorsionFullLorentzTriangularCurrent 0 :=
  preContorsionFullLorentzTriangularCurrent_contactResponse.primalUnique
    candidate candidateLaw

theorem preContorsionFullLorentzFreshActual_matterTimeJet :
    deriv
        (fun time : Real =>
          matterCoordinateEquiv
            ((positiveP506MatterPreContorsionFullLorentzCurrentRestart
              time).matter 0))
        0 =
      positiveP506MatterPreContorsionFullLorentzFreshResponse.matter :=
  preContorsionFullLorentzTriangularCurrent_contactResponse.matterTimeJet

theorem preContorsionFullLorentzFreshActual_adjointResponse :
    IdentityCoframeConjugateMatterTimeActionLaw
      PreContorsionFullLorentzTriangularCurrent 0
      (currentCanonicalFullActionLorentzStateAdjointResponse
        PreContorsionFullLorentzTriangularCurrent 0) :=
  preContorsionFullLorentzTriangularCurrent_contactResponse.adjointResponse

theorem preContorsionFullLorentzFreshActual_adjointUnique
    (candidate : Module.Dual Complex DiracExteriorMatterCarrier)
    (candidateLaw :
      IdentityCoframeConjugateMatterTimeActionLaw
        PreContorsionFullLorentzTriangularCurrent 0 candidate) :
    candidate =
      currentCanonicalFullActionLorentzStateAdjointResponse
        PreContorsionFullLorentzTriangularCurrent 0 :=
  preContorsionFullLorentzTriangularCurrent_contactResponse.adjointUnique
    candidate candidateLaw

theorem preContorsionFullLorentzFreshActual_conjugateMatterTimeJet
    (matter : DiracExteriorMatterCarrier) :
    deriv
        (fun time : Real =>
          (positiveP506MatterPreContorsionFullLorentzCurrentRestart
            time).conjugateMatter 0 matter)
        0 =
      positiveP506MatterPreContorsionFullLorentzFreshResponse.conjugateMatter
        matter :=
  preContorsionFullLorentzTriangularCurrent_contactResponse
    |>.conjugateMatterTimeJet matter

/-! ## Local primal acceptance -/

private theorem preContorsionFullLorentzFreshLinearBase_coframe_eq_comparison :
    preContorsionFullLorentzFreshLinearBase.coframe =
      preContorsionFullLorentzFreshMatterComparisonActual.coframe :=
  rfl

private theorem preContorsionFullLorentzFreshLinearBase_matter_eq_comparison :
    preContorsionFullLorentzFreshLinearBase.matter =
      preContorsionFullLorentzFreshMatterComparisonActual.matter :=
  rfl

private theorem
    preContorsionFullLorentzFreshLinearBase_gravityConnection_origin_eq_comparison :
    preContorsionFullLorentzFreshLinearBase.gravityConnection 0 =
    preContorsionFullLorentzFreshMatterComparisonActual.gravityConnection
        0 := by
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).gravityConnection 0 =
    (sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).gravityConnection 0
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_initialConnection]
  exact
    (sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).symm

private theorem
    preContorsionFullLorentzFreshLinearBase_gaugeConnection_eq_comparison :
    preContorsionFullLorentzFreshLinearBase.gaugeConnection =
      preContorsionFullLorentzFreshMatterComparisonActual.gaugeConnection :=
  rfl

private theorem
    preContorsionFullLorentzFreshLinearBase_scalar_origin_eq_comparison :
    preContorsionFullLorentzFreshLinearBase.scalar 0 =
      preContorsionFullLorentzFreshMatterComparisonActual.scalar 0 := by
  change
    (sourceActionGeneratedJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).scalar 0 =
    (sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).scalar 0
  rw [sourceActionGeneratedJointLocalActualLift_initialScalar]
  exact
    (sourceGeneratedP286ActionLocalActualLift_scalar_origin
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).symm

private theorem
    preContorsionFullLorentzFreshLinearBase_matterCovariantDerivative_eq_comparison :
    holonomicMatterCovariantDerivative
        preContorsionFullLorentzFreshLinearBase 0 =
      holonomicMatterCovariantDerivative
        preContorsionFullLorentzFreshMatterComparisonActual 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [preContorsionFullLorentzFreshLinearBase_matter_eq_comparison,
    preContorsionFullLorentzFreshLinearBase_gravityConnection_origin_eq_comparison,
    preContorsionFullLorentzFreshLinearBase_gaugeConnection_eq_comparison]

private theorem preContorsionFullLorentzFreshLinearBase_diracYukawa_origin :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField preContorsionFullLorentzFreshLinearBase 0) =
      0 := by
  have vectorEquality :
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (toContinuumPointField preContorsionFullLorentzFreshLinearBase 0) =
        generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            preContorsionFullLorentzFreshMatterComparisonActual 0) := by
    unfold generatedContinuumMatterVector toContinuumPointField
    rw [preContorsionFullLorentzFreshLinearBase_coframe_eq_comparison,
      preContorsionFullLorentzFreshLinearBase_matter_eq_comparison,
      preContorsionFullLorentzFreshLinearBase_scalar_origin_eq_comparison,
      preContorsionFullLorentzFreshLinearBase_matterCovariantDerivative_eq_comparison]
  rw [vectorEquality]
  exact
    sourceActionGeneratedMatterDualLocalActualLift_diracYukawa_origin
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0 preContorsionFullLorentzTriangularCurrent_coframe_origin

private theorem preContorsionFullLorentzFreshLinearBase_smooth :
    preContorsionFullLorentzFreshLinearBase.Smooth :=
  sourceActionGeneratedLinearPlebanskiJointLocalActualLift_smooth
    positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent 0

private theorem preContorsionFullLorentzFreshP286Actual_smooth :
    preContorsionFullLorentzFreshP286Actual.Smooth :=
  currentP286CompleteActionResponseOperator_smooth
    positiveSmoothUnifiedSource preContorsionFullLorentzFreshLinearBase
    preContorsionFullLorentzFreshLinearBase_smooth

private theorem preContorsionFullLorentzFreshTemporalMatterActual_smooth :
    preContorsionFullLorentzFreshTemporalMatterActual.Smooth :=
  actionGeneratedMatterTemporalFirstGermActual_smooth
    positiveSmoothUnifiedSource preContorsionFullLorentzFreshP286Actual
    preContorsionFullLorentzFreshP286Actual_smooth

private theorem
    preContorsionFullLorentzFreshActual_diracYukawa_eq_complete :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterPreContorsionFullLorentzFreshActual 0) =
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          preContorsionFullLorentzFreshCompleteMatterActual 0) := by
  rcases
      currentCanonicalFullActionLorentzActualFirstJetLift_retainsPrimitiveFields
        positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
        0 with
    ⟨coframeEq, gravityConnectionEq, _multiplierEq, gaugeConnectionEq,
      _gaugeAuxiliaryEq, scalarEq, matterEq, _conjugateMatterEq⟩
  have matterCovariantDerivativeEq :
      holonomicMatterCovariantDerivative
          positiveP506MatterPreContorsionFullLorentzFreshActual 0 =
        holonomicMatterCovariantDerivative
          preContorsionFullLorentzFreshCompleteMatterActual 0 := by
    funext direction
    unfold holonomicMatterCovariantDerivative
    rw [matterEq, gravityConnectionEq, gaugeConnectionEq]
  unfold generatedContinuumMatterVector toContinuumPointField
  rw [coframeEq, matterEq, scalarEq, matterCovariantDerivativeEq]

private theorem
    preContorsionFullLorentzFreshCompleteMatterActual_diracYukawa_eq_temporal :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          preContorsionFullLorentzFreshCompleteMatterActual 0) =
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          preContorsionFullLorentzFreshTemporalMatterActual 0) :=
  actionGeneratedMatterCompleteFirstGermActual_diracYukawa_origin
    positiveSmoothUnifiedSource
    preContorsionFullLorentzFreshTemporalMatterActual
    preContorsionFullLorentzFreshTemporalMatterActual_smooth

private theorem
    preContorsionFullLorentzFreshTemporalMatterActual_diracYukawa_eq_p286 :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          preContorsionFullLorentzFreshTemporalMatterActual 0) =
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField preContorsionFullLorentzFreshP286Actual 0) :=
  actionGeneratedMatterTemporalFirstGermActual_diracYukawa_origin
    positiveSmoothUnifiedSource preContorsionFullLorentzFreshP286Actual
    preContorsionFullLorentzFreshP286Actual_smooth

private theorem
    preContorsionFullLorentzFreshP286Actual_diracYukawa_eq_linearBase :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField preContorsionFullLorentzFreshP286Actual 0) =
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField preContorsionFullLorentzFreshLinearBase 0) := by
  have coframeEq :
      preContorsionFullLorentzFreshP286Actual.coframe =
        preContorsionFullLorentzFreshLinearBase.coframe :=
    currentP286CompleteActionResponseOperator_coframe
      positiveSmoothUnifiedSource preContorsionFullLorentzFreshLinearBase
  have gravityConnectionEq :
      preContorsionFullLorentzFreshP286Actual.gravityConnection =
        preContorsionFullLorentzFreshLinearBase.gravityConnection :=
    currentP286CompleteActionResponseOperator_gravityConnection
      positiveSmoothUnifiedSource preContorsionFullLorentzFreshLinearBase
  have gaugeConnectionEq :
      preContorsionFullLorentzFreshP286Actual.gaugeConnection =
        preContorsionFullLorentzFreshLinearBase.gaugeConnection :=
    currentP286CompleteActionResponseOperator_gaugeConnection
      positiveSmoothUnifiedSource preContorsionFullLorentzFreshLinearBase
  have scalarEq :
      preContorsionFullLorentzFreshP286Actual.scalar =
        preContorsionFullLorentzFreshLinearBase.scalar :=
    currentP286CompleteActionResponseOperator_scalar
      positiveSmoothUnifiedSource preContorsionFullLorentzFreshLinearBase
  have matterEq :
      preContorsionFullLorentzFreshP286Actual.matter =
        preContorsionFullLorentzFreshLinearBase.matter :=
    currentP286CompleteActionResponseOperator_matter
      positiveSmoothUnifiedSource preContorsionFullLorentzFreshLinearBase
  have matterCovariantDerivativeEq :
      holonomicMatterCovariantDerivative
          preContorsionFullLorentzFreshP286Actual 0 =
        holonomicMatterCovariantDerivative
          preContorsionFullLorentzFreshLinearBase 0 := by
    funext direction
    unfold holonomicMatterCovariantDerivative
    rw [matterEq, gravityConnectionEq, gaugeConnectionEq]
  unfold generatedContinuumMatterVector toContinuumPointField
  rw [coframeEq, matterEq, scalarEq, matterCovariantDerivativeEq]

/-- The corrected-current local actual satisfies the primal equation.  This
is substitution into the action equation that generated its matter response,
so it remains producer consistency. -/
theorem preContorsionFullLorentzFreshActual_diracYukawa_origin :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterPreContorsionFullLorentzFreshActual 0) =
      0 := by
  rw [preContorsionFullLorentzFreshActual_diracYukawa_eq_complete,
    preContorsionFullLorentzFreshCompleteMatterActual_diracYukawa_eq_temporal,
    preContorsionFullLorentzFreshTemporalMatterActual_diracYukawa_eq_p286,
    preContorsionFullLorentzFreshP286Actual_diracYukawa_eq_linearBase]
  exact preContorsionFullLorentzFreshLinearBase_diracYukawa_origin

/-! ## Local adjoint transport -/

private theorem preContorsionFullLorentzFreshActual_coframe_eq_comparison :
    positiveP506MatterPreContorsionFullLorentzFreshActual.coframe =
      preContorsionFullLorentzFreshMatterComparisonActual.coframe :=
  rfl

private theorem
    preContorsionFullLorentzFreshActual_conjugateMatter_eq_comparison :
    positiveP506MatterPreContorsionFullLorentzFreshActual.conjugateMatter =
      preContorsionFullLorentzFreshMatterComparisonActual.conjugateMatter :=
  rfl

private theorem
    preContorsionFullLorentzFreshActual_gravityConnection_origin_eq_comparison :
    positiveP506MatterPreContorsionFullLorentzFreshActual.gravityConnection 0 =
      preContorsionFullLorentzFreshMatterComparisonActual.gravityConnection
        0 := by
  change
    (currentCanonicalGravityPreservingActual
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).gravityConnection 0 =
    (sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).gravityConnection 0
  rw [currentCanonicalGravityPreservingActual_gravityConnection_origin]
  exact
    (sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).symm

private theorem
    preContorsionFullLorentzFreshActual_gaugeConnection_eq_comparison :
    positiveP506MatterPreContorsionFullLorentzFreshActual.gaugeConnection =
      preContorsionFullLorentzFreshMatterComparisonActual.gaugeConnection :=
  rfl

private theorem
    preContorsionFullLorentzFreshActual_scalar_origin_eq_comparison :
    positiveP506MatterPreContorsionFullLorentzFreshActual.scalar 0 =
      preContorsionFullLorentzFreshMatterComparisonActual.scalar 0 :=
  preContorsionFullLorentzFreshLinearBase_scalar_origin_eq_comparison

private theorem preContorsionFullLorentzFreshActual_matterMomentum_eq_comparison
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual direction
        derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource
        preContorsionFullLorentzFreshMatterComparisonActual direction
        derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [preContorsionFullLorentzFreshActual_coframe_eq_comparison,
    preContorsionFullLorentzFreshActual_conjugateMatter_eq_comparison]

private theorem
    preContorsionFullLorentzFreshActual_matterMomentumDivergence_eq_comparison
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        preContorsionFullLorentzFreshMatterComparisonActual direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [preContorsionFullLorentzFreshActual_matterMomentum_eq_comparison]

private theorem
    preContorsionFullLorentzFreshActual_matterAlgebraic_eq_comparison
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual direction 0 =
      matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        preContorsionFullLorentzFreshMatterComparisonActual direction 0 := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection
          positiveP506MatterPreContorsionFullLorentzFreshActual direction 0 =
        holonomicMatterVariationAlgebraicDirection
          preContorsionFullLorentzFreshMatterComparisonActual direction 0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [
      preContorsionFullLorentzFreshActual_gravityConnection_origin_eq_comparison,
      preContorsionFullLorentzFreshActual_gaugeConnection_eq_comparison]
  have vectorEquality :
      matterAlgebraicVariationVector positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshActual direction 0 =
        matterAlgebraicVariationVector positiveSmoothUnifiedSource
          preContorsionFullLorentzFreshMatterComparisonActual direction 0 := by
    unfold matterAlgebraicVariationVector matterFieldVariationVector
    rw [matterGaugeKineticSum_zeroChart, matterGaugeKineticSum_zeroChart]
    simp only [toContinuumPointField]
    rw [preContorsionFullLorentzFreshActual_coframe_eq_comparison,
      preContorsionFullLorentzFreshActual_scalar_origin_eq_comparison,
      variationEquality]
  unfold matterAlgebraicDirectionalCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [vectorEquality,
    preContorsionFullLorentzFreshActual_coframe_eq_comparison,
    preContorsionFullLorentzFreshActual_conjugateMatter_eq_comparison]

/-- The same corrected-current local actual satisfies the adjoint equation.
This is producer consistency of the independently generated dual germ. -/
theorem preContorsionFullLorentzFreshActual_matterEuler_origin
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterPreContorsionFullLorentzFreshActual direction 0 =
      0 := by
  unfold matterEulerLagrangeDirectionalCoefficient
  rw [preContorsionFullLorentzFreshActual_matterAlgebraic_eq_comparison,
    preContorsionFullLorentzFreshActual_matterMomentumDivergence_eq_comparison]
  exact
    sourceActionGeneratedMatterDualLocalActualLift_matterEulerLagrange_origin
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0 preContorsionFullLorentzTriangularCurrent_coframe_origin direction

/-- Complete local same-actual matter checkpoint. -/
theorem preContorsionFullLorentzFreshActual_primalAdjoint_origin :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterPreContorsionFullLorentzFreshActual 0) =
      0 ∧
    ∀ direction : MatterCoordinateCarrier,
      matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          positiveP506MatterPreContorsionFullLorentzFreshActual direction 0 =
        0 :=
  ⟨preContorsionFullLorentzFreshActual_diracYukawa_origin,
    preContorsionFullLorentzFreshActual_matterEuler_origin⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshMatterAdjointResponse
