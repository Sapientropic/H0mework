import H0mework.Physics.CartanGeneration.SecondJetTrajectoryActualResponse
import H0mework.Physics.Dirac.GeneratedMatterSpinActionUpdate

/-!
# S9-C3h142: source/action-generated P506 matter current Cartan actual

C3h137 is generic in its primitive Cauchy seed.  The zero-matter restriction
of C3h139 came only from its positive specialization to
`positivePhaseProbeCauchyState`; it is not a restriction of the current
Cartan dynamics.

This module instead sends the C3h107 P506/L0 source-generated matter state
through the existing current action path:

```text
positive proof-free source
→ actual Stage-8 P506/L0 matter link
→ source-generated nonzero matter Cauchy seed
→ C3h135 whole-slice current trajectory
→ C3h137 current Cartan second-jet local actual U(T)
→ complete ten-field synchronized restart response.
```

The actual and response are generated before the matter-spin readout below.
No residual, endpoint decoder, inverse image, range witness, supplied actual,
or stationarity certificate enters the constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCartanActual

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageEightSourceGeneratedMatter
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzActionCanonicalPairUpdate
open StageNineMatterActionTimeVelocity
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanSecondJetLocalActualLift
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryActualResponse
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
open StageNineSourceActionGeneratedPrimitiveCanonicalSplitDevelopment
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineStateDependentCartanCoframeFirstJetLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Positive source/action trajectory and actual -/

def positiveP506MatterCurrentCartanTrajectoryState
    (trajectoryTime : ℝ) :
    StageNineCauchyState :=
  sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
    positiveSmoothUnifiedSource 0 trajectoryTime
    positiveSourceTargetMatterCauchyState

def positiveP506MatterCurrentCartanTrajectoryActual
    (trajectoryTime : ℝ) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift
    positiveSmoothUnifiedSource 0 trajectoryTime
    positiveSourceTargetMatterCauchyState 0

/-- Frontier theorem: the P506/L0 source-generated matter state enters the
actual current Cartan dynamics and produces both the local second-jet actual
and its complete synchronized restart response. -/
theorem
    positiveP506MatterCurrentCartanTrajectoryActualResponse_realizes :
    SourceActionGeneratedCurrentCartanSecondJetTrajectoryActualResponseLaw
      positiveSmoothUnifiedSource 0
      positiveSourceTargetMatterCauchyState :=
  sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryActualResponse_realizes
    positiveSmoothUnifiedSource 0 positiveSourceTargetMatterCauchyState

@[simp] theorem positiveP506MatterCurrentCartanTrajectoryState_zero :
    positiveP506MatterCurrentCartanTrajectoryState 0 =
      sourceActionGeneratedJointPrimitiveActionInitialState
        positiveSourceTargetMatterCauchyState := by
  unfold positiveP506MatterCurrentCartanTrajectoryState
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
  rw [
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyUpdate_zero]
  unfold sourceActionGeneratedCurrentPrimitiveCauchyState
    sourceActionGeneratedPrimitiveCanonicalCurrent
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate
  rw [sourceActionGeneratedJointPrimitiveCauchyUpdate_zero]

/-! ## Readout from the already generated initial actual -/

theorem positiveP506MatterCurrentCartanTrajectoryActual_coframe_origin :
    (positiveP506MatterCurrentCartanTrajectoryActual 0).coframe 0 = 1 := by
  change
    (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift
      positiveSmoothUnifiedSource 0 0
      positiveSourceTargetMatterCauchyState 0).coframe 0 =
        1
  have law :=
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift_realizes
      positiveSmoothUnifiedSource 0 0
      positiveSourceTargetMatterCauchyState 0
  rw [law.coframeInitial]
  rw [
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_currentIdentity]
  change
    (positiveP506MatterCurrentCartanTrajectoryState 0).coframe 0 = 1
  rw [positiveP506MatterCurrentCartanTrajectoryState_zero]
  simp [sourceActionGeneratedJointPrimitiveActionInitialState,
    positiveSourceTargetMatterCauchyState, sourceTargetMatterCauchyState,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

theorem positiveP506MatterCurrentCartanTrajectoryActual_matter_origin :
    (positiveP506MatterCurrentCartanTrajectoryActual 0).matter 0 =
      diracSpinTwoMatterProbe := by
  change
    (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift
      positiveSmoothUnifiedSource 0 0
      positiveSourceTargetMatterCauchyState 0).matter 0 =
        diracSpinTwoMatterProbe
  have retained :=
    (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift_realizes
      positiveSmoothUnifiedSource 0 0
      positiveSourceTargetMatterCauchyState 0).retainsActionFields
  unfold SourceActionCartanCoframeRetainedFields at retained
  rw [retained.2.2.2.2.2.1]
  rw [sourceActionGeneratedJointLocalActualLift_initialMatter]
  rw [
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_currentIdentity]
  change
    (positiveP506MatterCurrentCartanTrajectoryState 0).matter 0 =
      diracSpinTwoMatterProbe
  rw [positiveP506MatterCurrentCartanTrajectoryState_zero]
  simp [sourceActionGeneratedJointPrimitiveActionInitialState]

theorem positiveP506MatterCurrentCartanTrajectoryActual_matter_origin_nonzero :
    (positiveP506MatterCurrentCartanTrajectoryActual 0).matter 0 ≠ 0 := by
  rw [positiveP506MatterCurrentCartanTrajectoryActual_matter_origin]
  exact diracSpinTwoMatterProbe_nonzero

/-- The same generated actual retains the source-generated target dual at
the common contact. -/
theorem positiveP506MatterCurrentCartanTrajectoryActual_conjugate_origin :
    (positiveP506MatterCurrentCartanTrajectoryActual 0).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift
      positiveSmoothUnifiedSource 0 0
      positiveSourceTargetMatterCauchyState 0).conjugateMatter 0 =
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier)
  have retained :=
    (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift_realizes
      positiveSmoothUnifiedSource 0 0
      positiveSourceTargetMatterCauchyState 0).retainsActionFields
  unfold SourceActionCartanCoframeRetainedFields at retained
  rw [retained.2.2.2.2.2.2]
  rw [sourceActionGeneratedJointLocalActualLift_initialConjugateMatter]
  rw [
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_currentIdentity]
  change
    (positiveP506MatterCurrentCartanTrajectoryState 0).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [positiveP506MatterCurrentCartanTrajectoryState_zero]
  simp [sourceActionGeneratedJointPrimitiveActionInitialState]

/-- Interaction-sensitive readout of the actual generated above.  The
coframe, matter and dual origin values are conclusions, not producer
premises. -/
theorem positiveP506MatterCurrentCartanTrajectoryActual_matterSpin_eq_half :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentCartanTrajectoryActual 0)
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      1 / 2 := by
  exact
    spinProbeResponse_eq_half_of_origin
      (positiveP506MatterCurrentCartanTrajectoryActual 0)
      positiveP506MatterCurrentCartanTrajectoryActual_coframe_origin
      positiveP506MatterCurrentCartanTrajectoryActual_matter_origin
      positiveP506MatterCurrentCartanTrajectoryActual_conjugate_origin

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCartanActual
