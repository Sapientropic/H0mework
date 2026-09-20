import H0mework.Physics.FinalJoint.FixedMatterAcceptance
import H0mework.Physics.GaugeAction.P286GaugeConnectionMomentumRegularity

/-!
# Fixed P506/L0 final common zero fiber

The source/action-owned common write has already generated one final actual.
This module completes its last matter readout at the fixed contact.  The
calculation transports the explicit identity/zero coframe first jet through
the point--coframe momentum factorization, then assembles all nine residual
coordinates into one zero fiber.

No residual coordinate, support branch, target derivative, equation receipt,
or zero-fiber witness is accepted by the common write.  The results here are
readback and producer-soundness of that already generated actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonMatterAcceptance
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterIdentityCoframeAcceptance
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineMatterPointwiseEquation
open StageNineP286GaugeConnectionMomentumRegularity

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private theorem coframe_fderiv_coordinate_zero_of_zeroFirstJet
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (zeroFirstJet :
      holonomicCoframeFirstJetAt configuration.coframe 0 =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet))
    (direction : LorentzianIndex) :
    (fderiv ℝ configuration.coframe 0)
        (coordinateDirection direction) = 0 := by
  have coframeDifferentiable : DifferentiableAt ℝ configuration.coframe 0 :=
    ((holonomicCoframe_contDiff configuration smooth).differentiable (by simp)
      ).differentiableAt
  ext internal coordinate
  let evaluation : LorentzianCoframe →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate :
        (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj internal :
        LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))
  have evaluatedDerivative :
      HasFDerivAt
        (fun point : BasePoint => evaluation (configuration.coframe point))
        (evaluation.comp (fderiv ℝ configuration.coframe 0)) 0 :=
    evaluation.hasFDerivAt.comp 0 coframeDifferentiable.hasFDerivAt
  have componentDerivativeZero :=
    congrArg
      (fun jet => jet.derivative direction internal coordinate)
      zeroFirstJet
  have evaluatedFunctionEquality :
      (fun point : BasePoint => evaluation (configuration.coframe point)) =
        (fun point : BasePoint =>
          configuration.coframe point internal coordinate) := by
    funext point
    rfl
  have evaluatedZero :
      (fderiv ℝ
          (fun point : BasePoint => evaluation (configuration.coframe point)) 0)
          (coordinateDirection direction) = 0 := by
    rw [evaluatedFunctionEquality]
    simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative] using
      componentDerivativeZero
  rw [evaluatedDerivative.fderiv] at evaluatedZero
  change
    evaluation
        ((fderiv ℝ configuration.coframe 0)
          (coordinateDirection direction)) = 0 at evaluatedZero
  exact evaluatedZero

private theorem fderiv_pointCoframe_eq_frozen_of_zero_local
    (outer : BasePoint × LorentzianCoframe → ℝ)
    (outerDifferentiable : DifferentiableAt ℝ outer (0, 1))
    (coframe : BasePoint → LorentzianCoframe)
    (coframeOrigin : coframe 0 = 1)
    (coframeDifferentiable : DifferentiableAt ℝ coframe 0)
    (direction : LorentzianIndex)
    (coframeDerivativeZero :
      (fderiv ℝ coframe 0) (coordinateDirection direction) = 0) :
    (fderiv ℝ
        (outer ∘ fun point => (point, coframe point)) 0)
        (coordinateDirection direction) =
      (fderiv ℝ
        (outer ∘ fun point => (point, (1 : LorentzianCoframe))) 0)
        (coordinateDirection direction) := by
  have actualInner :
      HasFDerivAt (fun point : BasePoint => (point, coframe point))
        ((ContinuousLinearMap.id ℝ BasePoint).prod
          (fderiv ℝ coframe 0)) 0 :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
      coframeDifferentiable.hasFDerivAt
  have frozenInner :
      HasFDerivAt
        (fun point : BasePoint => (point, (1 : LorentzianCoframe)))
        ((ContinuousLinearMap.id ℝ BasePoint).prod
          (0 : BasePoint →L[ℝ] LorentzianCoframe)) 0 :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
      (hasFDerivAt_const (x := (0 : BasePoint))
        (c := (1 : LorentzianCoframe)))
  have outerAtActual : DifferentiableAt ℝ outer (0, coframe 0) := by
    simpa only [coframeOrigin] using outerDifferentiable
  have actualComposition := outerAtActual.hasFDerivAt.comp 0 actualInner
  have frozenComposition := outerDifferentiable.hasFDerivAt.comp 0 frozenInner
  rw [actualComposition.fderiv, frozenComposition.fderiv]
  rw [coframeOrigin]
  change
    (fderiv ℝ outer (0, 1))
        (coordinateDirection direction,
          (fderiv ℝ coframe 0) (coordinateDirection direction)) =
      (fderiv ℝ outer (0, 1))
        (coordinateDirection direction, 0)
  rw [coframeDerivativeZero]

private theorem
    matterMomentumDerivative_origin_eq_identityComparison_of_smooth_zeroFirstJet
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (zeroFirstJet :
      holonomicCoframeFirstJetAt configuration.coframe 0 =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet))
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum source configuration direction
          derivativeDirection) 0 derivativeDirection =
      fieldDirectionalDerivative
        (matterDifferentialMomentum source
          (identityCoframeComparison configuration) direction
          derivativeDirection) 0 derivativeDirection := by
  let outer :=
    matterDifferentialMomentumPointCoframe source configuration
      direction derivativeDirection
  have actualEq :
      matterDifferentialMomentum source configuration direction
          derivativeDirection =
        outer ∘ fun point => (point, configuration.coframe point) := by
    simpa only [outer] using
      matterDifferentialMomentum_eq_pointCoframe_actualSection
        source configuration direction derivativeDirection
  have frozenEq :
      matterDifferentialMomentum source
          (identityCoframeComparison configuration) direction
          derivativeDirection =
        outer ∘ fun point => (point, (1 : LorentzianCoframe)) := by
    calc
      _ = matterDifferentialMomentumPointCoframe source
            (identityCoframeComparison configuration) direction
              derivativeDirection ∘
          fun point =>
            (point,
              (identityCoframeComparison configuration).coframe point) :=
        matterDifferentialMomentum_eq_pointCoframe_actualSection _ _ _ _
      _ = _ := by
        rw [matterDifferentialMomentumPointCoframe_identityCoframeComparison]
        rfl
  have coframeOrigin : configuration.coframe 0 = 1 :=
    congrArg PointwiseLorentzianCoframeJet.coframe zeroFirstJet
  have coframeDifferentiable : DifferentiableAt ℝ configuration.coframe 0 :=
    ((holonomicCoframe_contDiff configuration smooth).differentiable (by simp)
      ).differentiableAt
  have outerDifferentiable : DifferentiableAt ℝ outer (0, 1) := by
    exact
      (matterDifferentialMomentumPointCoframe_contDiffAt source configuration
        smooth 0 1 (by norm_num) direction derivativeDirection).differentiableAt
        (by simp)
  unfold fieldDirectionalDerivative
  rw [actualEq, frozenEq]
  exact
    fderiv_pointCoframe_eq_frozen_of_zero_local outer outerDifferentiable
      configuration.coframe coframeOrigin coframeDifferentiable
      derivativeDirection
      (coframe_fderiv_coordinate_zero_of_zeroFirstJet configuration smooth
        zeroFirstJet derivativeDirection)

theorem
    fixedP506L0FinalCommonMatterMomentumDivergence_origin_eq_identityComparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterSmoothComparison space) direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterIdentityCoframeComparison space)
        direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    matterMomentumDerivative_origin_eq_identityComparison_of_smooth_zeroFirstJet
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonMatterSmoothComparison space)
      (fixedP506L0FinalCommonMatterSmoothComparison_smooth space)
      (fixedP506L0FinalCommonMatterSmoothComparison_coframeFirstJet_origin
        space)
      direction derivativeDirection

theorem
    fixedP506L0FinalCommonMatterAlgebraic_origin_eq_identityComparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterSmoothComparison space) direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterIdentityCoframeComparison space)
        direction 0 := by
  have comparisonCoframeOne :
      (fixedP506L0FinalCommonMatterSmoothComparison space).coframe 0 = 1 :=
    congrArg PointwiseLorentzianCoframeJet.coframe
      (fixedP506L0FinalCommonMatterSmoothComparison_coframeFirstJet_origin
        space)
  rw [
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonMatterSmoothComparison space) direction 0
      comparisonCoframeOne,
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonMatterIdentityCoframeComparison space) direction 0
      (by rfl)]
  rfl

theorem fixedP506L0FinalCommonMatterSmoothComparison_matterEuler_origin_zero
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterSmoothComparison space) direction 0 =
      0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [fixedP506L0FinalCommonMatterAlgebraic_origin_eq_identityComparison,
    fixedP506L0FinalCommonMatterMomentumDivergence_origin_eq_identityComparison]
  exact
    fixedP506L0FinalCommonMatterIdentityCoframeComparison_matterEuler_zero
      space direction

private theorem fixedP506L0FinalCommonActionActual_matterMomentum_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction
          derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterSmoothComparison space) direction
          derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [fixedP506L0FinalCommonMatterSmoothComparison_coframe_eq_final,
    fixedP506L0FinalCommonMatterSmoothComparison_conjugateMatter_eq_final]

private theorem
    fixedP506L0FinalCommonActionActual_matterMomentumDivergence_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterSmoothComparison space) direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [fixedP506L0FinalCommonActionActual_matterMomentum_eq_comparison]

private theorem
    fixedP506L0FinalCommonActionActual_matterAlgebraic_origin_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterSmoothComparison space) direction 0 := by
  have comparisonCoframeOne :
      (fixedP506L0FinalCommonMatterSmoothComparison space).coframe 0 = 1 := by
    rw [fixedP506L0FinalCommonMatterSmoothComparison_coframe_eq_final]
    exact fixedP506L0FinalCommonActionActual_coframe_origin space
  rw [
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonActionActual space) direction 0
      (fixedP506L0FinalCommonActionActual_coframe_origin space),
    holonomicDiracDualIdentityCoframeMatterAlgebraicCoefficient_of_coframe_eq_one
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonMatterSmoothComparison space) direction 0
      comparisonCoframeOne]
  rw [← fixedP506L0FinalCommonMatterSmoothComparison_conjugateMatter_eq_final,
    ← fixedP506L0FinalCommonMatterSmoothComparison_algebraicOperator_origin_eq_final]

theorem fixedP506L0FinalCommonActionActual_matterEuler_origin_zero
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction 0 = 0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [fixedP506L0FinalCommonActionActual_matterAlgebraic_origin_eq_comparison,
    fixedP506L0FinalCommonActionActual_matterMomentumDivergence_eq_comparison]
  exact
    fixedP506L0FinalCommonMatterSmoothComparison_matterEuler_origin_zero
      space direction

theorem fixedP506L0FinalCommonActionResidual_matter_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).matter = 0 := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction 0 = 0
  exact fixedP506L0FinalCommonActionActual_matterEuler_origin_zero
    space direction

/-- The source/action-generated final common actual lies in the complete
nine-channel zero fiber at its fixed contact. -/
theorem fixedP506L0FinalCommonActionResidual_zero
    (space : StageNineSpatialPoint) :
    fixedP506L0FinalCommonActionResidual space = 0 := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact fixedP506L0FinalCommonActionResidual_gravityMultiplier_zero space
  · exact fixedP506L0FinalCommonActionResidual_gravityAuxiliary_zero space
  · exact fixedP506L0FinalCommonActionResidual_p286GaugeAuxiliary_zero space
  · exact fixedP506L0FinalCommonActionResidual_lorentzConnection_zero space
  · exact fixedP506L0FinalCommonActionResidual_p286GaugeConnection_zero space
  · exact fixedP506L0FinalCommonActionResidual_scalar_zero space
  · exact fixedP506L0FinalCommonActionResidual_matter_zero space
  · exact fixedP506L0FinalCommonActionResidual_conjugateMatter_zero space
  · exact fixedP506L0FinalCommonActionResidual_coframe_zero space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber
