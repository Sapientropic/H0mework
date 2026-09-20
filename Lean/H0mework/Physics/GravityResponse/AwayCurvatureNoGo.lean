import H0mework.Physics.GravityResponse.Regularity

/-!
# S9-C3h72c: away-origin no-go for the normalized-affine keep response

C3h70's normalized-affine connection realizes its internally forced curvature
at the canonical origin.  This diagnostic computes the same actual
`dω + ω∧ω` curvature at the source-selected time-axis point.  In the
`(02;01)` coordinate it is `-5/32`, while the pointwise forced endpoint is
`0`.  Hence the current normalized-affine candidate does not realize the
forced auxiliary graph at every point.

The terminal theorem is uniform in the retained input template: the
source-native eliminator overwrites every gravity field consumed by the
comparison.  This is a stable no-go for this explicit connection grammar, not
a proof that the whole gravity shell is empty and not authority for a new
field, carrier, source slot, coefficient, branch, or receipt.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseAwayCurvatureNoGo

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineGravityAlgebraicKeepEndpoint
open StageNineGravityAlgebraicKeepResponseGerm
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNinePositiveSourceNativeGravityCurvatureBridge
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

private def zeroCompletionTemplate : StageNineHolonomicConfiguration where
  coframe := 0
  gravityConnection := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeConnection := 0
  gaugeAuxiliary := 0
  scalar := 0
  matter := 0
  conjugateMatter := 0

private abbrev inputImage : StageNineHolonomicConfiguration :=
  positiveSourceNativeAlgebraicEliminationUpdate zeroCompletionTemplate

private abbrev responseImage : StageNineHolonomicConfiguration :=
  positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate inputImage

private abbrev responseOmega0 : PointwiseLorentzSpinConnection :=
  generatedLorentzConnectionAt positiveSmoothUnifiedSource 0

private abbrev responseTarget : PhysicalBivector :=
  gravityAlgebraicKeepResponseCurvatureTarget
    positiveSmoothUnifiedSource inputImage

def gravityKeepResponseTimeAxisPoint : BasePoint :=
  coordinateDirection (0 : LorentzianIndex)

private theorem normalizedAffineBivectorOneForm_directionalDerivative_at
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun candidate =>
          normalizedAffineBivectorOneForm omega0 target candidate
            formDirection internalPair)
        point derivativeDirection =
      ∑ spacetimePair : Fin 6,
        normalizedDerivativeBivector omega0 target internalPair spacetimePair *
          orientedLorentzBivectorBasisCoefficient spacetimePair
            derivativeDirection formDirection := by
  unfold fieldDirectionalDerivative normalizedAffineBivectorOneForm
  rw [(normalizedAffineBivectorComponentLinear omega0 target formDirection
    internalPair).hasFDerivAt.fderiv]
  fin_cases derivativeDirection <;> fin_cases formDirection <;>
    simp [normalizedAffineBivectorComponentLinear,
      coordinateDirection, baseCoordinate,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_four, Fin.sum_univ_six]

private theorem normalizedAffineBivectorOneForm_antisymmetrizedDerivative_at
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    fieldDirectionalDerivative
        (fun candidate =>
          normalizedAffineBivectorOneForm omega0 target candidate
            (pairSecond spacetimePair) internalPair)
        point (pairFirst spacetimePair) -
      fieldDirectionalDerivative
        (fun candidate =>
          normalizedAffineBivectorOneForm omega0 target candidate
            (pairFirst spacetimePair) internalPair)
        point (pairSecond spacetimePair) =
      target internalPair spacetimePair -
        originLorentzBracketCurvature omega0 internalPair spacetimePair := by
  rw [normalizedAffineBivectorOneForm_directionalDerivative_at,
    normalizedAffineBivectorOneForm_directionalDerivative_at]
  fin_cases spacetimePair <;>
    simp [normalizedDerivativeBivector,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six] <;>
    ring

private theorem normalizedAffineLorentzConnectionField_loweredDerivative_at
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (normalizedAffineConfiguration omega0 target) point
          derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      fieldDirectionalDerivative
        (fun candidate =>
          normalizedAffineBivectorOneForm omega0 target candidate
            formDirection internalPair)
        point derivativeDirection := by
  unfold gravityConnectionDerivative normalizedAffineConfiguration
    configurationOfLorentzConnection
    normalizedAffineLorentzConnectionField
  unfold fieldDirectionalDerivative normalizedAffineBivectorOneForm
  let component :=
    normalizedAffineBivectorComponentLinear omega0 target formDirection
      internalPair
  have componentDerivative :
      fderiv ℝ component point = component :=
    component.hasFDerivAt.fderiv
  fin_cases internalPair <;>
    simp [lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.sum_univ_six]

theorem holonomicGravityCurvature_normalizedAffineConfiguration_at
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (point : BasePoint) :
    holonomicGravityCurvature
        (normalizedAffineConfiguration omega0 target) point =
      target - originLorentzBracketCurvature omega0 +
        originLorentzBracketCurvature
          (normalizedAffineLorentzConnectionField omega0 target point) := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  have firstDerivative :=
    normalizedAffineLorentzConnectionField_loweredDerivative_at
      omega0 target point (pairFirst spacetimePair)
      (pairSecond spacetimePair) internalPair
  have secondDerivative :=
    normalizedAffineLorentzConnectionField_loweredDerivative_at
      omega0 target point (pairSecond spacetimePair)
      (pairFirst spacetimePair) internalPair
  have antisymmetrized :=
    normalizedAffineBivectorOneForm_antisymmetrizedDerivative_at
      omega0 target point internalPair spacetimePair
  change
    minkowskiInternalSign (pairFirst internalPair) *
      (gravityConnectionDerivative
          (normalizedAffineConfiguration omega0 target) point
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair) (pairSecond internalPair) -
        gravityConnectionDerivative
          (normalizedAffineConfiguration omega0 target) point
          (pairSecond spacetimePair) (pairFirst spacetimePair)
          (pairFirst internalPair) (pairSecond internalPair) +
        ∑ middle : LorentzianIndex,
          ((normalizedAffineConfiguration omega0 target).gravityConnection point
                (pairFirst spacetimePair) (pairFirst internalPair) middle *
              (normalizedAffineConfiguration omega0 target).gravityConnection point
                (pairSecond spacetimePair) middle (pairSecond internalPair) -
            (normalizedAffineConfiguration omega0 target).gravityConnection point
                (pairSecond spacetimePair) (pairFirst internalPair) middle *
              (normalizedAffineConfiguration omega0 target).gravityConnection point
                (pairFirst spacetimePair) middle (pairSecond internalPair))) = _
  calc
    _ =
      (minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative
            (normalizedAffineConfiguration omega0 target) point
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) -
        minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative
            (normalizedAffineConfiguration omega0 target) point
            (pairSecond spacetimePair) (pairFirst spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair)) +
        minkowskiInternalSign (pairFirst internalPair) *
          ∑ middle : LorentzianIndex,
            ((normalizedAffineConfiguration omega0 target).gravityConnection point
                  (pairFirst spacetimePair) (pairFirst internalPair) middle *
                (normalizedAffineConfiguration omega0 target).gravityConnection point
                  (pairSecond spacetimePair) middle (pairSecond internalPair) -
              (normalizedAffineConfiguration omega0 target).gravityConnection point
                  (pairSecond spacetimePair) (pairFirst internalPair) middle *
                (normalizedAffineConfiguration omega0 target).gravityConnection point
                  (pairFirst spacetimePair) middle (pairSecond internalPair)) := by
        ring
    _ =
      (fieldDirectionalDerivative
          (fun candidate =>
            normalizedAffineBivectorOneForm omega0 target candidate
              (pairSecond spacetimePair) internalPair)
          point (pairFirst spacetimePair) -
        fieldDirectionalDerivative
          (fun candidate =>
            normalizedAffineBivectorOneForm omega0 target candidate
              (pairFirst spacetimePair) internalPair)
          point (pairSecond spacetimePair)) +
        minkowskiInternalSign (pairFirst internalPair) *
          ∑ middle : LorentzianIndex,
            ((normalizedAffineConfiguration omega0 target).gravityConnection point
                  (pairFirst spacetimePair) (pairFirst internalPair) middle *
                (normalizedAffineConfiguration omega0 target).gravityConnection point
                  (pairSecond spacetimePair) middle (pairSecond internalPair) -
              (normalizedAffineConfiguration omega0 target).gravityConnection point
                  (pairSecond spacetimePair) (pairFirst internalPair) middle *
                (normalizedAffineConfiguration omega0 target).gravityConnection point
                  (pairFirst spacetimePair) middle (pairSecond internalPair)) := by
        rw [firstDerivative, secondDerivative]
    _ =
      (target internalPair spacetimePair -
          originLorentzBracketCurvature omega0 internalPair spacetimePair) +
        originLorentzBracketCurvature
          (normalizedAffineLorentzConnectionField omega0 target point)
            internalPair spacetimePair := by
        rw [antisymmetrized]
        rfl
    _ = _ := by rfl

private theorem inputImage_gravityConnectionDerivative_zero_one_zero_one_timeAxis :
    gravityConnectionDerivative inputImage gravityKeepResponseTimeAxisPoint 0 1 0 1 = 0 := by
  unfold gravityConnectionDerivative
  rw [show
    (fun candidate => inputImage.gravityConnection candidate 1 0 1) =
        (fun _ : BasePoint => (0 : ℝ)) by
      funext candidate
      change
        ((installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
            candidate 1 0 1) = 0
      exact sourceNativeGravityConnection_one_zero_one
        zeroCompletionTemplate candidate]
  simp

private theorem inputImage_gravityConnectionDerivative_one_zero_zero_one_timeAxis :
    gravityConnectionDerivative inputImage gravityKeepResponseTimeAxisPoint 1 0 0 1 = 0 := by
  unfold gravityConnectionDerivative
  rw [show
    (fun candidate => inputImage.gravityConnection candidate 0 0 1) =
        (fun _ : BasePoint => (0 : ℝ)) by
      funext candidate
      change
        ((installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
            candidate 0 0 1) = 0
      exact sourceNativeGravityConnection_zero_zero_one
        zeroCompletionTemplate candidate]
  simp

private theorem inputImage_gravityConnection_timeAxis_eq_origin :
    inputImage.gravityConnection gravityKeepResponseTimeAxisPoint =
      inputImage.gravityConnection 0 := by
  change
    generatedLorentzConnectionAt positiveSmoothUnifiedSource gravityKeepResponseTimeAxisPoint =
      generatedLorentzConnectionAt positiveSmoothUnifiedSource 0
  have coframeEquality :
      canonicalPhysicalSource.coframeAt gravityKeepResponseTimeAxisPoint =
        canonicalPhysicalSource.coframeAt 0 := by
    rw [canonicalPhysicalSource_coframeAt_eq_transvection,
      canonicalPhysicalSource_coframeAt_eq_transvection]
    simp [gravityKeepResponseTimeAxisPoint, coordinateDirection]
  have jetEquality :
      positiveSmoothUnifiedSource.legacy.jetAt gravityKeepResponseTimeAxisPoint =
        positiveSmoothUnifiedSource.legacy.jetAt 0 := by
    change canonicalPhysicalSource.jetAt gravityKeepResponseTimeAxisPoint =
      canonicalPhysicalSource.jetAt 0
    unfold ProofFreeRicherAnholonomicSource.Source.jetAt
    rw [coframeEquality]
  unfold generatedLorentzConnectionAt
  rw [jetEquality]

private theorem inputImage_curvature_zero_zero_timeAxis :
    holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint 0 0 =
      (1 / 4 : ℝ) := by
  unfold holonomicGravityCurvature
  dsimp only
  change
    minkowskiInternalSign 0 *
      (gravityConnectionDerivative inputImage gravityKeepResponseTimeAxisPoint 0 1 0 1 -
        gravityConnectionDerivative inputImage gravityKeepResponseTimeAxisPoint 1 0 0 1 +
        ∑ middle : LorentzianIndex,
          (inputImage.gravityConnection gravityKeepResponseTimeAxisPoint 0 0 middle *
              inputImage.gravityConnection gravityKeepResponseTimeAxisPoint 1 middle 1 -
            inputImage.gravityConnection gravityKeepResponseTimeAxisPoint 1 0 middle *
              inputImage.gravityConnection gravityKeepResponseTimeAxisPoint 0 middle 1)) =
      (1 / 4 : ℝ)
  rw [inputImage_gravityConnectionDerivative_zero_one_zero_one_timeAxis,
    inputImage_gravityConnectionDerivative_one_zero_zero_one_timeAxis]
  rw [inputImage_gravityConnection_timeAxis_eq_origin]
  have originCurvature :=
    installPositiveSourceNativeGravityKinematics_curvature_zero_zero
      zeroCompletionTemplate
  unfold holonomicGravityCurvature at originCurvature
  dsimp only at originCurvature
  change
    minkowskiInternalSign 0 *
      (gravityConnectionDerivative
          (installPositiveSourceNativeGravityKinematics zeroCompletionTemplate)
          0 0 1 0 1 -
        gravityConnectionDerivative
          (installPositiveSourceNativeGravityKinematics zeroCompletionTemplate)
          0 1 0 0 1 +
        ∑ middle : LorentzianIndex,
          ((installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
                0 0 0 middle *
              (installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
                0 1 middle 1 -
            (installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
                0 1 0 middle *
              (installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
                0 0 middle 1)) =
      (1 / 4 : ℝ) at originCurvature
  rw [sourceNativeGravityConnectionDerivative_zero_one_zero_one,
    sourceNativeGravityConnectionDerivative_one_zero_zero_one]
    at originCurvature
  change
    minkowskiInternalSign 0 *
      (0 - 0 +
        ∑ middle : LorentzianIndex,
          (inputImage.gravityConnection 0 0 0 middle *
              inputImage.gravityConnection 0 1 middle 1 -
            inputImage.gravityConnection 0 1 0 middle *
              inputImage.gravityConnection 0 0 middle 1)) =
      (1 / 4 : ℝ)
  change
    minkowskiInternalSign 0 *
      (0 - 0 +
        ∑ middle : LorentzianIndex,
          ((installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
                0 0 0 middle *
              (installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
                0 1 middle 1 -
            (installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
                0 1 0 middle *
              (installPositiveSourceNativeGravityKinematics zeroCompletionTemplate).gravityConnection
                0 0 middle 1)) =
      (1 / 4 : ℝ)
  exact originCurvature

private theorem inputImage_coframe_timeAxis_eq_one :
    inputImage.coframe gravityKeepResponseTimeAxisPoint = 1 := by
  change canonicalPhysicalSource.coframeAt gravityKeepResponseTimeAxisPoint = 1
  rw [canonicalPhysicalSource_coframeAt_eq_transvection]
  simp [gravityKeepResponseTimeAxisPoint, coordinateDirection]

private theorem forcedEndpoint_zero_zero_timeAxis :
    forcedGravityCurvatureKeepEndpoint
          positiveSmoothUnifiedSource.legacy.sigma
          (inputImage.coframe gravityKeepResponseTimeAxisPoint)
          (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint)
          (inputImage.gravityAuxiliary gravityKeepResponseTimeAxisPoint) 0 0 =
      (-3 / 8 : ℝ) := by
  have auxiliaryEquation :=
    positiveSourceNativeAlgebraicEliminationUpdate_gravityAuxiliaryEquation
      zeroCompletionTemplate gravityKeepResponseTimeAxisPoint
  change
    holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint =
      gravityInternalDualEquiv (inputImage.gravityAuxiliary gravityKeepResponseTimeAxisPoint)
      at auxiliaryEquation
  unfold forcedGravityCurvatureKeepEndpoint
    forcedGravityAuxiliaryKeepEndpoint
  simp only [map_add, map_smul, map_sub]
  rw [← auxiliaryEquation, inputImage_coframe_timeAxis_eq_one]
  change
    gravityInternalDualEquiv (physicalIIPlusBivector 1) 0 0 +
        (1 - positiveSmoothUnifiedSource.legacy.sigma) *
          (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint 0 0 -
            gravityInternalDualEquiv (physicalIIPlusBivector 1) 0 0) +
      (1 - positiveSmoothUnifiedSource.legacy.sigma) *
        (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint 0 0 -
          holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint 0 0) =
      (-3 / 8 : ℝ)
  rw [inputImage_curvature_zero_zero_timeAxis,
    positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  norm_num [gravityInternalDualEquiv, gravityInternalDualLinear,
    internalBivectorDual, lorentzianCoframeHodge,
    physicalIIPlusBivector_identity_component]

private theorem originBracket_one_zero :
    originLorentzBracketCurvature
        (generatedLorentzConnectionAt positiveSmoothUnifiedSource 0) 1 0 = 0 := by
  norm_num [originLorentzBracketCurvature, generatedLorentzConnectionAt,
    PointwiseLorentzianCoframeJet.lorentzSpinConnection,
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix,
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix,
    affineConnectionMatrix,
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix,
    PointwiseLorentzianCoframeJet.leviCivitaConnection,
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    PointwiseLorentzianCoframeJet.metric,
    StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource.legacy,
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource.forget,
    StageEightProofFreeSource.Source.toPhysicalSource,
    StageEightProofFreeSource.canonicalPhysicalSource,
    StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.shearCoefficient,
    lorentzianMetricOfCoframe_one_inv,
    minkowskiInternalMetric, minkowskiInternalSign, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four, Fin.sum_univ_succ,
    Matrix.diagonal_apply, Matrix.one_apply, pairFirst, pairSecond]; simp

private theorem inputImage_gravityConnection_one_zero_two (point : BasePoint) :
    inputImage.gravityConnection point 1 0 2 = (1 / 2 : ℝ) := by
  change (canonicalPhysicalSource.jetAt point).lorentzSpinConnection 1 0 2 =
    (1 / 2 : ℝ)
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe⁻¹ =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (-(point 2)) by
      exact canonicalSourceCoframe_inv point,
    canonicalSourceMetric_inv point,
    show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  simp [canonicalSourceMetricInverseCandidate,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    StageEightProofFreeSource.Source.toPhysicalSource,
    StageEightProofFreeSource.canonicalPhysicalSource,
    StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.shearCoefficient,
    minkowskiInternalMetric, minkowskiInternalSign, Matrix.mulVec,
    Matrix.mul_apply, Matrix.transvection, Matrix.single,
    Matrix.one_apply, dotProduct, Fin.sum_univ_succ,
    Matrix.diagonal_apply]
  ring

private theorem inputImage_gravityConnection_zero_zero_two (point : BasePoint) :
    inputImage.gravityConnection point 0 0 2 = 0 := by
  change (canonicalPhysicalSource.jetAt point).lorentzSpinConnection 0 0 2 = 0
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe⁻¹ =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (-(point 2)) by
      exact canonicalSourceCoframe_inv point,
    canonicalSourceMetric_inv point,
    show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  simp [canonicalSourceMetricInverseCandidate,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    StageEightProofFreeSource.Source.toPhysicalSource,
    StageEightProofFreeSource.canonicalPhysicalSource,
    StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.shearCoefficient,
    minkowskiInternalMetric, minkowskiInternalSign, Matrix.mulVec,
    Matrix.mul_apply, Matrix.transvection, Matrix.single,
    Matrix.one_apply, dotProduct, Fin.sum_univ_succ,
    Matrix.diagonal_apply]

private theorem inputImage_gravityConnectionDerivative_zero_one_zero_two_timeAxis :
    gravityConnectionDerivative inputImage gravityKeepResponseTimeAxisPoint 0 1 0 2 = 0 := by
  unfold gravityConnectionDerivative
  rw [show
    (fun candidate => inputImage.gravityConnection candidate 1 0 2) =
        (fun _ : BasePoint => (1 / 2 : ℝ)) by
      funext candidate
      exact inputImage_gravityConnection_one_zero_two candidate]
  simp

private theorem inputImage_gravityConnectionDerivative_one_zero_zero_two_timeAxis :
    gravityConnectionDerivative inputImage gravityKeepResponseTimeAxisPoint 1 0 0 2 = 0 := by
  unfold gravityConnectionDerivative
  rw [show
    (fun candidate => inputImage.gravityConnection candidate 0 0 2) =
        (fun _ : BasePoint => (0 : ℝ)) by
      funext candidate
      exact inputImage_gravityConnection_zero_zero_two candidate]
  simp

private theorem inputImage_curvature_one_zero_timeAxis :
    holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint 1 0 = 0 := by
  unfold holonomicGravityCurvature
  dsimp only
  change
    minkowskiInternalSign 0 *
      (gravityConnectionDerivative inputImage gravityKeepResponseTimeAxisPoint 0 1 0 2 -
        gravityConnectionDerivative inputImage gravityKeepResponseTimeAxisPoint 1 0 0 2 +
        ∑ middle : LorentzianIndex,
          (inputImage.gravityConnection gravityKeepResponseTimeAxisPoint 0 0 middle *
              inputImage.gravityConnection gravityKeepResponseTimeAxisPoint 1 middle 2 -
            inputImage.gravityConnection gravityKeepResponseTimeAxisPoint 1 0 middle *
              inputImage.gravityConnection gravityKeepResponseTimeAxisPoint 0 middle 2)) = 0
  rw [inputImage_gravityConnectionDerivative_zero_one_zero_two_timeAxis,
    inputImage_gravityConnectionDerivative_one_zero_zero_two_timeAxis,
    inputImage_gravityConnection_timeAxis_eq_origin]
  rw [show inputImage.gravityConnection =
    generatedLorentzConnectionAt positiveSmoothUnifiedSource by rfl]
  have bracket := originBracket_one_zero
  unfold originLorentzBracketCurvature at bracket
  norm_num [pairFirst, pairSecond, minkowskiInternalSign] at bracket ⊢
  exact bracket

private theorem inputImage_curvature_one_zero_origin :
    holonomicGravityCurvature inputImage 0 1 0 = 0 := by
  have firstDerivative :
      gravityConnectionDerivative inputImage 0 0 1 0 2 = 0 := by
    unfold gravityConnectionDerivative
    rw [show
      (fun candidate => inputImage.gravityConnection candidate 1 0 2) =
          (fun _ : BasePoint => (1 / 2 : ℝ)) by
        funext candidate
        exact inputImage_gravityConnection_one_zero_two candidate]
    simp
  have secondDerivative :
      gravityConnectionDerivative inputImage 0 1 0 0 2 = 0 := by
    unfold gravityConnectionDerivative
    rw [show
      (fun candidate => inputImage.gravityConnection candidate 0 0 2) =
          (fun _ : BasePoint => (0 : ℝ)) by
        funext candidate
        exact inputImage_gravityConnection_zero_zero_two candidate]
    simp
  unfold holonomicGravityCurvature
  dsimp only
  change
    minkowskiInternalSign 0 *
      (gravityConnectionDerivative inputImage 0 0 1 0 2 -
        gravityConnectionDerivative inputImage 0 1 0 0 2 +
        ∑ middle : LorentzianIndex,
          (inputImage.gravityConnection 0 0 0 middle *
              inputImage.gravityConnection 0 1 middle 2 -
            inputImage.gravityConnection 0 1 0 middle *
              inputImage.gravityConnection 0 0 middle 2)) = 0
  rw [firstDerivative, secondDerivative]
  rw [show inputImage.gravityConnection 0 = responseOmega0 by rfl]
  have bracket := originBracket_one_zero
  unfold originLorentzBracketCurvature at bracket
  norm_num [pairFirst, pairSecond, minkowskiInternalSign] at bracket ⊢
  exact bracket

private theorem forcedEndpoint_one_zero_timeAxis :
    forcedGravityCurvatureKeepEndpoint
          positiveSmoothUnifiedSource.legacy.sigma
          (inputImage.coframe gravityKeepResponseTimeAxisPoint)
          (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint)
          (inputImage.gravityAuxiliary gravityKeepResponseTimeAxisPoint) 1 0 = 0 := by
  have auxiliaryEquation :=
    positiveSourceNativeAlgebraicEliminationUpdate_gravityAuxiliaryEquation
      zeroCompletionTemplate gravityKeepResponseTimeAxisPoint
  change
    holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint =
      gravityInternalDualEquiv (inputImage.gravityAuxiliary gravityKeepResponseTimeAxisPoint)
      at auxiliaryEquation
  unfold forcedGravityCurvatureKeepEndpoint
    forcedGravityAuxiliaryKeepEndpoint
  simp only [map_add, map_smul, map_sub]
  rw [← auxiliaryEquation, inputImage_coframe_timeAxis_eq_one]
  change
    gravityInternalDualEquiv (physicalIIPlusBivector 1) 1 0 +
        (1 - positiveSmoothUnifiedSource.legacy.sigma) *
          (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint 1 0 -
            gravityInternalDualEquiv (physicalIIPlusBivector 1) 1 0) +
      (1 - positiveSmoothUnifiedSource.legacy.sigma) *
        (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint 1 0 -
          holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint 1 0) = 0
  rw [inputImage_curvature_one_zero_timeAxis,
    positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  norm_num [gravityInternalDualEquiv, gravityInternalDualLinear,
    internalBivectorDual, lorentzianCoframeHodge,
    physicalIIPlusBivector, coframeWedge, pairFirst, pairSecond,
    Matrix.one_apply]
  simp

private theorem responseTarget_zero_zero : responseTarget 0 0 = (-3 / 8 : ℝ) := by
  have realized := congrFun (congrFun
    (gravityAlgebraicKeepResponseUpdate_curvature_origin
      positiveSmoothUnifiedSource inputImage) 0) 0
  change holonomicGravityCurvature responseImage 0 0 0 =
    responseTarget 0 0 at realized
  rw [positiveSourceNativeGravityAlgebraicKeepResponse_curvature_zero_zero]
    at realized
  exact realized.symm

private theorem responseTarget_one_zero : responseTarget 1 0 = 0 := by
  have auxiliaryEquation :=
    positiveSourceNativeAlgebraicEliminationUpdate_gravityAuxiliaryEquation
      zeroCompletionTemplate 0
  change
    holonomicGravityCurvature inputImage 0 =
      gravityInternalDualEquiv (inputImage.gravityAuxiliary 0)
      at auxiliaryEquation
  unfold responseTarget gravityAlgebraicKeepResponseCurvatureTarget
    forcedGravityCurvatureKeepEndpoint forcedGravityAuxiliaryKeepEndpoint
  simp only [map_add, map_smul, map_sub]
  rw [← auxiliaryEquation]
  have inputCoframeOrigin : inputImage.coframe 0 =
      (1 : LorentzianCoframe) := by
    change canonicalPhysicalSource.coframeAt 0 = 1
    exact canonicalPhysicalSource.coframeAt_zero
  rw [inputCoframeOrigin]
  change
    gravityInternalDualEquiv (physicalIIPlusBivector 1) 1 0 +
        (1 - positiveSmoothUnifiedSource.legacy.sigma) *
          (holonomicGravityCurvature inputImage 0 1 0 -
            gravityInternalDualEquiv (physicalIIPlusBivector 1) 1 0) +
      (1 - positiveSmoothUnifiedSource.legacy.sigma) *
        (holonomicGravityCurvature inputImage 0 1 0 -
          holonomicGravityCurvature inputImage 0 1 0) = 0
  rw [inputImage_curvature_one_zero_origin,
    positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  norm_num [gravityInternalDualEquiv, gravityInternalDualLinear,
    internalBivectorDual, lorentzianCoframeHodge,
    physicalIIPlusBivector, coframeWedge, pairFirst, pairSecond,
    Matrix.one_apply]
  simp

private theorem responseBracket_one_zero_timeAxis :
    originLorentzBracketCurvature
        (normalizedAffineLorentzConnectionField
          responseOmega0 responseTarget gravityKeepResponseTimeAxisPoint) 1 0 =
      (-5 / 32 : ℝ) := by
  simp [originLorentzBracketCurvature,
    normalizedAffineLorentzConnectionField,
    normalizedAffineBivectorOneForm,
    normalizedAffineBivectorComponentLinear,
    normalizedDerivativeBivector,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    gravityKeepResponseTimeAxisPoint, baseCoordinate, coordinateDirection,
    responseOmega0, generatedLorentzConnectionAt,
    PointwiseLorentzianCoframeJet.lorentzSpinConnection,
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix,
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix,
    affineConnectionMatrix,
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix,
    PointwiseLorentzianCoframeJet.leviCivitaConnection,
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    PointwiseLorentzianCoframeJet.metric,
    StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ProofFreeRicherAnholonomicSource.Source.jetAt,
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource.legacy,
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource.forget,
    StageEightProofFreeSource.Source.toPhysicalSource,
    StageEightProofFreeSource.canonicalSource,
    ProofFreeRicherAnholonomicSource.shearCoefficient,
    lorentzianMetricOfCoframe_one_inv,
    minkowskiInternalMetric, minkowskiInternalSign,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.diagonal_apply, Matrix.one_apply,
    pairFirst, pairSecond,
    responseTarget_zero_zero, responseTarget_one_zero];
    ring

private theorem responseCurvature_one_zero_timeAxis :
    holonomicGravityCurvature responseImage gravityKeepResponseTimeAxisPoint 1 0 =
      (-5 / 32 : ℝ) := by
  change
    holonomicGravityCurvature
        (normalizedAffineConfiguration responseOmega0 responseTarget)
        gravityKeepResponseTimeAxisPoint 1 0 = (-5 / 32 : ℝ)
  rw [holonomicGravityCurvature_normalizedAffineConfiguration_at]
  change
    responseTarget 1 0 -
        originLorentzBracketCurvature responseOmega0 1 0 +
      originLorentzBracketCurvature
        (normalizedAffineLorentzConnectionField
          responseOmega0 responseTarget gravityKeepResponseTimeAxisPoint) 1 0 =
      (-5 / 32 : ℝ)
  rw [responseTarget_one_zero, originBracket_one_zero,
    responseBracket_one_zero_timeAxis]
  norm_num

private theorem responseCurvature_ne_forcedEndpoint_one_zero_timeAxis :
    holonomicGravityCurvature responseImage gravityKeepResponseTimeAxisPoint 1 0 ≠
      forcedGravityCurvatureKeepEndpoint
          positiveSmoothUnifiedSource.legacy.sigma
          (inputImage.coframe gravityKeepResponseTimeAxisPoint)
          (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint)
          (inputImage.gravityAuxiliary gravityKeepResponseTimeAxisPoint) 1 0 := by
  rw [responseCurvature_one_zero_timeAxis,
    forcedEndpoint_one_zero_timeAxis]
  norm_num

private theorem responseCurvature_ne_forcedEndpoint_timeAxis :
    holonomicGravityCurvature responseImage gravityKeepResponseTimeAxisPoint ≠
      forcedGravityCurvatureKeepEndpoint
        positiveSmoothUnifiedSource.legacy.sigma
        (inputImage.coframe gravityKeepResponseTimeAxisPoint)
        (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint)
        (inputImage.gravityAuxiliary gravityKeepResponseTimeAxisPoint) := by
  intro equality
  have coordinateEquality := congrFun (congrFun equality 1) 0
  exact responseCurvature_ne_forcedEndpoint_one_zero_timeAxis
    coordinateEquality

/-- The counterexample is independent of the retained multiplier, gauge,
scalar, and matter template fields: source-native elimination overwrites every
field consumed by this gravity comparison. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_ne_forcedEndpoint_timeAxis
    (configuration : StageNineHolonomicConfiguration) :
    let input := positiveSourceNativeAlgebraicEliminationUpdate configuration
    let response :=
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate input
    holonomicGravityCurvature response gravityKeepResponseTimeAxisPoint ≠
      forcedGravityCurvatureKeepEndpoint
        positiveSmoothUnifiedSource.legacy.sigma
        (input.coframe gravityKeepResponseTimeAxisPoint)
        (holonomicGravityCurvature input gravityKeepResponseTimeAxisPoint)
        (input.gravityAuxiliary gravityKeepResponseTimeAxisPoint) := by
  change
    holonomicGravityCurvature responseImage gravityKeepResponseTimeAxisPoint ≠
      forcedGravityCurvatureKeepEndpoint
        positiveSmoothUnifiedSource.legacy.sigma
        (inputImage.coframe gravityKeepResponseTimeAxisPoint)
        (holonomicGravityCurvature inputImage gravityKeepResponseTimeAxisPoint)
        (inputImage.gravityAuxiliary gravityKeepResponseTimeAxisPoint)
  exact responseCurvature_ne_forcedEndpoint_timeAxis


/-- Therefore the C3h70 normalized-affine response is not an all-point
realizer of its pointwise forced curvature endpoint.  The quantifier is only
over points for this declared response grammar. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_allPoint_forcedCurvature_noGo
    (configuration : StageNineHolonomicConfiguration) :
    ¬ ∀ point : BasePoint,
      let input :=
        positiveSourceNativeAlgebraicEliminationUpdate configuration
      let response :=
        positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate input
      holonomicGravityCurvature response point =
        forcedGravityCurvatureKeepEndpoint
          positiveSmoothUnifiedSource.legacy.sigma
          (input.coframe point)
          (holonomicGravityCurvature input point)
          (input.gravityAuxiliary point) := by
  intro allPoints
  exact
    positiveSourceNativeGravityAlgebraicKeepResponse_ne_forcedEndpoint_timeAxis
      configuration (allPoints gravityKeepResponseTimeAxisPoint)

end

end SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseAwayCurvatureNoGo
