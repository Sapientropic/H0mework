import H0mework.Physics.Coframe.EinsteinCartanSkewCoframeActualResponseOperator

/-!
# Dependency-light P506 matter-spin coordinate normal form

This module isolates the exact 24-coordinate matter-spin readout used by
several later Lorentz action consumers.  It depends only on the actual
matter-spin action and the finite Lorentz coordinate basis; it does not
import the historical C3h108 skew-coframe producer or any stationarity law.

The declarations intentionally retain their historical namespace so old
consumers continue to elaborate while new modules can import the true
physics dependency directly.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceGeneratedEinsteinCartanSkewCoframeLocalActualLift

open ProofFreeRicherAnholonomicSource
open PointwiseDiracSpinConnectionLift
open StageNineConnectionSectorSourceBalance
open StageNineEinsteinCartanSkewCoframeActualResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineConjugateMatterActionTimeVelocity
open StageNineP286GaugeConnectionActionVariation
open StageNineSourceGeneratedMatterSpinActionUpdate
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def lorentzMatterSpinCoordinates
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    lorentzMatterSpinSourceCoefficient source configuration
      (lorentzBivectorOneFormCoordinateDirection formDirection internalPair)
      point

def positiveMatterSpinCoordinatesNormalForm : LorentzBivectorOneForm :=
  ![
    ![0, 0, 0, 0, 0, -(1 / 2 : ℝ)],
    ![0, (1 / 2 : ℝ), 0, -(1 / 2 : ℝ), 0, 0],
    ![-(1 / 2 : ℝ), 0, 0, 0, -(1 / 2 : ℝ), 0],
    ![0, 0, 0, 0, 0, -(1 / 2 : ℝ)]
  ]

set_option linter.unusedSimpArgs false in
theorem positiveMatterSpinCoordinates_eq_normalForm_of_origin
    (configuration : StageNineHolonomicConfiguration)
    (coframeOrigin : configuration.coframe 0 = 1)
    (matterOrigin : configuration.matter 0 = diracSpinTwoMatterProbe)
    (conjugateOrigin :
      configuration.conjugateMatter 0 = diracSpinZeroMatterCoordinate) :
    lorentzMatterSpinCoordinates positiveSmoothUnifiedSource
        configuration 0 =
      positiveMatterSpinCoordinatesNormalForm := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [lorentzMatterSpinCoordinates,
      lorentzBivectorOneFormCoordinateDirection,
      lorentzMatterSpinSourceCoefficient,
      positiveMatterSpinCoordinatesNormalForm,
      coframeOrigin, matterOrigin, conjugateOrigin,
      matterGaugeConnectionFirstVariationDensity,
      matterGaugeConnectionVariationVector,
      matterGaugeKineticSum,
      holonomicMatterLorentzConnectionVariation,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      generatedVolumeDensity, toContinuumPointField,
      positiveSourceTargetMatterCauchyState_matter,
      positiveSourceTargetMatterCauchyState_conjugate,
      positiveSmoothUnifiedSource,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm,
      Fin.sum_univ_four, Fin.sum_univ_six,
      pairFirst, pairSecond, lorentzBivectorFirst,
      lorentzBivectorSecond, minkowskiInternalSign,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      inverseCoframeDiracGamma,
      inverseCoframeDiracGamma_identity,
      diracMatrixMatterAction,
      diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      hyperchargeDegreeTwoMatterCoordinate_probe,
      Matrix.mul_apply]

theorem positiveMatterSpinCoordinates_eq_normalForm :
    lorentzMatterSpinCoordinates positiveSmoothUnifiedSource
        positiveSourceTargetMatterActual 0 =
      positiveMatterSpinCoordinatesNormalForm := by
  apply positiveMatterSpinCoordinates_eq_normalForm_of_origin
  · rfl
  · change
      (sourceActionGeneratedMatterLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        0).matter 0 = diracSpinTwoMatterProbe
    rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
    exact positiveSourceTargetMatterCauchyState_matter
  · change
      (sourceActionGeneratedMatterDualLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        0).conjugateMatter 0 = diracSpinZeroMatterCoordinate
    rw [sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin]
    exact positiveSourceTargetMatterCauchyState_conjugate

end


end
  SaturationMonoid.PhysicsCore.StageNineSourceGeneratedEinsteinCartanSkewCoframeLocalActualLift
