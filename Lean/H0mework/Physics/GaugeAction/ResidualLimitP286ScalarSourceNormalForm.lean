import H0mework.Physics.Admission.ResidualLimitDifferentialChannelNormalForm
import H0mework.Physics.Matter.ResidualLimitMatterOrbitJointClassification

/-!
# S9-C3h25: residual-limit P286 and scalar source normal forms

This module evaluates the two C3h21 residual channels whose remaining terms
are determined by the six residual-limit primitive fields and the already
generated matter first-jet orbit.  It exposes exact source-only functions for
the P286 and scalar origin residuals.

The carrier and matter orbit remain explicit readout hypotheses through
`ExtendsResidualLimitAndMatterOrbitAt`.  No differential response, shell,
state update, zero-fiber witness, or stationarity receipt is stored or
generated here.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitP286ScalarSourceNormalForm

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageEightSourceGeneratedMatter
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineResidualLimitDifferentialChannelNormalForm
open StageNineResidualLimitMatterOrbitJointClassification
open StageNineSourceMatterFirstJetResidualOrbit
open StageNineConnectionSectorSourceBalance
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceGeneratedPartialPrimitiveCarrier
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open SU7ExteriorYukawaMassSpectrum

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev positiveResidualLimitSixFieldCarrier :
    StageNinePartialPrimitiveCarrier :=
  positiveSourceResidualLimitStageNinePartialPrimitiveCarrier

/-! ## Source scalar and P286-current readouts -/

def positiveSourceOriginScalarGaugeDerivative
    (direction : LorentzianIndex) : ScalarCoordinateCarrier :=
  scalarMotherLieAction
    (p286LieBlockEmbed
      (sourceP286Potential positiveSmoothUnifiedSource.legacy direction))
    (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)

private theorem residualLimitExtension_scalar_eq_constantVacuum
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration) :
    configuration.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [extension.scalar]
  funext point
  change scalarCoordinateAction
      (generatedTransition positiveSmoothUnifiedSource 0 0 point)
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
    sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [generatedTransition_normalized]
  exact scalarCoordinateAction_one _

private theorem residualLimitExtension_scalarCovariantDerivative_origin_eq_source
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration)
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative configuration 0 direction =
      positiveSourceOriginScalarGaugeDerivative direction := by
  unfold holonomicScalarCovariantDerivative
    positiveSourceOriginScalarGaugeDerivative
  rw [residualLimitExtension_scalar_eq_constantVacuum configuration extension,
    extension.gaugeConnection]
  simp [positiveSourceResidualLimitStageNinePartialPrimitiveCarrier,
    positiveSourceStageNinePartialPrimitiveCarrier,
    sourceGeneratedStageNinePartialPrimitiveCarrier,
    sourceP286AffineConnectionField_origin, fieldDirectionalDerivative]

def positiveSourceOriginP286ScalarCurrent
    (direction : P286GaugeOneForm) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex,
        ((lorentzianMetricOfCoframe (1 : LorentzianCoframe))⁻¹ first second) *
          (scalarCoordinatePairingRe
              (scalarMotherLieAction
                (p286LieBlockEmbed
                  (p286CoordinateEquiv.symm (direction first)))
                (sourceGeneratedVacuumCoordinates
                  positiveSmoothUnifiedSource))
              (positiveSourceOriginScalarGaugeDerivative second) +
            scalarCoordinatePairingRe
              (positiveSourceOriginScalarGaugeDerivative first)
              (scalarMotherLieAction
                (p286LieBlockEmbed
                  (p286CoordinateEquiv.symm (direction second)))
                (sourceGeneratedVacuumCoordinates
                  positiveSmoothUnifiedSource)))

private theorem residualLimitMatterOrbit_p286ScalarCurrent_origin_eq_source
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (belongs : ExtendsResidualLimitAndMatterOrbitAt n configuration)
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource configuration
        direction 0 =
      positiveSourceOriginP286ScalarCurrent direction := by
  have coframeOrigin :
      (toContinuumPointField configuration 0).coframe = 1 :=
    belongs.matterOrbit.coframeOrigin
  have scalarOrigin :
      configuration.scalar 0 =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    rw [residualLimitExtension_scalar_eq_constantVacuum configuration
      belongs.residualLimit]
  have covariantDerivativeOrigin :
      (toContinuumPointField configuration 0).scalarCovariantDerivative =
        positiveSourceOriginScalarGaugeDerivative := by
    funext derivativeDirection
    exact residualLimitExtension_scalarCovariantDerivative_origin_eq_source
      configuration belongs.residualLimit derivativeDirection
  unfold p286ScalarCurrentCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    positiveSourceOriginP286ScalarCurrent
    holonomicScalarGaugeConnectionVariation
  rw [coframeOrigin, scalarOrigin, covariantDerivativeOrigin]
  simp [generatedVolumeDensity, scalarFrameRelativeCovariantDerivative,
    p286GaugeConnectionMotherVariation]
  rw [coframeOrigin, Matrix.det_one, abs_one, one_mul]

/-! ## Source-only P286 balance -/

def positiveResidualLimitP286AuxiliaryCoordinate
    (point : BasePoint) : P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateEquiv
      (positiveResidualLimitSixFieldCarrier.gaugeAuxiliary point pair)

def positiveResidualLimitP286ConnectionCoordinate
    (point : BasePoint) : P286GaugeOneForm :=
  fun formDirection =>
    p286CoordinateEquiv
      (positiveResidualLimitSixFieldCarrier.gaugeConnection point formDirection)

def positiveResidualLimitP286AlgebraicCurvatureDirection
    (direction : P286GaugeOneForm) : P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateLieBracket
      (direction (pairFirst pair))
      (positiveResidualLimitP286ConnectionCoordinate 0 (pairSecond pair)) +
    p286CoordinateLieBracket
      (positiveResidualLimitP286ConnectionCoordinate 0 (pairFirst pair))
      (direction (pairSecond pair))

def positiveResidualLimitP286BFAlgebraicResponse
    (direction : P286GaugeOneForm) : ℝ :=
  abs (Matrix.det (positiveResidualLimitSixFieldCarrier.coframe 0)) *
    p286GaugeBFCurvatureIncrementDensity
      (positiveResidualLimitSixFieldCarrier.coframe 0)
      (coframeGaugeSpacetimeHodgeLinear
        (positiveResidualLimitSixFieldCarrier.coframe 0))
      (positiveResidualLimitP286AuxiliaryCoordinate 0)
      (positiveResidualLimitP286AlgebraicCurvatureDirection direction)

def positiveResidualLimitP286DifferentialMomentum
    (direction : P286GaugeTwoForm) (point : BasePoint) : ℝ :=
  abs (Matrix.det (positiveResidualLimitSixFieldCarrier.coframe point)) *
    p286GaugeAuxiliaryHodgePairingPolynomial
      (positiveResidualLimitSixFieldCarrier.coframe point)
      (positiveResidualLimitP286AuxiliaryCoordinate point) direction

def positiveResidualLimitP286Divergence
    (direction : P286GaugeOneForm) : ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (positiveResidualLimitP286DifferentialMomentum
        (p286GaugeExteriorDerivativeDirection derivativeDirection direction))
      0 derivativeDirection

def positiveResidualLimitP286BFBalance
    (direction : P286GaugeOneForm) : ℝ :=
  positiveResidualLimitP286BFAlgebraicResponse direction -
    positiveResidualLimitP286Divergence direction

/-- The full source-only P286 balance, including the scalar current rather
than discarding it. -/
def positiveResidualLimitP286TotalBalance
    (direction : P286GaugeOneForm) : ℝ :=
  positiveResidualLimitP286BFBalance direction +
    positiveSourceOriginP286ScalarCurrent direction

private theorem residualLimitExtension_p286BFBalance_origin_eq_source
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration)
    (direction : P286GaugeOneForm) :
    p286GaugeBFBalanceCoefficient configuration direction 0 =
      positiveResidualLimitP286BFBalance direction := by
  unfold p286GaugeBFBalanceCoefficient p286GaugeBFAlgebraicCoefficient
    p286GaugeConnectionBFDifferentialMomentumDivergence
    p286GaugeConnectionBFDifferentialMomentum
    p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
    positiveResidualLimitP286BFBalance
    positiveResidualLimitP286BFAlgebraicResponse
    positiveResidualLimitP286Divergence
    positiveResidualLimitP286DifferentialMomentum
    positiveResidualLimitP286AlgebraicCurvatureDirection
    positiveResidualLimitP286ConnectionCoordinate
    positiveResidualLimitP286AuxiliaryCoordinate
    generatedVolumeDensity toContinuumPointField
  rw [extension.coframe, extension.gaugeConnection,
    extension.gaugeAuxiliary]

/-- Pointwise origin P286 normal form on the existing residual-limit and
matter-orbit reader class. -/
theorem residualLimitMatterOrbit_p286Residual_origin_eq_sourceOnly
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (belongs : ExtendsResidualLimitAndMatterOrbitAt n configuration)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        configuration direction 0 =
      positiveResidualLimitP286TotalBalance direction := by
  rw [realizingOrbit_p286Residual_origin_eq_bfBalance_add_scalarCurrent
      n configuration belongs.matterOrbit direction,
    residualLimitExtension_p286BFBalance_origin_eq_source
      configuration belongs.residualLimit direction,
    residualLimitMatterOrbit_p286ScalarCurrent_origin_eq_source
      n configuration belongs direction]
  rfl

/-- The complete P286 direction function is fixed by the same source-only
balance; this is stronger than a single-probe equality but remains a readout. -/
theorem residualLimitMatterOrbit_p286Residual_origin_eq_sourceOnly_allDirections
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (belongs : ExtendsResidualLimitAndMatterOrbitAt n configuration) :
    (fun direction =>
      p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource configuration direction 0) =
      positiveResidualLimitP286TotalBalance := by
  funext direction
  exact residualLimitMatterOrbit_p286Residual_origin_eq_sourceOnly
    n configuration belongs direction

/-! ## Source-only scalar kinetic balance -/

def positiveSourceOriginScalarKineticAlgebraic
    (direction : ScalarCoordinateCarrier) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex,
        ((lorentzianMetricOfCoframe (1 : LorentzianCoframe))⁻¹ first second) *
          (scalarCoordinatePairingRe
              (scalarMotherLieAction
                (p286LieBlockEmbed
                  (sourceP286Potential positiveSmoothUnifiedSource.legacy
                    first))
                direction)
              (positiveSourceOriginScalarGaugeDerivative second) +
            scalarCoordinatePairingRe
              (positiveSourceOriginScalarGaugeDerivative first)
              (scalarMotherLieAction
                (p286LieBlockEmbed
                  (sourceP286Potential positiveSmoothUnifiedSource.legacy
                    second))
                direction))

def positiveResidualLimitScalarCovariantDerivative
    (point : BasePoint) (direction : LorentzianIndex) :
    ScalarCoordinateCarrier :=
  fieldDirectionalDerivative positiveResidualLimitSixFieldCarrier.scalar
      point direction +
    scalarMotherLieAction
      (p286LieBlockEmbed
        (positiveResidualLimitSixFieldCarrier.gaugeConnection point direction))
      (positiveResidualLimitSixFieldCarrier.scalar point)

def positiveResidualLimitScalarDifferentialMomentum
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) : ℝ :=
  abs (Matrix.det (positiveResidualLimitSixFieldCarrier.coframe point)) *
    ((1 / 2 : ℝ) *
      ∑ first : LorentzianIndex,
        ∑ second : LorentzianIndex,
          ((lorentzianMetricOfCoframe
            (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
              first second) *
            (scalarCoordinatePairingRe
                (scalarVariationDifferentialDirection direction
                  derivativeDirection first)
                (positiveResidualLimitScalarCovariantDerivative point second) +
              scalarCoordinatePairingRe
                (positiveResidualLimitScalarCovariantDerivative point first)
                (scalarVariationDifferentialDirection direction
                  derivativeDirection second)))

def positiveResidualLimitScalarDivergence
    (direction : ScalarCoordinateCarrier) : ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (positiveResidualLimitScalarDifferentialMomentum direction
        derivativeDirection) 0 derivativeDirection

/-- The full source-only scalar kinetic balance.  The actual differential
divergence stays visible in the expression. -/
def positiveResidualLimitScalarKineticBalance
    (direction : ScalarCoordinateCarrier) : ℝ :=
  positiveSourceOriginScalarKineticAlgebraic direction -
    positiveResidualLimitScalarDivergence direction

private theorem residualLimitMatterOrbit_scalarKineticAlgebraic_origin_eq_source
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (belongs : ExtendsResidualLimitAndMatterOrbitAt n configuration)
    (direction : ScalarCoordinateCarrier) :
    generatedVolumeDensity (toContinuumPointField configuration 0) *
        scalarGaugeConnectionKineticFirstVariationDensity
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField configuration 0)
          (holonomicScalarVariationAlgebraicDirection configuration
            direction 0) =
      positiveSourceOriginScalarKineticAlgebraic direction := by
  have coframeOrigin :
      (toContinuumPointField configuration 0).coframe = 1 :=
    belongs.matterOrbit.coframeOrigin
  have covariantDerivativeOrigin :
      (toContinuumPointField configuration 0).scalarCovariantDerivative =
        positiveSourceOriginScalarGaugeDerivative := by
    funext derivativeDirection
    exact residualLimitExtension_scalarCovariantDerivative_origin_eq_source
      configuration belongs.residualLimit derivativeDirection
  have gaugeConnectionOrigin : ∀ formDirection,
      configuration.gaugeConnection 0 formDirection =
        sourceP286Potential positiveSmoothUnifiedSource.legacy formDirection := by
    intro formDirection
    rw [belongs.residualLimit.gaugeConnection]
    exact sourceP286AffineConnectionField_origin _ _
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    positiveSourceOriginScalarKineticAlgebraic
    holonomicScalarVariationAlgebraicDirection
  rw [coframeOrigin, covariantDerivativeOrigin]
  simp_rw [gaugeConnectionOrigin]
  simp [generatedVolumeDensity, scalarFrameRelativeCovariantDerivative]
  rw [coframeOrigin, Matrix.det_one, abs_one, one_mul]

private theorem residualLimitExtension_scalarMomentum_eq_source
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource configuration
        direction derivativeDirection point =
      positiveResidualLimitScalarDifferentialMomentum direction
        derivativeDirection point := by
  have coframePoint :
      (toContinuumPointField configuration point).coframe =
        positiveResidualLimitSixFieldCarrier.coframe point := by
    change configuration.coframe point = _
    rw [extension.coframe]
  have scalarCovariantDerivativePoint :
      (toContinuumPointField configuration point).scalarCovariantDerivative =
        positiveResidualLimitScalarCovariantDerivative point := by
    funext formDirection
    change holonomicScalarCovariantDerivative configuration point
        formDirection = _
    unfold holonomicScalarCovariantDerivative
      positiveResidualLimitScalarCovariantDerivative
    rw [extension.gaugeConnection, extension.scalar]
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    positiveResidualLimitScalarDifferentialMomentum generatedVolumeDensity
  rw [coframePoint, scalarCovariantDerivativePoint]
  simp [scalarFrameRelativeCovariantDerivative]

private theorem residualLimitExtension_scalarDivergence_eq_source
    (configuration : StageNineHolonomicConfiguration)
    (extension :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier configuration)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        configuration direction 0 =
      positiveResidualLimitScalarDivergence direction := by
  unfold scalarDifferentialMomentumDivergence
    positiveResidualLimitScalarDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  apply congrArg
    (fun momentum : BasePoint → ℝ =>
      fieldDirectionalDerivative momentum 0 derivativeDirection)
  funext point
  exact residualLimitExtension_scalarMomentum_eq_source configuration extension
    direction derivativeDirection point

/-- Pointwise origin scalar normal form on the existing residual-limit and
matter-orbit reader class. -/
theorem residualLimitMatterOrbit_scalarResidual_origin_eq_sourceOnly
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (belongs : ExtendsResidualLimitAndMatterOrbitAt n configuration)
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        configuration direction 0 =
      positiveResidualLimitScalarKineticBalance direction := by
  rw [residualLimitRealizingOrbit_scalarResidual_origin_eq_kineticBalance
      n configuration belongs.residualLimit belongs.matterOrbit direction,
    residualLimitMatterOrbit_scalarKineticAlgebraic_origin_eq_source
      n configuration belongs direction,
    residualLimitExtension_scalarDivergence_eq_source
      configuration belongs.residualLimit direction]
  rfl

/-- The complete scalar direction function is fixed by the source-only
balance, without selecting a stationary branch. -/
theorem residualLimitMatterOrbit_scalarResidual_origin_eq_sourceOnly_allDirections
    (n : ℕ)
    (configuration : StageNineHolonomicConfiguration)
    (belongs : ExtendsResidualLimitAndMatterOrbitAt n configuration) :
    (fun direction =>
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        configuration direction 0) =
      positiveResidualLimitScalarKineticBalance := by
  funext direction
  exact residualLimitMatterOrbit_scalarResidual_origin_eq_sourceOnly
    n configuration belongs direction

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitP286ScalarSourceNormalForm
