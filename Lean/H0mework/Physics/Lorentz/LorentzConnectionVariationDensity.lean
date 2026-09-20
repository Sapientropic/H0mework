import H0mework.Physics.Lorentz.LorentzConnectionActionVariation
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity

/-!
# S9-C3b2: analytic control of the Lorentz connection variation density

The primitive Lorentz-skew variation from C3b0 and its exact local action
polynomial from C3b1 are promoted to honest analytic data.  Smoothness of the
six bivector-coordinate variation generates continuity of the lifted
connection, its first derivative, the non-Abelian curvature jets, and the
actual exterior-Dirac spin jet.  Those facts generate continuity of both
local action coefficients.

Compact support of the primitive variation and of the derivatives of its
lifted scalar components generates compact support and integrability of the
first and second densities.  No spin current, curvature increment, support,
integrability, stationarity, or equation certificate is supplied.
-/

namespace SaturationMonoid.PhysicsCore.StageNineLorentzConnectionVariationDensity

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineGravityAuxiliaryVariation
open StageNinePlebanskiMultiplierVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActionVariation
open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open DiracCliffordRepresentation
open MeasureTheory
open scoped ContDiff

noncomputable section

set_option maxHeartbeats 600000

@[simp] theorem lorentzSkewConnectionOfBivectorOneForm_zero :
    lorentzSkewConnectionOfBivectorOneForm (0 : LorentzBivectorOneForm) = 0 := by
  funext formDirection internalOut internalIn
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix]

@[simp] theorem loweredLorentzConnectionCoefficient_zero
    (formDirection : LorentzianIndex) (pair : Fin 6) :
    loweredLorentzConnectionCoefficient (0 : PointwiseLorentzSpinConnection)
        formDirection pair = 0 := by
  simp [loweredLorentzConnectionCoefficient]

@[simp] theorem diracSpinConnectionLift_zero
    (direction : LorentzianIndex) :
    diracSpinConnectionLift (0 : PointwiseLorentzSpinConnection) direction =
      0 := by
  funext row column
  simp [diracSpinConnectionLift]

@[simp] theorem diracMatrixMatterAction_zero_matrix
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (0 : DiracMatrix) matter = 0 := by
  funext row
  simp [diracMatrixMatterAction]

def compactLorentzConnectionVariationComponent
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (formDirection internalOut internalIn : LorentzianIndex) :
    CompactlySupportedSmoothVariation ℝ where
  toFun := fun point =>
    lorentzSkewConnectionOfBivectorOneForm (variation point)
      formDirection internalOut internalIn
  smooth := by
    have coordinateSmooth : ∀ pair : Fin 6,
        ContDiff ℝ ∞ fun point => variation point formDirection pair := by
      intro pair
      exact contDiff_pi.mp (contDiff_pi.mp variation.smooth formDirection) pair
    unfold lorentzSkewConnectionOfBivectorOneForm
      loweredLorentzBivectorMatrix
    exact contDiff_const.mul
      (ContDiff.sum fun pair _ =>
        (coordinateSmooth pair).mul contDiff_const)
  compactSupport := by
    have variationEventually := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at variationEventually ⊢
    filter_upwards [variationEventually] with point variationZero
    simp [variationZero, lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix]

theorem lorentzSkewConnectionVariation_component_continuous
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (formDirection internalOut internalIn : LorentzianIndex) :
    Continuous fun point =>
      lorentzSkewConnectionOfBivectorOneForm (variation point)
        formDirection internalOut internalIn :=
  (compactLorentzConnectionVariationComponent variation formDirection
    internalOut internalIn).smooth.continuous

theorem lorentzConnectionVariationDerivative_continuous
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    Continuous fun point =>
      lorentzConnectionVariationDerivative variation point derivativeDirection
        formDirection internalOut internalIn := by
  change Continuous fun point =>
    fderiv ℝ
      (compactLorentzConnectionVariationComponent variation formDirection
        internalOut internalIn)
      point (coordinateDirection derivativeDirection)
  exact compactVariation_directionalDerivative_continuous
    (compactLorentzConnectionVariationComponent variation formDirection
      internalOut internalIn) derivativeDirection

theorem lorentzConnectionLinearCurvatureVariation_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous
      (lorentzConnectionLinearCurvatureVariation configuration variation) := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  have derivativeContinuous : ∀
      (derivativeDirection formDirection internalOut internalIn :
        LorentzianIndex),
      Continuous fun point =>
        lorentzConnectionVariationDerivative variation point
          derivativeDirection formDirection internalOut internalIn :=
    lorentzConnectionVariationDerivative_continuous variation
  have variedContinuous : ∀
      (formDirection internalOut internalIn : LorentzianIndex),
      Continuous fun point =>
        lorentzSkewConnectionOfBivectorOneForm (variation point)
          formDirection internalOut internalIn :=
    lorentzSkewConnectionVariation_component_continuous variation
  have connectionContinuous : ∀
      (formDirection internalOut internalIn : LorentzianIndex),
      Continuous fun point =>
        configuration.gravityConnection point formDirection
          internalOut internalIn := fun formDirection internalOut internalIn =>
    (smooth.2.1 formDirection internalOut internalIn).continuous
  unfold lorentzConnectionLinearCurvatureVariation
  dsimp only
  fun_prop

theorem lorentzConnectionQuadraticCurvatureVariation_continuous
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous (lorentzConnectionQuadraticCurvatureVariation variation) := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  have variedContinuous : ∀
      (formDirection internalOut internalIn : LorentzianIndex),
      Continuous fun point =>
        lorentzSkewConnectionOfBivectorOneForm (variation point)
          formDirection internalOut internalIn :=
    lorentzSkewConnectionVariation_component_continuous variation
  unfold lorentzConnectionQuadraticCurvatureVariation
  dsimp only
  fun_prop

theorem diracSpinConnectionLift_lorentzVariation_continuous
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      diracSpinConnectionLift
        (lorentzSkewConnectionOfBivectorOneForm (variation point)) direction := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  have variationContinuous : ∀ pair : Fin 6,
      Continuous fun point => variation point direction pair := by
    intro pair
    exact (continuous_apply pair).comp
      ((continuous_apply direction).comp variation.smooth.continuous)
  unfold diracSpinConnectionLift
  simp_rw [loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  fun_prop

theorem holonomicMatterLorentzConnectionVariation_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (holonomicMatterLorentzConnectionVariation configuration variation point
          direction) := by
  have matrixContinuous :=
    diracSpinConnectionLift_lorentzVariation_continuous variation direction
  have matterContinuous : Continuous fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1.continuous
  unfold holonomicMatterLorentzConnectionVariation
  exact diracMatrixMatterCoordinate_raw_apply_continuous _ _
    matrixContinuous matterContinuous

theorem holonomicMatterLorentzKineticSummand_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            direction)
          (holonomicMatterLorentzConnectionVariation configuration variation
            point direction)) :=
  diracMatrixMatterCoordinate_raw_apply_continuous _ _
    (holonomicInverseCoframeDiracGamma_continuous configuration smooth
      nondegenerate direction)
    (holonomicMatterLorentzConnectionVariation_coordinate_continuous
      configuration smooth variation direction)

theorem holonomicMatterLorentzKineticSum_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterLorentzConnectionVariation configuration variation
            point)) := by
  have sumContinuous : Continuous fun point =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              direction)
            (holonomicMatterLorentzConnectionVariation configuration variation
              point direction)) := by
    apply continuous_finsetSum
    intro direction _
    exact holonomicMatterLorentzKineticSummand_coordinate_continuous
      configuration smooth nondegenerate variation direction
  exact sumContinuous.congr fun point => by
    unfold matterGaugeKineticSum matterDerivativeFrameRelative
    simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]

theorem holonomicMatterLorentzVariationVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeConnectionVariationVector source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterLorentzConnectionVariation configuration variation
            point)) := by
  have kineticContinuous :=
    holonomicMatterLorentzKineticSum_coordinate_continuous source
      configuration smooth nondegenerate variation
  have coordinateContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterLorentzConnectionVariation configuration variation
            point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticContinuous).congr fun point => rfl
  unfold matterGaugeConnectionVariationVector
  exact coordinateContinuous.congr fun point => by
    rw [map_smul]

theorem holonomicMatterLorentzFirstDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous fun point =>
      matterGaugeConnectionFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicMatterLorentzConnectionVariation configuration variation
          point) := by
  let vector := fun point =>
    matterGaugeConnectionVariationVector source 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterLorentzConnectionVariation configuration variation point)
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    holonomicMatterLorentzVariationVector_coordinate_continuous source
      configuration smooth nondegenerate variation
  have dualCoefficientContinuous : ∀ index : MatterCoordinateIndex,
      Continuous fun point =>
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) :=
    fun index => smooth.2.2.2.2.2.2.2.2 index |>.continuous
  have pairingContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply continuous_finsetSum
    intro index _
    have vectorCoefficientContinuous : Continuous fun point =>
        matterCoordinateEquiv (vector point) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp
          vectorCoordinateContinuous
    exact vectorCoefficientContinuous.mul (dualCoefficientContinuous index)
  have realPairingContinuous := Complex.continuous_re.comp pairingContinuous
  unfold matterGaugeConnectionFirstVariationDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart]
  exact realPairingContinuous.congr fun point => by
    simp only [Function.comp_apply]
    rw [← matterDual_coordinate_expansion
      (configuration.conjugateMatter point)
      (matterCoordinateEquiv (vector point))]
    simp only [matterCoordinateEquiv.symm_apply_apply]
    rfl

theorem holonomicLorentzConnectionBFFirstDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous fun point =>
      gravityBFCurvatureIncrementDensity
        (configuration.coframe point)
        (configuration.gravityAuxiliary point)
        (lorentzConnectionLinearCurvatureVariation configuration variation
          point) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have auxiliaryContinuous :=
    holonomicGravityAuxiliary_continuous configuration smooth
  have variationContinuous :=
    lorentzConnectionLinearCurvatureVariation_continuous configuration smooth
      variation
  have hodgeVariationContinuous :=
    holonomicGravitySpacetimeHodge_apply_continuous configuration smooth
      nondegenerate _ variationContinuous
  have pairingContinuous := gravityCoframePairing_apply_continuous
    configuration.coframe coframeContinuous configuration.gravityAuxiliary
      (fun point => gravitySpacetimeHodge (configuration.coframe point)
        (lorentzConnectionLinearCurvatureVariation configuration variation
          point))
      auxiliaryContinuous hodgeVariationContinuous
  simpa [gravityBFCurvatureIncrementDensity] using pairingContinuous

theorem holonomicLorentzConnectionBFSecondDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous fun point =>
      gravityBFCurvatureIncrementDensity
        (configuration.coframe point)
        (configuration.gravityAuxiliary point)
        (lorentzConnectionQuadraticCurvatureVariation variation point) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have auxiliaryContinuous :=
    holonomicGravityAuxiliary_continuous configuration smooth
  have variationContinuous :=
    lorentzConnectionQuadraticCurvatureVariation_continuous variation
  have hodgeVariationContinuous :=
    holonomicGravitySpacetimeHodge_apply_continuous configuration smooth
      nondegenerate _ variationContinuous
  have pairingContinuous := gravityCoframePairing_apply_continuous
    configuration.coframe coframeContinuous configuration.gravityAuxiliary
      (fun point => gravitySpacetimeHodge (configuration.coframe point)
        (lorentzConnectionQuadraticCurvatureVariation variation point))
      auxiliaryContinuous hodgeVariationContinuous
  simpa [gravityBFCurvatureIncrementDensity] using pairingContinuous

theorem holonomicLorentzConnectionFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous
      (holonomicLorentzConnectionFirstVariationDensity source 0 configuration
        variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      abs (Matrix.det (configuration.coframe point)) :=
    coframeContinuous.matrix_det.abs
  have bfContinuous := holonomicLorentzConnectionBFFirstDensity_continuous
    configuration smooth nondegenerate variation
  have matterContinuous := holonomicMatterLorentzFirstDensity_continuous source
    configuration smooth nondegenerate variation
  unfold holonomicLorentzConnectionFirstVariationDensity
    lorentzConnectionFirstVariationDensity generatedVolumeDensity
  exact volumeContinuous.mul (bfContinuous.add matterContinuous)

theorem holonomicLorentzConnectionSecondVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous
      (holonomicLorentzConnectionSecondVariationDensity configuration
        variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      abs (Matrix.det (configuration.coframe point)) :=
    coframeContinuous.matrix_det.abs
  have bfContinuous := holonomicLorentzConnectionBFSecondDensity_continuous
    configuration smooth nondegenerate variation
  unfold holonomicLorentzConnectionSecondVariationDensity
    lorentzConnectionSecondVariationDensity generatedVolumeDensity
  exact volumeContinuous.mul bfContinuous

theorem lorentzConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ derivativeDirection formDirection internalOut
        internalIn : LorentzianIndex,
      lorentzConnectionVariationDerivative variation point derivativeDirection
        formDirection internalOut internalIn = 0) :
    lorentzConnectionLinearCurvatureVariation configuration variation point =
      0 := by
  funext internalPair spacetimePair
  simp [lorentzConnectionLinearCurvatureVariation, variationZero,
    derivativeZero]

theorem lorentzConnectionQuadraticCurvatureVariation_eq_zero
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    lorentzConnectionQuadraticCurvatureVariation variation point = 0 := by
  funext internalPair spacetimePair
  simp [lorentzConnectionQuadraticCurvatureVariation, variationZero]

theorem holonomicMatterLorentzConnectionVariation_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    holonomicMatterLorentzConnectionVariation configuration variation point =
      0 := by
  funext direction
  simp [holonomicMatterLorentzConnectionVariation, variationZero,
    PointwiseDiracSpinConnectionLift.diracSpinConnectionLift]

@[simp] theorem gravityBFCurvatureIncrementDensity_zero
    (coframe : LorentzianCoframe) (auxiliary : PhysicalBivector) :
    gravityBFCurvatureIncrementDensity coframe auxiliary 0 = 0 := by
  simp [gravityBFCurvatureIncrementDensity, gravityCoframePairing,
    coframeTwoFormMetricPairing]

theorem holonomicLorentzConnectionFirstVariationDensity_eq_zero_of_jet_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ derivativeDirection formDirection internalOut
        internalIn : LorentzianIndex,
      lorentzConnectionVariationDerivative variation point derivativeDirection
        formDirection internalOut internalIn = 0) :
    holonomicLorentzConnectionFirstVariationDensity source chart configuration
      variation point = 0 := by
  unfold holonomicLorentzConnectionFirstVariationDensity
  rw [show lorentzConnectionLinearCurvatureVariation configuration variation
      point = 0 from
    lorentzConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
      configuration variation point variationZero derivativeZero]
  rw [show holonomicMatterLorentzConnectionVariation configuration variation
      point = 0 from
    holonomicMatterLorentzConnectionVariation_eq_zero configuration variation
      point variationZero]
  simp [lorentzConnectionFirstVariationDensity]

theorem holonomicLorentzConnectionSecondVariationDensity_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    holonomicLorentzConnectionSecondVariationDensity configuration variation
      point = 0 := by
  unfold holonomicLorentzConnectionSecondVariationDensity
  rw [show lorentzConnectionQuadraticCurvatureVariation variation point = 0
    from lorentzConnectionQuadraticCurvatureVariation_eq_zero variation point
      variationZero]
  simp [lorentzConnectionSecondVariationDensity]

theorem compactLorentzConnectionVariation_eventually_jet_zero
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    ∀ᶠ point in Filter.coclosedCompact BasePoint,
      variation point = 0 ∧
        ∀ derivativeDirection formDirection internalOut internalIn :
            LorentzianIndex,
          lorentzConnectionVariationDerivative variation point
            derivativeDirection formDirection internalOut internalIn = 0 := by
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  have derivativeEventually : ∀
      (derivativeDirection formDirection internalOut internalIn :
        LorentzianIndex),
      ∀ᶠ point in Filter.coclosedCompact BasePoint,
        lorentzConnectionVariationDerivative variation point
          derivativeDirection formDirection internalOut internalIn = 0 := by
    intro derivativeDirection formDirection internalOut internalIn
    have actual := compactVariation_directionalDerivative_compact
      (compactLorentzConnectionVariationComponent variation formDirection
        internalOut internalIn) derivativeDirection
    rw [hasCompactSupport_iff_eventuallyEq] at actual
    change ∀ᶠ point in Filter.coclosedCompact BasePoint,
      fderiv ℝ
          (compactLorentzConnectionVariationComponent variation formDirection
            internalOut internalIn)
          point (coordinateDirection derivativeDirection) = 0
    exact actual
  have everyDerivativeEventually :
      ∀ᶠ point in Filter.coclosedCompact BasePoint,
        ∀ derivativeDirection formDirection internalOut internalIn :
            LorentzianIndex,
          lorentzConnectionVariationDerivative variation point
            derivativeDirection formDirection internalOut internalIn = 0 := by
    apply Filter.eventually_all.2
    intro derivativeDirection
    apply Filter.eventually_all.2
    intro formDirection
    apply Filter.eventually_all.2
    intro internalOut
    apply Filter.eventually_all.2
    intro internalIn
    exact derivativeEventually derivativeDirection formDirection internalOut
      internalIn
  filter_upwards [variationEventually, everyDerivativeEventually] with
    point variationZero derivativeZero
  exact ⟨variationZero, derivativeZero⟩

theorem holonomicLorentzConnectionFirstVariationDensity_compact
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    HasCompactSupport
      (holonomicLorentzConnectionFirstVariationDensity source chart
        configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactLorentzConnectionVariation_eventually_jet_zero variation] with
    point jetZero
  exact holonomicLorentzConnectionFirstVariationDensity_eq_zero_of_jet_zero
    source chart configuration variation point jetZero.1 jetZero.2

theorem holonomicLorentzConnectionSecondVariationDensity_compact
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    HasCompactSupport
      (holonomicLorentzConnectionSecondVariationDensity configuration
        variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  filter_upwards [variationEventually] with point variationZero
  exact holonomicLorentzConnectionSecondVariationDensity_eq_zero configuration
    variation point variationZero

theorem holonomicLorentzConnectionFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Integrable
      (holonomicLorentzConnectionFirstVariationDensity source 0 configuration
        variation) :=
  (holonomicLorentzConnectionFirstVariationDensity_continuous source
    configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicLorentzConnectionFirstVariationDensity_compact source 0
        configuration variation)

theorem holonomicLorentzConnectionSecondVariationDensity_integrable
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Integrable
      (holonomicLorentzConnectionSecondVariationDensity configuration
        variation) :=
  (holonomicLorentzConnectionSecondVariationDensity_continuous configuration
    smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicLorentzConnectionSecondVariationDensity_compact configuration
        variation)

end

end SaturationMonoid.PhysicsCore.StageNineLorentzConnectionVariationDensity
