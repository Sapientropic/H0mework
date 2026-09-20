import H0mework.Physics.Lorentz.LorentzConnectionMomentumRegularity
import H0mework.Physics.Geometry.FundamentalLemma

/-!
# S9-C3b4b: pointwise Lorentz connection equation by genuine IBP

One primitive compactly supported Lorentz-skew connection variation is
specialized to a smooth scalar bump times an arbitrary constant six-coordinate
one-form direction.  Its actual curvature variation is split into derivative
and algebraic commutator channels, while the same direction generates the
exterior-Dirac spin channel.

The canonical weak equation is integrated by parts in every spacetime
direction using the smooth BF momentum from C3b4a.  All continuity, compact
support, and integrability obligations are generated internally.  The smooth
bump fundamental lemma then produces the pointwise directional
gravity-BF/spin-current equation.  No current, residual, regularity, or
equation certificate is supplied.
-/

namespace SaturationMonoid.PhysicsCore.StageNineLorentzConnectionPointwiseEquation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNinePlebanskiMultiplierVariation
open StageNineGravityAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionVariationDensity
open StageNineLorentzConnectionWeakEquation
open StageNineLorentzConnectionMomentumRegularity
open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open DiracCliffordRepresentation
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

set_option maxHeartbeats 600000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

def scalarTimesLorentzConnectionVariation
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation LorentzBivectorOneForm where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

@[simp] theorem scalarTimesLorentzConnectionVariation_apply
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    scalarTimesLorentzConnectionVariation direction variation point =
      variation point • direction :=
  rfl

theorem lorentzConnectionVariationDerivative_scalarTimes
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    lorentzConnectionVariationDerivative
        (scalarTimesLorentzConnectionVariation direction variation) point
        derivativeDirection formDirection internalOut internalIn =
      fieldDirectionalDerivative variation point derivativeDirection *
        lorentzSkewConnectionOfBivectorOneForm direction formDirection
          internalOut internalIn := by
  have differentiable : DifferentiableAt ℝ
      (variation : BasePoint → ℝ) point :=
    (variation.smooth.differentiable (by simp)).differentiableAt
  unfold lorentzConnectionVariationDerivative fieldDirectionalDerivative
  rw [show (fun candidate =>
      lorentzSkewConnectionOfBivectorOneForm
          (scalarTimesLorentzConnectionVariation direction variation candidate)
          formDirection internalOut internalIn) =
      fun candidate => variation candidate •
        lorentzSkewConnectionOfBivectorOneForm direction formDirection
          internalOut internalIn by
    funext candidate
    rw [scalarTimesLorentzConnectionVariation_apply,
      lorentzSkewConnectionOfBivectorOneForm_smul]
    rfl]
  rw [fderiv_smul_const differentiable]
  rfl

def lorentzConnectionExteriorDerivativeDirection
    (derivativeDirection : LorentzianIndex)
    (direction : LorentzBivectorOneForm) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    minkowskiInternalSign internalOut *
      ((if derivativeDirection = first then
          lorentzSkewConnectionOfBivectorOneForm direction second internalOut
            internalIn else 0) -
        if derivativeDirection = second then
          lorentzSkewConnectionOfBivectorOneForm direction first internalOut
            internalIn else 0)

def lorentzConnectionExteriorDerivativeVariation
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint) :
    PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    minkowskiInternalSign internalOut *
      (lorentzConnectionVariationDerivative variation point first second
          internalOut internalIn -
        lorentzConnectionVariationDerivative variation point second first
          internalOut internalIn)

def lorentzConnectionAlgebraicCurvatureVariation
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint) :
    PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    let varied := lorentzSkewConnectionOfBivectorOneForm (variation point)
    minkowskiInternalSign internalOut *
      ∑ middle : LorentzianIndex,
        (varied first internalOut middle *
            configuration.gravityConnection point second middle internalIn +
          configuration.gravityConnection point first internalOut middle *
            varied second middle internalIn -
          varied second internalOut middle *
            configuration.gravityConnection point first middle internalIn -
          configuration.gravityConnection point second internalOut middle *
            varied first middle internalIn)

def lorentzConnectionAlgebraicCurvatureDirection
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) :
    PhysicalBivector :=
  lorentzConnectionAlgebraicCurvatureVariation configuration
    (fun _ => direction) point

theorem lorentzConnectionLinearCurvatureVariation_eq_parts
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (point : BasePoint) :
    lorentzConnectionLinearCurvatureVariation configuration variation point =
      lorentzConnectionExteriorDerivativeVariation variation point +
        lorentzConnectionAlgebraicCurvatureVariation configuration variation
          point := by
  funext internalPair spacetimePair
  unfold lorentzConnectionLinearCurvatureVariation
    lorentzConnectionExteriorDerivativeVariation
    lorentzConnectionAlgebraicCurvatureVariation
  dsimp only
  simp only [Pi.add_apply]
  ring

theorem lorentzConnectionExteriorDerivativeVariation_scalarTimes
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    lorentzConnectionExteriorDerivativeVariation
        (scalarTimesLorentzConnectionVariation direction variation) point =
      ∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection •
          lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction := by
  funext internalPair spacetimePair
  unfold lorentzConnectionExteriorDerivativeVariation
    lorentzConnectionExteriorDerivativeDirection
  dsimp only
  rw [lorentzConnectionVariationDerivative_scalarTimes,
    lorentzConnectionVariationDerivative_scalarTimes]
  fin_cases spacetimePair <;>
    simp [Fin.sum_univ_four, pairFirst, pairSecond] <;> ring

theorem lorentzConnectionAlgebraicCurvatureVariation_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    lorentzConnectionAlgebraicCurvatureVariation configuration
        (scalarTimesLorentzConnectionVariation direction variation) point =
      variation point •
        lorentzConnectionAlgebraicCurvatureDirection configuration direction
          point := by
  funext internalPair spacetimePair
  unfold lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  dsimp only
  rw [scalarTimesLorentzConnectionVariation_apply,
    lorentzSkewConnectionOfBivectorOneForm_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  ring

theorem lorentzConnectionLinearCurvatureVariation_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    lorentzConnectionLinearCurvatureVariation configuration
        (scalarTimesLorentzConnectionVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection •
          lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) +
      variation point •
        lorentzConnectionAlgebraicCurvatureDirection configuration direction
          point := by
  rw [lorentzConnectionLinearCurvatureVariation_eq_parts,
    lorentzConnectionExteriorDerivativeVariation_scalarTimes,
    lorentzConnectionAlgebraicCurvatureVariation_scalarTimes]

theorem holonomicMatterLorentzConnectionVariation_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicMatterLorentzConnectionVariation configuration
        (scalarTimesLorentzConnectionVariation direction variation) point =
      variation point •
        holonomicMatterLorentzConnectionVariation configuration
          (fun _ => direction) point := by
  funext formDirection
  unfold holonomicMatterLorentzConnectionVariation
  rw [scalarTimesLorentzConnectionVariation_apply,
    lorentzSkewConnectionOfBivectorOneForm_smul,
    diracSpinConnectionLift_real_smul,
    diracMatrixMatterAction_real_smul_matrix_local]
  rfl

theorem gravityBFCurvatureIncrementDensity_add
    (coframe : LorentzianCoframe) (auxiliary first second : PhysicalBivector) :
    gravityBFCurvatureIncrementDensity coframe auxiliary (first + second) =
      gravityBFCurvatureIncrementDensity coframe auxiliary first +
        gravityBFCurvatureIncrementDensity coframe auxiliary second := by
  unfold gravityBFCurvatureIncrementDensity
  rw [gravitySpacetimeHodge_add, gravityCoframePairing_add_right]

theorem gravityBFCurvatureIncrementDensity_smul
    (coframe : LorentzianCoframe) (auxiliary variation : PhysicalBivector)
    (parameter : ℝ) :
    gravityBFCurvatureIncrementDensity coframe auxiliary
        (parameter • variation) =
      parameter * gravityBFCurvatureIncrementDensity coframe auxiliary
        variation := by
  unfold gravityBFCurvatureIncrementDensity
  rw [gravitySpacetimeHodge_smul, gravityCoframePairing_smul_right]

def gravityBFCurvatureIncrementLinear
    (coframe : LorentzianCoframe)
    (auxiliary : PhysicalBivector) : PhysicalBivector →ₗ[ℝ] ℝ where
  toFun := fun variation =>
    gravityBFCurvatureIncrementDensity coframe auxiliary variation
  map_add' := gravityBFCurvatureIncrementDensity_add _ _
  map_smul' := by
    intro parameter variation
    simpa [smul_eq_mul] using
      gravityBFCurvatureIncrementDensity_smul coframe auxiliary variation
        parameter

@[simp] theorem gravityBFCurvatureIncrementLinear_apply
    (coframe : LorentzianCoframe) (auxiliary variation : PhysicalBivector) :
    gravityBFCurvatureIncrementLinear coframe auxiliary variation =
      gravityBFCurvatureIncrementDensity coframe auxiliary variation :=
  rfl

theorem gravityBFCurvatureIncrementDensity_sum_add_smul
    {Index : Type*} [Fintype Index]
    (coframe : LorentzianCoframe) (auxiliary : PhysicalBivector)
    (coefficient : Index → ℝ) (direction : Index → PhysicalBivector)
    (parameter : ℝ) (residual : PhysicalBivector) :
    gravityBFCurvatureIncrementDensity coframe auxiliary
        ((∑ index : Index, coefficient index • direction index) +
          parameter • residual) =
      (∑ index : Index,
        coefficient index * gravityBFCurvatureIncrementDensity coframe
          auxiliary (direction index)) +
        parameter * gravityBFCurvatureIncrementDensity coframe auxiliary
          residual := by
  change gravityBFCurvatureIncrementLinear coframe auxiliary
      ((∑ index : Index, coefficient index • direction index) +
        parameter • residual) = _
  rw [map_add, map_sum, map_smul]
  simp only [gravityBFCurvatureIncrementLinear_apply, smul_eq_mul, map_smul]

theorem matterGaugeConnectionFirstVariationDensity_real_smul_local
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity source chart point field
        (parameter • variation) =
      parameter * matterGaugeConnectionFirstVariationDensity source chart
        point field variation := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [matterGaugeKineticSum_real_smul]
  have vectorEquality :
      Complex.I •
          (parameter • matterGaugeKineticSum source chart point field variation) =
        parameter •
          (Complex.I •
            matterGaugeKineticSum source chart point field variation) := by
    change Complex.I •
        ((parameter : ℂ) •
          matterGaugeKineticSum source chart point field variation) =
      (parameter : ℂ) •
        (Complex.I •
          matterGaugeKineticSum source chart point field variation)
    module
  rw [vectorEquality, matterDualFrameRelative_real_smul]
  simp [Complex.mul_re]

def lorentzConnectionAlgebraicSpinCurrentCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) : ℝ :=
  lorentzConnectionFirstVariationDensity source 0 point
    (toContinuumPointField configuration point)
    (lorentzConnectionAlgebraicCurvatureDirection configuration direction
      point)
    (holonomicMatterLorentzConnectionVariation configuration
      (fun _ => direction) point)

theorem holonomicLorentzConnectionFirstVariationDensity_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicLorentzConnectionFirstVariationDensity source 0 configuration
        (scalarTimesLorentzConnectionVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          lorentzConnectionBFDifferentialMomentum configuration
            (lorentzConnectionExteriorDerivativeDirection derivativeDirection
              direction) point) +
        variation point *
          lorentzConnectionAlgebraicSpinCurrentCoefficient source configuration
            direction point := by
  unfold holonomicLorentzConnectionFirstVariationDensity
  rw [lorentzConnectionLinearCurvatureVariation_scalarTimes,
    holonomicMatterLorentzConnectionVariation_scalarTimes]
  unfold lorentzConnectionFirstVariationDensity
  rw [gravityBFCurvatureIncrementDensity_sum_add_smul,
    matterGaugeConnectionFirstVariationDensity_real_smul_local]
  simp_rw [lorentzConnectionBFDifferentialMomentum_eq_density configuration
    nondegenerate]
  unfold lorentzConnectionAlgebraicSpinCurrentCoefficient
    lorentzConnectionFirstVariationDensity
  rw [show (toContinuumPointField configuration point).coframe =
      configuration.coframe point by rfl]
  rw [show (toContinuumPointField configuration point).gravityAuxiliary =
      configuration.gravityAuxiliary point by rfl]
  have sumEquality :
      generatedVolumeDensity (toContinuumPointField configuration point) *
          (∑ derivativeDirection : LorentzianIndex,
            fieldDirectionalDerivative variation point derivativeDirection *
              gravityBFCurvatureIncrementDensity
                (configuration.coframe point)
                (configuration.gravityAuxiliary point)
                (lorentzConnectionExteriorDerivativeDirection
                  derivativeDirection direction)) =
        ∑ derivativeDirection : LorentzianIndex,
          fieldDirectionalDerivative variation point derivativeDirection *
            (generatedVolumeDensity
                (toContinuumPointField configuration point) *
              gravityBFCurvatureIncrementDensity
                (configuration.coframe point)
                (configuration.gravityAuxiliary point)
                (lorentzConnectionExteriorDerivativeDirection
                  derivativeDirection direction)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro derivativeDirection _
    ring
  rw [← sumEquality]
  ring

theorem lorentzConnectionAlgebraicCurvatureDirection_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      lorentzConnectionAlgebraicCurvatureDirection configuration direction
        point := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  have connectionContinuous : ∀
      (formDirection internalOut internalIn : LorentzianIndex),
      Continuous fun point =>
        configuration.gravityConnection point formDirection internalOut
          internalIn := fun formDirection internalOut internalIn =>
    (smooth.2.1 formDirection internalOut internalIn).continuous
  unfold lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  dsimp only
  fun_prop

theorem holonomicLorentzConnectionAlgebraicBFDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      gravityBFCurvatureIncrementDensity
        (configuration.coframe point)
        (configuration.gravityAuxiliary point)
        (lorentzConnectionAlgebraicCurvatureDirection configuration direction
          point) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have auxiliaryContinuous :=
    holonomicGravityAuxiliary_continuous configuration smooth
  have algebraicContinuous :=
    lorentzConnectionAlgebraicCurvatureDirection_continuous configuration
      smooth direction
  have hodgeAlgebraicContinuous :=
    holonomicGravitySpacetimeHodge_apply_continuous configuration smooth
      nondegenerate _ algebraicContinuous
  have pairingContinuous := gravityCoframePairing_apply_continuous
    configuration.coframe coframeContinuous configuration.gravityAuxiliary
      (fun point => gravitySpacetimeHodge (configuration.coframe point)
        (lorentzConnectionAlgebraicCurvatureDirection configuration direction
          point))
      auxiliaryContinuous hodgeAlgebraicContinuous
  simpa [gravityBFCurvatureIncrementDensity] using pairingContinuous

theorem holonomicMatterLorentzConstantDirection_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (holonomicMatterLorentzConnectionVariation configuration
          (fun _ => direction) point formDirection) := by
  have matterContinuous : Continuous fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1.continuous
  unfold holonomicMatterLorentzConnectionVariation
  exact diracMatrixMatterCoordinate_raw_apply_continuous _ _ continuous_const
    matterContinuous

theorem holonomicMatterLorentzConstantDirectionKineticSummand_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            formDirection)
          (holonomicMatterLorentzConnectionVariation configuration
            (fun _ => direction) point formDirection)) :=
  diracMatrixMatterCoordinate_raw_apply_continuous _ _
    (holonomicInverseCoframeDiracGamma_continuous configuration smooth
      nondegenerate formDirection)
    (holonomicMatterLorentzConstantDirection_coordinate_continuous
      configuration smooth direction formDirection)

theorem holonomicMatterLorentzConstantDirectionKineticSum_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterLorentzConnectionVariation configuration
            (fun _ => direction) point)) := by
  have sumContinuous : Continuous fun point =>
      ∑ formDirection : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (holonomicMatterLorentzConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
    apply continuous_finsetSum
    intro formDirection _
    exact holonomicMatterLorentzConstantDirectionKineticSummand_continuous
      configuration smooth nondegenerate direction formDirection
  exact sumContinuous.congr fun point => by
    unfold matterGaugeKineticSum matterDerivativeFrameRelative
    simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]

theorem holonomicMatterLorentzConstantDirectionVector_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeConnectionVariationVector source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterLorentzConnectionVariation configuration
            (fun _ => direction) point)) := by
  have kineticContinuous :=
    holonomicMatterLorentzConstantDirectionKineticSum_continuous source
      configuration smooth nondegenerate direction
  have coordinateContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterLorentzConnectionVariation configuration
            (fun _ => direction) point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticContinuous).congr fun point => rfl
  unfold matterGaugeConnectionVariationVector
  exact coordinateContinuous.congr fun point => by rw [map_smul]

theorem holonomicMatterLorentzAlgebraicDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      matterGaugeConnectionFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicMatterLorentzConnectionVariation configuration
          (fun _ => direction) point) := by
  let vector := fun point =>
    matterGaugeConnectionVariationVector source 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterLorentzConnectionVariation configuration
        (fun _ => direction) point)
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    holonomicMatterLorentzConstantDirectionVector_continuous source
      configuration smooth nondegenerate direction
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

theorem lorentzConnectionAlgebraicSpinCurrentCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous
      (lorentzConnectionAlgebraicSpinCurrentCoefficient source configuration
        direction) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      abs (Matrix.det (configuration.coframe point)) :=
    coframeContinuous.matrix_det.abs
  have bfContinuous :=
    holonomicLorentzConnectionAlgebraicBFDensity_continuous configuration
      smooth nondegenerate direction
  have matterContinuous :=
    holonomicMatterLorentzAlgebraicDensity_continuous source configuration
      smooth nondegenerate direction
  unfold lorentzConnectionAlgebraicSpinCurrentCoefficient
    lorentzConnectionFirstVariationDensity generatedVolumeDensity
  exact volumeContinuous.mul (bfContinuous.add matterContinuous)

def lorentzConnectionBFDifferentialMomentumDivergence
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) : ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (lorentzConnectionBFDifferentialMomentum configuration
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          direction)) point derivativeDirection

def lorentzConnectionEulerLagrangeCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm) (point : BasePoint) : ℝ :=
  lorentzConnectionAlgebraicSpinCurrentCoefficient source configuration
      direction point -
    lorentzConnectionBFDifferentialMomentumDivergence configuration direction
      point

theorem lorentzConnectionBFDifferentialMomentumDivergence_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous
      (lorentzConnectionBFDifferentialMomentumDivergence configuration
        direction) := by
  unfold lorentzConnectionBFDifferentialMomentumDivergence
  apply continuous_finsetSum
  intro derivativeDirection _
  have momentumSmooth :=
    lorentzConnectionBFDifferentialMomentum_contDiff configuration smooth
      nondegenerate
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection
        direction)
  have derivativeContinuous : Continuous fun point =>
      fderiv ℝ
        (lorentzConnectionBFDifferentialMomentum configuration
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction)) point := momentumSmooth.continuous_fderiv (by simp)
  unfold fieldDirectionalDerivative
  exact derivativeContinuous.clm_apply continuous_const

theorem lorentzConnectionEulerLagrangeCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous
      (lorentzConnectionEulerLagrangeCoefficient source configuration
        direction) :=
  (lorentzConnectionAlgebraicSpinCurrentCoefficient_continuous source
    configuration smooth nondegenerate direction).sub
      (lorentzConnectionBFDifferentialMomentumDivergence_continuous
        configuration smooth nondegenerate direction)

theorem compactScalar_mul_continuous_integrable_local
    (variation : CompactlySupportedSmoothVariation ℝ)
    (background : BasePoint → ℝ)
    (backgroundContinuous : Continuous background) :
    Integrable fun point => variation point * background point := by
  have productContinuous : Continuous fun point =>
      variation point * background point :=
    variation.smooth.continuous.mul backgroundContinuous
  have productCompact : HasCompactSupport fun point =>
      variation point * background point := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]
  exact productContinuous.integrable_of_hasCompactSupport productCompact

theorem compactScalarDerivative_mul_continuous_integrable_local
    (variation : CompactlySupportedSmoothVariation ℝ)
    (background : BasePoint → ℝ)
    (backgroundContinuous : Continuous background)
    (derivativeDirection : LorentzianIndex) :
    Integrable fun point =>
      fieldDirectionalDerivative variation point derivativeDirection *
        background point := by
  have derivativeContinuous : Continuous fun point =>
      fieldDirectionalDerivative variation point derivativeDirection := by
    simpa [fieldDirectionalDerivative] using
      compactVariation_directionalDerivative_continuous variation
        derivativeDirection
  have productContinuous := derivativeContinuous.mul backgroundContinuous
  have derivativeCompact : HasCompactSupport fun point =>
      fieldDirectionalDerivative variation point derivativeDirection := by
    simpa [fieldDirectionalDerivative] using
      compactVariation_directionalDerivative_compact variation
        derivativeDirection
  have productCompact : HasCompactSupport fun point =>
      fieldDirectionalDerivative variation point derivativeDirection *
        background point := by
    have derivativeEventually := derivativeCompact
    rw [hasCompactSupport_iff_eventuallyEq] at derivativeEventually ⊢
    filter_upwards [derivativeEventually] with point derivativeZero
    simp [derivativeZero]
  exact productContinuous.integrable_of_hasCompactSupport productCompact

theorem lorentzConnectionBFDifferentialMomentum_integrationByParts
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (derivativeDirection : LorentzianIndex) :
    (∫ point : BasePoint,
      fieldDirectionalDerivative variation point derivativeDirection *
        lorentzConnectionBFDifferentialMomentum configuration
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) point) =
      -(∫ point : BasePoint,
        variation point *
          fieldDirectionalDerivative
            (lorentzConnectionBFDifferentialMomentum configuration
              (lorentzConnectionExteriorDerivativeDirection
                derivativeDirection direction)) point
            derivativeDirection) := by
  have actual := compactSupport_integrationByParts
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (lorentzConnectionBFDifferentialMomentum configuration
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection
        direction)) variation
    (lorentzConnectionBFDifferentialMomentum_contDiff configuration smooth
      nondegenerate
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection
        direction)) derivativeDirection
  simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    fieldDirectionalDerivative, mul_comm] using actual

theorem canonicalLorentzConnectionWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalLorentzConnectionWeakEquation source
      configuration)
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        lorentzConnectionEulerLagrangeCoefficient source configuration
          direction point) = 0 := by
  let momentum := fun derivativeDirection : LorentzianIndex =>
    lorentzConnectionBFDifferentialMomentum configuration
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection
        direction)
  let momentumDerivative := fun derivativeDirection : LorentzianIndex =>
    fun point => fieldDirectionalDerivative (momentum derivativeDirection)
      point derivativeDirection
  let algebraic :=
    lorentzConnectionAlgebraicSpinCurrentCoefficient source configuration
      direction
  have momentumContinuous : ∀ derivativeDirection,
      Continuous (momentum derivativeDirection) := fun derivativeDirection =>
    (lorentzConnectionBFDifferentialMomentum_contDiff configuration smooth
      nondegenerate
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection
        direction)).continuous
  have momentumDerivativeContinuous : ∀ derivativeDirection,
      Continuous (momentumDerivative derivativeDirection) := by
    intro derivativeDirection
    have momentumSmooth :=
      lorentzConnectionBFDifferentialMomentum_contDiff configuration smooth
        nondegenerate
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          direction)
    unfold momentumDerivative momentum fieldDirectionalDerivative
    exact (momentumSmooth.continuous_fderiv (by simp)).clm_apply
      continuous_const
  have derivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point := fun derivativeDirection =>
    compactScalarDerivative_mul_continuous_integrable_local variation
      (momentum derivativeDirection) (momentumContinuous derivativeDirection)
      derivativeDirection
  have derivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      derivativeTermIntegrable derivativeDirection
  have algebraicContinuous : Continuous algebraic :=
    lorentzConnectionAlgebraicSpinCurrentCoefficient_continuous source
      configuration smooth nondegenerate direction
  have algebraicTermIntegrable : Integrable fun point =>
      variation point * algebraic point :=
    compactScalar_mul_continuous_integrable_local variation algebraic
      algebraicContinuous
  have momentumDerivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        variation point * momentumDerivative derivativeDirection point :=
    fun derivativeDirection =>
      compactScalar_mul_continuous_integrable_local variation
        (momentumDerivative derivativeDirection)
        (momentumDerivativeContinuous derivativeDirection)
  have momentumDerivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        variation point * momentumDerivative derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      momentumDerivativeTermIntegrable derivativeDirection
  have weakDirection := weakEquation
    (scalarTimesLorentzConnectionVariation direction variation)
  rw [show (fun point : BasePoint =>
      holonomicLorentzConnectionFirstVariationDensity source 0 configuration
        (scalarTimesLorentzConnectionVariation direction variation) point) =
      fun point =>
        (∑ derivativeDirection : LorentzianIndex,
          fieldDirectionalDerivative variation point derivativeDirection *
            momentum derivativeDirection point) +
          variation point * algebraic point by
    funext point
    exact holonomicLorentzConnectionFirstVariationDensity_scalarTimes source
      configuration nondegenerate direction variation point] at weakDirection
  have integralDerivativeSum :
      (∫ point : BasePoint,
        ∑ derivativeDirection : LorentzianIndex,
          fieldDirectionalDerivative variation point derivativeDirection *
            momentum derivativeDirection point) =
        ∑ derivativeDirection : LorentzianIndex,
          ∫ point : BasePoint,
            fieldDirectionalDerivative variation point derivativeDirection *
              momentum derivativeDirection point := by
    simpa using integral_finsetSum Finset.univ
      (fun derivativeDirection _ => derivativeTermIntegrable derivativeDirection)
  rw [integral_add derivativeSumIntegrable algebraicTermIntegrable,
    integralDerivativeSum] at weakDirection
  have ibp : ∀ derivativeDirection,
      (∫ point : BasePoint,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point) =
        -(∫ point : BasePoint,
          variation point * momentumDerivative derivativeDirection point) := by
    intro derivativeDirection
    exact lorentzConnectionBFDifferentialMomentum_integrationByParts
      configuration smooth nondegenerate direction variation
        derivativeDirection
  simp_rw [ibp] at weakDirection
  have integralMomentumDerivativeSum :
      (∫ point : BasePoint,
        ∑ derivativeDirection : LorentzianIndex,
          variation point * momentumDerivative derivativeDirection point) =
        ∑ derivativeDirection : LorentzianIndex,
          ∫ point : BasePoint,
            variation point * momentumDerivative derivativeDirection point := by
    simpa using integral_finsetSum Finset.univ
      (fun derivativeDirection _ =>
        momentumDerivativeTermIntegrable derivativeDirection)
  have residualFunctionEquality :
      (fun point : BasePoint =>
        variation point *
          lorentzConnectionEulerLagrangeCoefficient source configuration
            direction point) =
      fun point =>
        variation point * algebraic point -
          ∑ derivativeDirection : LorentzianIndex,
            variation point * momentumDerivative derivativeDirection point := by
    funext point
    unfold lorentzConnectionEulerLagrangeCoefficient
      lorentzConnectionBFDifferentialMomentumDivergence
      algebraic momentumDerivative momentum
    rw [mul_sub, Finset.mul_sum]
  rw [residualFunctionEquality,
    integral_sub algebraicTermIntegrable momentumDerivativeSumIntegrable,
    integralMomentumDerivativeSum]
  have rearrangedWeak :
      (∫ point : BasePoint, variation point * algebraic point) -
          ∑ derivativeDirection : LorentzianIndex,
            ∫ point : BasePoint,
              variation point * momentumDerivative derivativeDirection point =
        0 := by
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simpa only [add_comm] using weakDirection
  exact rearrangedWeak

def CanonicalLorentzConnectionPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ direction : LorentzBivectorOneForm,
    lorentzConnectionEulerLagrangeCoefficient source configuration direction =
      0

theorem canonicalLorentzConnectionWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalLorentzConnectionWeakEquation source
      configuration) :
    CanonicalLorentzConnectionPointwiseEquation source configuration := by
  intro direction
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (lorentzConnectionEulerLagrangeCoefficient source configuration direction)
    (lorentzConnectionEulerLagrangeCoefficient_continuous source configuration
      smooth nondegenerate direction)
  intro variation
  exact canonicalLorentzConnectionWeakEquation_direction_integral source
    configuration smooth nondegenerate weakEquation direction variation

end

end SaturationMonoid.PhysicsCore.StageNineLorentzConnectionPointwiseEquation
