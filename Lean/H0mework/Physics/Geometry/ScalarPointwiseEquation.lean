import H0mework.Physics.Exterior.ScalarVariation
import H0mework.Physics.Geometry.FundamentalLemma

/-!
# S9-C3d1: pointwise scalar equation by genuine integration by parts

The primitive scalar variation is specialized to a compact smooth real bump
times an arbitrary direction in the actual scalar-coordinate carrier.  Its
covariant derivative splits into the derivative of the bump and the algebraic
P286 action.  The generated first density therefore splits into differential
momentum and algebraic potential/Yukawa terms.

The dynamic volume, inverse metric, and background scalar covariant derivative
are proved `C∞` directly from the primitive holonomic fields.  Genuine
four-dimensional compact-support integration by parts and the internally
proved fundamental lemma then yield the pointwise directional scalar
Euler--Lagrange equation.  No momentum, regularity, current, field equation,
or supplied certificate is accepted at the theorem mouth.
-/

namespace SaturationMonoid.PhysicsCore.StageNineScalarPointwiseEquation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNinePlebanskiMultiplierVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarVariation
open SU7ExteriorMatterFullVariations
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorBreakingYukawa
open MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 600000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286GaugeConnectionActionVariation.p286CoordinateIndexFintype

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def scalarTimesScalarVariation
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation ScalarCoordinateCarrier where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

@[simp] theorem scalarTimesScalarVariation_apply
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint) :
    scalarTimesScalarVariation direction variation point =
      variation point • direction :=
  rfl

theorem scalarVariationCoordinateDerivative_scalarTimes
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint)
    (derivativeDirection : LorentzianIndex) :
    scalarVariationCoordinateDerivative
        (scalarTimesScalarVariation direction variation) point
        derivativeDirection =
      fieldDirectionalDerivative variation point derivativeDirection •
        direction := by
  have differentiable : DifferentiableAt ℝ
      (variation : BasePoint → ℝ) point :=
    (variation.smooth.differentiable (by simp)).differentiableAt
  unfold scalarVariationCoordinateDerivative fieldDirectionalDerivative
  change
    (fderiv ℝ (fun candidate => variation candidate • direction) point)
        (coordinateDirection derivativeDirection) = _
  rw [fderiv_smul_const differentiable]
  rfl

def holonomicScalarVariationAlgebraicDirection
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) (point : BasePoint)
    (formDirection : LorentzianIndex) : ScalarCoordinateCarrier :=
  scalarMotherLieAction
    (p286LieBlockEmbed (configuration.gaugeConnection point formDirection))
    direction

theorem holonomicScalarVariationCovariantDerivative_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint)
    (formDirection : LorentzianIndex) :
    holonomicScalarVariationCovariantDerivative configuration
        (scalarTimesScalarVariation direction variation) point formDirection =
      fieldDirectionalDerivative variation point formDirection • direction +
        variation point •
          holonomicScalarVariationAlgebraicDirection configuration direction
            point formDirection := by
  unfold holonomicScalarVariationCovariantDerivative
    holonomicScalarVariationAlgebraicDirection
  rw [scalarVariationCoordinateDerivative_scalarTimes]
  simp only [scalarTimesScalarVariation_apply]
  rw [scalarMotherLieAction_real_smul_right]

def scalarVariationDifferentialDirection
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    ScalarCoordinateCarrier :=
  if formDirection = derivativeDirection then direction else 0

theorem holonomicScalarVariationCovariantDerivative_scalarTimes_as_sum
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint) :
    holonomicScalarVariationCovariantDerivative configuration
        (scalarTimesScalarVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection •
          scalarVariationDifferentialDirection direction derivativeDirection) +
        variation point •
          holonomicScalarVariationAlgebraicDirection configuration direction
            point := by
  funext formDirection
  rw [holonomicScalarVariationCovariantDerivative_scalarTimes]
  congr 1
  simp [scalarVariationDifferentialDirection]

theorem scalarWeightedDoubleSum_add_linear
    {First Second : Type*} [Fintype First] [Fintype Second]
    (weight firstLeft firstRight secondLeft secondRight :
      First → Second → ℝ) :
    (∑ first : First, ∑ second : Second,
      weight first second *
        ((firstLeft first second + secondLeft first second) +
          (firstRight first second + secondRight first second))) =
      (∑ first : First, ∑ second : Second,
        weight first second *
          (firstLeft first second + firstRight first second)) +
      (∑ first : First, ∑ second : Second,
        weight first second *
          (secondLeft first second + secondRight first second)) := by
  calc
    _ = ∑ first : First, ∑ second : Second,
        (weight first second *
          (firstLeft first second + firstRight first second) +
        weight first second *
          (secondLeft first second + secondRight first second)) := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib]

/-- Scaled form of `scalarWeightedDoubleSum_add_linear`.  Keeping the outer
coefficient inside the algebraic producer avoids downstream rewrite matching
against semireducible matrix-coordinate expressions. -/
theorem scalarWeightedDoubleSum_add_linear_scaled
    {First Second : Type*} [Fintype First] [Fintype Second]
    (volume scale : ℝ)
    (weight firstLeft firstRight secondLeft secondRight :
      First → Second → ℝ) :
    volume * (scale *
      ∑ first : First, ∑ second : Second,
        weight first second *
          ((firstLeft first second + secondLeft first second) +
            (firstRight first second + secondRight first second))) =
      volume * (scale *
        ∑ first : First, ∑ second : Second,
          weight first second *
            (firstLeft first second + firstRight first second)) +
      volume * (scale *
        ∑ first : First, ∑ second : Second,
          weight first second *
            (secondLeft first second + secondRight first second)) := by
  rw [scalarWeightedDoubleSum_add_linear]
  ring

theorem scalarWeightedDoubleSum_real_linear
    {First Second : Type*} [Fintype First] [Fintype Second]
    (weight left right : First → Second → ℝ) (parameter : ℝ) :
    (∑ first : First, ∑ second : Second,
      weight first second *
        (parameter * left first second + parameter * right first second)) =
      parameter *
        (∑ first : First, ∑ second : Second,
          weight first second *
            (left first second + right first second)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem scalarKineticFirstVariationDensity_add
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (first second : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
        (first + second) =
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
          first +
        scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
          second := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [scalarFrameRelativeCovariantDerivative_add]
  simp only [Pi.add_apply, scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  simp_rw [← Matrix.of_symm_apply]
  rw [scalarWeightedDoubleSum_add_linear]
  ring

theorem scalarKineticFirstVariationDensity_real_smul
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) (parameter : ℝ)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
        (parameter • variation) =
      parameter * scalarGaugeConnectionKineticFirstVariationDensity source 0
        point field variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [scalarFrameRelativeCovariantDerivative_real_smul]
  simp only [Pi.smul_apply,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp_rw [← Matrix.of_symm_apply]
  rw [scalarWeightedDoubleSum_real_linear]
  ring

def scalarKineticFirstVariationLinear
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    (LorentzianIndex → ScalarCoordinateCarrier) →ₗ[ℝ] ℝ where
  toFun := scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
  map_add' := scalarKineticFirstVariationDensity_add source point field
  map_smul' := by
    intro parameter variation
    simpa [smul_eq_mul] using
      scalarKineticFirstVariationDensity_real_smul source point field parameter
        variation

@[simp] theorem scalarKineticFirstVariationLinear_apply
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarKineticFirstVariationLinear source point field variation =
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
        variation :=
  rfl

theorem scalarPotentialFirstVariation_real_smul
    (source : SmoothUnifiedSource) (field : StageNineContinuumPointField)
    (parameter : ℝ) (variation : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation source field (parameter • variation) =
      parameter * scalarPotentialFirstVariation source field variation := by
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
  change 2 * scalarCoordinatePairingRe
      (field.scalar - sourceGeneratedVacuumCoordinates source)
      (parameter • variation) =
    parameter *
      (2 * scalarCoordinatePairingRe
        (field.scalar - sourceGeneratedVacuumCoordinates source) variation)
  rw [scalarCoordinatePairingRe_real_smul_right]
  ring

theorem scalarYukawaFirstVariationDensity_real_smul
    (field : StageNineContinuumPointField) (parameter : ℝ)
    (variation : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity field (parameter • variation) =
      parameter * scalarYukawaFirstVariationDensity field variation := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  rw [show scalarCoordinateEquiv.symm (parameter • variation) =
      (parameter : ℂ) • scalarCoordinateEquiv.symm variation by
    change scalarCoordinateEquiv.symm ((parameter : ℂ) • variation) = _
    rw [map_smul]]
  rw [chiralExteriorYukawaAction_smul, LinearMap.smul_apply, map_smul]
  simp [Complex.mul_re]

def scalarDifferentialMomentum
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    scalarGaugeConnectionKineticFirstVariationDensity source 0 point
      (toContinuumPointField configuration point)
      (scalarVariationDifferentialDirection direction derivativeDirection)

def scalarAlgebraicDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicScalarVariationAlgebraicDirection configuration direction
          point) -
      scalarPotentialFirstVariation source
        (toContinuumPointField configuration point) direction +
      scalarYukawaFirstVariationDensity
        (toContinuumPointField configuration point) direction)

theorem holonomicScalarFirstVariationDensity_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint) :
    holonomicScalarFirstVariationDensity source configuration
        (scalarTimesScalarVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          scalarDifferentialMomentum source configuration direction
            derivativeDirection point) +
        variation point *
          scalarAlgebraicDirectionalCoefficient source configuration direction
            point := by
  unfold holonomicScalarFirstVariationDensity scalarFirstVariationDensity
    scalarDifferentialMomentum scalarAlgebraicDirectionalCoefficient
  rw [holonomicScalarVariationCovariantDerivative_scalarTimes_as_sum]
  change
    generatedVolumeDensity (toContinuumPointField configuration point) *
      (scalarKineticFirstVariationLinear source point
          (toContinuumPointField configuration point)
          ((∑ derivativeDirection : LorentzianIndex,
            fieldDirectionalDerivative variation point derivativeDirection •
              scalarVariationDifferentialDirection direction
                derivativeDirection) +
            variation point •
              holonomicScalarVariationAlgebraicDirection configuration
                direction point) -
        scalarPotentialFirstVariation source
          (toContinuumPointField configuration point)
          (scalarTimesScalarVariation direction variation point) +
        scalarYukawaFirstVariationDensity
          (toContinuumPointField configuration point)
          (scalarTimesScalarVariation direction variation point)) = _
  rw [map_add, map_sum]
  simp_rw [map_smul]
  simp only [scalarKineticFirstVariationLinear_apply, smul_eq_mul,
    scalarTimesScalarVariation_apply,
    scalarPotentialFirstVariation_real_smul,
    scalarYukawaFirstVariationDensity_real_smul]
  calc
    _ = generatedVolumeDensity (toContinuumPointField configuration point) *
          (∑ derivativeDirection : LorentzianIndex,
            fieldDirectionalDerivative variation point derivativeDirection *
              scalarGaugeConnectionKineticFirstVariationDensity source 0 point
                (toContinuumPointField configuration point)
                (scalarVariationDifferentialDirection direction
                  derivativeDirection)) +
        variation point *
          (generatedVolumeDensity (toContinuumPointField configuration point) *
            (scalarGaugeConnectionKineticFirstVariationDensity source 0 point
                (toContinuumPointField configuration point)
                (holonomicScalarVariationAlgebraicDirection configuration
                  direction point) -
              scalarPotentialFirstVariation source
                (toContinuumPointField configuration point) direction +
              scalarYukawaFirstVariationDensity
                (toContinuumPointField configuration point) direction)) := by
      ring
    _ = _ := by
      apply congrArg₂ (fun left right : ℝ => left + right)
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro derivativeDirection _
        ring
      · rfl

/-! ## Smooth scalar differential momentum -/

theorem scalarHolonomicCoframe_det_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point => Matrix.det (configuration.coframe point) := by
  rw [show (fun point => Matrix.det (configuration.coframe point)) =
      fun point => ∑ σ : Equiv.Perm LorentzianIndex,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ index : LorentzianIndex,
            configuration.coframe point (σ index) index by
    funext point
    exact Matrix.det_apply' _]
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  exact smooth.1 (permutation index) index

theorem scalarHolonomicGeneratedVolumeDensity_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ fun point =>
      abs (Matrix.det (configuration.coframe point)) :=
  (scalarHolonomicCoframe_det_contDiff configuration smooth).abs nondegenerate

theorem holonomicLorentzianMetric_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point =>
      lorentzianMetricOfCoframe (configuration.coframe point) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  unfold lorentzianMetricOfCoframe
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiff.sum
  intro internalRight _
  apply ContDiff.mul
  · apply ContDiff.sum
    intro internalLeft _
    exact (smooth.1 internalLeft row).mul contDiff_const
  · exact smooth.1 internalRight column

theorem holonomicLorentzianMetric_det_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point =>
      Matrix.det
        (lorentzianMetricOfCoframe (configuration.coframe point)) := by
  let metric := fun point =>
    lorentzianMetricOfCoframe (configuration.coframe point)
  have metricSmooth : ContDiff ℝ ∞ metric :=
    holonomicLorentzianMetric_contDiff configuration smooth
  rw [show (fun point => Matrix.det (metric point)) =
      fun point => ∑ σ : Equiv.Perm LorentzianIndex,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ index : LorentzianIndex, metric point (σ index) index by
    funext point
    exact Matrix.det_apply' _]
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  exact contDiff_pi.mp (contDiff_pi.mp metricSmooth (permutation index)) index

theorem holonomicLorentzianMetric_adjugate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point =>
      (lorentzianMetricOfCoframe
        (configuration.coframe point)).adjugate := by
  let metric := fun point =>
    lorentzianMetricOfCoframe (configuration.coframe point)
  have metricSmooth : ContDiff ℝ ∞ metric :=
    holonomicLorentzianMetric_contDiff configuration smooth
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  rw [show (fun point => (metric point).adjugate row column) =
      fun point => Matrix.det
        ((metric point).updateRow column (Pi.single row 1)) by
    funext point
    exact Matrix.adjugate_apply _ _ _]
  rw [show (fun point => Matrix.det
      ((metric point).updateRow column (Pi.single row 1))) =
      fun point => ∑ σ : Equiv.Perm LorentzianIndex,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ index : LorentzianIndex,
            (metric point).updateRow column
              (Pi.single row 1) (σ index) index by
    funext point
    exact Matrix.det_apply' _]
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  by_cases updated : permutation index = column
  · rw [show (fun point : BasePoint =>
        (metric point).updateRow column
          (Pi.single row (1 : ℝ)) (permutation index) index) =
      fun _ : BasePoint => if index = row then (1 : ℝ) else 0 by
        funext point
        simp [Matrix.updateRow_apply, updated, Pi.single_apply]]
    exact contDiff_const
  · simpa [Matrix.updateRow_apply, updated] using
      contDiff_pi.mp (contDiff_pi.mp metricSmooth (permutation index)) index

theorem holonomicLorentzianMetric_inv_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹ := by
  rw [show (fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹) =
      fun point =>
        (Matrix.det
          (lorentzianMetricOfCoframe
            (configuration.coframe point)))⁻¹ •
          (lorentzianMetricOfCoframe
            (configuration.coframe point)).adjugate by
    funext point
    rw [Matrix.inv_def, Ring.inverse_eq_inv]]
  exact (holonomicLorentzianMetric_det_contDiff configuration smooth).inv
      (fun point =>
        PointwiseLorentzianCoframeJet.metric_det_ne_zero_of_coframe
          { coframe := configuration.coframe point, derivative := 0 }
          (nondegenerate point)) |>.smul
        (holonomicLorentzianMetric_adjugate_contDiff configuration smooth)

theorem holonomicScalarCoordinateDerivative_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      fieldDirectionalDerivative configuration.scalar point direction := by
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry
        (fun _ : BasePoint => configuration.scalar)) := by
    exact scalarSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ configuration.scalar point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv (contDiff_id : ContDiff ℝ ∞
        (fun point : BasePoint => point)) (by simp)
  unfold fieldDirectionalDerivative
  exact derivativeSmooth.clm_apply contDiff_const

theorem holonomicScalarP286Action_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      scalarMotherLieAction
        (p286LieBlockEmbed (configuration.gaugeConnection point direction))
        (configuration.scalar point) := by
  have gaugeCoordinateSmooth : ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (configuration.gaugeConnection point direction) :=
    smooth.2.2.2.2.1 direction
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have outerSmooth : ContDiff ℝ ∞ fun point =>
      scalarP286ActionBilinear.toContinuousBilinearMap
        (p286CoordinateEquiv (configuration.gaugeConnection point direction)) :=
    contDiff_const.clm_apply gaugeCoordinateSmooth
  rw [show (fun point =>
      scalarMotherLieAction
        (p286LieBlockEmbed (configuration.gaugeConnection point direction))
        (configuration.scalar point)) =
      fun point =>
        scalarP286ActionBilinear
          (p286CoordinateEquiv
            (configuration.gaugeConnection point direction))
          (configuration.scalar point) by
    funext point
    change
      scalarMotherLieAction
          (p286LieBlockEmbed (configuration.gaugeConnection point direction))
          (configuration.scalar point) =
        scalarMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (configuration.gaugeConnection point direction))))
          (configuration.scalar point)
    rw [p286CoordinateEquiv.symm_apply_apply]]
  exact outerSmooth.clm_apply scalarSmooth

theorem holonomicScalarCovariantDerivative_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      holonomicScalarCovariantDerivative configuration point direction := by
  unfold holonomicScalarCovariantDerivative
  exact (holonomicScalarCoordinateDerivative_contDiff configuration smooth
    direction).add
      (holonomicScalarP286Action_contDiff configuration smooth direction)

theorem scalarCoordinatePairingRe_apply_contDiff
    (first second : BasePoint → ScalarCoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ fun point =>
      scalarCoordinatePairingRe (first point) (second point) := by
  have outerSmooth : ContDiff ℝ ∞ fun point =>
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap
        (first point) :=
    contDiff_const.clm_apply firstSmooth
  exact outerSmooth.clm_apply secondSmooth

theorem scalarDifferentialMomentum_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiff ℝ ∞
      (scalarDifferentialMomentum source configuration direction
        derivativeDirection) := by
  have volumeSmooth := scalarHolonomicGeneratedVolumeDensity_contDiff
    configuration smooth nondegenerate
  have metricInverseSmooth := holonomicLorentzianMetric_inv_contDiff
    configuration smooth nondegenerate
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [generatedVolumeDensity, toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  apply volumeSmooth.mul
  apply contDiff_const.mul
  apply ContDiff.sum
  intro first _
  apply ContDiff.sum
  intro second _
  have metricEntrySmooth : ContDiff ℝ ∞ fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹
        first second :=
    contDiff_pi.mp (contDiff_pi.mp metricInverseSmooth first) second
  apply metricEntrySmooth.mul
  apply ContDiff.add
  · exact scalarCoordinatePairingRe_apply_contDiff _ _ contDiff_const
      (holonomicScalarCovariantDerivative_contDiff configuration smooth second)
  · exact scalarCoordinatePairingRe_apply_contDiff _ _
      (holonomicScalarCovariantDerivative_contDiff configuration smooth first)
      contDiff_const

/-! ## Algebraic coefficient and pointwise residual -/

theorem holonomicScalarVariationAlgebraicDirection_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : ScalarCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      holonomicScalarVariationAlgebraicDirection configuration direction point
        formDirection := by
  have gaugeCoordinateContinuous : Continuous fun point =>
      p286CoordinateEquiv (configuration.gaugeConnection point formDirection) :=
    (smooth.2.2.2.2.1 formDirection).continuous
  have actual := scalarP286Action_apply_continuous
    (fun point => p286CoordinateEquiv
      (configuration.gaugeConnection point formDirection))
    (fun _ : BasePoint => direction)
    gaugeCoordinateContinuous continuous_const
  unfold holonomicScalarVariationAlgebraicDirection
  exact actual.congr fun point => by
    change
      scalarMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (configuration.gaugeConnection point formDirection))))
          direction = _
    rw [p286CoordinateEquiv.symm_apply_apply]

theorem scalarAlgebraicKineticDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : ScalarCoordinateCarrier) :
    Continuous fun point =>
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicScalarVariationAlgebraicDirection configuration direction
          point) := by
  have metricInverseContinuous :=
    (holonomicLorentzianMetric_inv_contDiff configuration smooth
      nondegenerate).continuous
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField, scalarFrameRelativeCoordinates_zeroChart]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro first _
  apply continuous_finsetSum
  intro second _
  have metricEntryContinuous : Continuous fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹
        first second :=
    (continuous_apply second).comp
      ((continuous_apply first).comp metricInverseContinuous)
  apply metricEntryContinuous.mul
  apply Continuous.add
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarVariationAlgebraicDirection_continuous configuration
        smooth direction first)
      (holonomicScalarCovariantDerivative_contDiff configuration smooth
        second).continuous
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarCovariantDerivative_contDiff configuration smooth
        first).continuous
      (holonomicScalarVariationAlgebraicDirection_continuous configuration
        smooth direction second)

theorem scalarPotentialConstantDirection_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : ScalarCoordinateCarrier) :
    Continuous fun point =>
      scalarPotentialFirstVariation source
        (toContinuumPointField configuration point) direction := by
  have scalarContinuous : Continuous configuration.scalar :=
    smooth.2.2.2.2.2.2.1.continuous
  have pairingContinuous := scalarCoordinatePairingRe_apply_continuous _ _
    (scalarContinuous.sub
      (continuous_const : Continuous
        (fun _ : BasePoint => sourceGeneratedVacuumCoordinates source)))
    (continuous_const : Continuous (fun _ : BasePoint => direction))
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
    scalarCoordinateRealPairing
  simp only [toContinuumPointField]
  exact ((continuous_const : Continuous (fun _ : BasePoint => (2 : ℝ))).mul
    pairingContinuous).congr fun point => by
      simp only [Pi.mul_apply, Pi.sub_apply, scalarCoordinatePairingRe]

theorem scalarYukawaConstantDirectionVector_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : ScalarCoordinateCarrier) :
    Continuous fun point =>
      matterCoordinateEquiv
        (scalarYukawaVariationVector
          (toContinuumPointField configuration point) direction) := by
  have actual := scalarVariationYukawaCoordinate_apply_continuous
    (fun _ : BasePoint => direction)
    (fun point => matterCoordinateEquiv (configuration.matter point))
    continuous_const smooth.2.2.2.2.2.2.2.1.continuous
  unfold scalarYukawaVariationVector
  exact actual.congr fun point => by
    simp only [toContinuumPointField]
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) = _
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem scalarYukawaConstantDirectionDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : ScalarCoordinateCarrier) :
    Continuous fun point =>
      scalarYukawaFirstVariationDensity
        (toContinuumPointField configuration point) direction := by
  let vector := fun point =>
    scalarYukawaVariationVector (toContinuumPointField configuration point)
      direction
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    scalarYukawaConstantDirectionVector_coordinate_continuous configuration
      smooth direction
  have pairingSumContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply continuous_finsetSum
    intro index _
    have vectorEntryContinuous : Continuous fun point =>
        matterCoordinateEquiv (vector point) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp
          vectorCoordinateContinuous
    have dualEntryContinuous : Continuous fun point =>
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) :=
      (smooth.2.2.2.2.2.2.2.2 index).continuous
    exact vectorEntryContinuous.mul dualEntryContinuous
  have dualPairingContinuous : Continuous fun point =>
      configuration.conjugateMatter point (vector point) := by
    rw [show (fun point =>
        configuration.conjugateMatter point (vector point)) =
      fun point => ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
      funext point
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        matterDual_coordinate_expansion (configuration.conjugateMatter point)
          (matterCoordinateEquiv (vector point))]
    exact pairingSumContinuous
  unfold scalarYukawaFirstVariationDensity
  exact (Complex.continuous_re.comp dualPairingContinuous).congr fun point => by
    simp only [Function.comp_apply, toContinuumPointField, vector]

theorem scalarAlgebraicDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : ScalarCoordinateCarrier) :
    Continuous
      (scalarAlgebraicDirectionalCoefficient source configuration direction) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have kineticContinuous := scalarAlgebraicKineticDensity_continuous source
    configuration smooth nondegenerate direction
  have potentialContinuous := scalarPotentialConstantDirection_continuous source
    configuration smooth direction
  have yukawaContinuous := scalarYukawaConstantDirectionDensity_continuous
    configuration smooth direction
  unfold scalarAlgebraicDirectionalCoefficient
  exact volumeContinuous.mul
    ((kineticContinuous.sub potentialContinuous).add yukawaContinuous)

def scalarDifferentialMomentumDivergence
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) (point : BasePoint) : ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (scalarDifferentialMomentum source configuration direction
        derivativeDirection) point derivativeDirection

def scalarEulerLagrangeDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) (point : BasePoint) : ℝ :=
  scalarAlgebraicDirectionalCoefficient source configuration direction point -
    scalarDifferentialMomentumDivergence source configuration direction point

theorem scalarDifferentialMomentumDivergence_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : ScalarCoordinateCarrier) :
    Continuous
      (scalarDifferentialMomentumDivergence source configuration direction) := by
  unfold scalarDifferentialMomentumDivergence
  apply continuous_finsetSum
  intro derivativeDirection _
  have momentumSmooth := scalarDifferentialMomentum_contDiff source
    configuration smooth nondegenerate direction derivativeDirection
  unfold fieldDirectionalDerivative
  exact (momentumSmooth.continuous_fderiv (by simp)).clm_apply continuous_const

theorem scalarEulerLagrangeDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : ScalarCoordinateCarrier) :
    Continuous
      (scalarEulerLagrangeDirectionalCoefficient source configuration
        direction) :=
  (scalarAlgebraicDirectionalCoefficient_continuous source configuration smooth
    nondegenerate direction).sub
      (scalarDifferentialMomentumDivergence_continuous source configuration
        smooth nondegenerate direction)

/-! ## Genuine compact-support integration by parts -/

theorem scalarCompact_mul_continuous_integrable
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

theorem scalarCompactDerivative_mul_continuous_integrable
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

theorem scalarDifferentialMomentum_integrationByParts
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (derivativeDirection : LorentzianIndex) :
    (∫ point : BasePoint,
      fieldDirectionalDerivative variation point derivativeDirection *
        scalarDifferentialMomentum source configuration direction
          derivativeDirection point) =
      -(∫ point : BasePoint,
        variation point *
          fieldDirectionalDerivative
            (scalarDifferentialMomentum source configuration direction
              derivativeDirection) point derivativeDirection) := by
  have actual := compactSupport_integrationByParts
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (scalarDifferentialMomentum source configuration direction
      derivativeDirection)
    variation
    (scalarDifferentialMomentum_contDiff source configuration smooth
      nondegenerate direction derivativeDirection)
    derivativeDirection
  simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    fieldDirectionalDerivative, mul_comm] using actual

theorem canonicalScalarWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalScalarWeakEquation source configuration)
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        scalarEulerLagrangeDirectionalCoefficient source configuration direction
          point) = 0 := by
  let momentum := fun derivativeDirection : LorentzianIndex =>
    scalarDifferentialMomentum source configuration direction
      derivativeDirection
  let momentumDerivative := fun derivativeDirection : LorentzianIndex =>
    fun point => fieldDirectionalDerivative (momentum derivativeDirection)
      point derivativeDirection
  let algebraic :=
    scalarAlgebraicDirectionalCoefficient source configuration direction
  have momentumContinuous : ∀ derivativeDirection,
      Continuous (momentum derivativeDirection) := fun derivativeDirection =>
    (scalarDifferentialMomentum_contDiff source configuration smooth
      nondegenerate direction derivativeDirection).continuous
  have momentumDerivativeContinuous : ∀ derivativeDirection,
      Continuous (momentumDerivative derivativeDirection) := by
    intro derivativeDirection
    have momentumSmooth := scalarDifferentialMomentum_contDiff source
      configuration smooth nondegenerate direction derivativeDirection
    unfold momentumDerivative momentum fieldDirectionalDerivative
    exact (momentumSmooth.continuous_fderiv (by simp)).clm_apply
      continuous_const
  have derivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point := fun derivativeDirection =>
    scalarCompactDerivative_mul_continuous_integrable variation
      (momentum derivativeDirection) (momentumContinuous derivativeDirection)
      derivativeDirection
  have derivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      derivativeTermIntegrable derivativeDirection
  have algebraicContinuous : Continuous algebraic :=
    scalarAlgebraicDirectionalCoefficient_continuous source configuration smooth
      nondegenerate direction
  have algebraicTermIntegrable : Integrable fun point =>
      variation point * algebraic point :=
    scalarCompact_mul_continuous_integrable variation algebraic
      algebraicContinuous
  have momentumDerivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        variation point * momentumDerivative derivativeDirection point :=
    fun derivativeDirection =>
      scalarCompact_mul_continuous_integrable variation
        (momentumDerivative derivativeDirection)
        (momentumDerivativeContinuous derivativeDirection)
  have momentumDerivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        variation point * momentumDerivative derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      momentumDerivativeTermIntegrable derivativeDirection
  have weakDirection := weakEquation
    (scalarTimesScalarVariation direction variation)
  rw [show (fun point : BasePoint =>
      holonomicScalarFirstVariationDensity source configuration
        (scalarTimesScalarVariation direction variation) point) =
    fun point =>
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point) +
        variation point * algebraic point by
    funext point
    exact holonomicScalarFirstVariationDensity_scalarTimes source configuration
      direction variation point] at weakDirection
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
    exact scalarDifferentialMomentum_integrationByParts source configuration
      smooth nondegenerate direction variation derivativeDirection
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
          scalarEulerLagrangeDirectionalCoefficient source configuration
            direction point) =
      fun point =>
        variation point * algebraic point -
          ∑ derivativeDirection : LorentzianIndex,
            variation point * momentumDerivative derivativeDirection point := by
    funext point
    unfold scalarEulerLagrangeDirectionalCoefficient
      scalarDifferentialMomentumDivergence algebraic momentumDerivative
      momentum
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

def CanonicalScalarPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ direction : ScalarCoordinateCarrier,
    scalarEulerLagrangeDirectionalCoefficient source configuration direction =
      0

theorem canonicalScalarWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalScalarWeakEquation source configuration) :
    CanonicalScalarPointwiseEquation source configuration := by
  intro direction
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (scalarEulerLagrangeDirectionalCoefficient source configuration direction)
    (scalarEulerLagrangeDirectionalCoefficient_continuous source configuration
      smooth nondegenerate direction)
  intro variation
  exact canonicalScalarWeakEquation_direction_integral source configuration
    smooth nondegenerate weakEquation direction variation

theorem canonicalScalarActionStationary_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalScalarActionStationary source configuration) :
    CanonicalScalarPointwiseEquation source configuration := by
  apply canonicalScalarWeakEquation_implies_pointwiseEquation source
    configuration smooth nondegenerate
  exact canonicalScalarActionStationary_implies_weakEquation source
    configuration smooth nondegenerate densityIntegrable stationary

end

end SaturationMonoid.PhysicsCore.StageNineScalarPointwiseEquation
