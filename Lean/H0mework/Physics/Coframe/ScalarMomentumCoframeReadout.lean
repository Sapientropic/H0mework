import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity
import H0mework.Physics.Geometry.ScalarPointwiseEquation

/-!
# Scalar momentum as a coframe/covariant-derivative readout

The scalar differential momentum factors through the pointwise coframe and
the already generated scalar covariant derivative.  The factor is smooth at
the identity coframe.  This is a generic readout/regularity seam: it neither
selects a source event nor constructs a field update.
-/

namespace SaturationMonoid.PhysicsCore.StageNineScalarMomentumCoframeReadout

open ProofFreeRicherAnholonomicSource
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open StageNineScalarVariation

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

/-- The scalar differential-momentum reader exposed as a function of the
pointwise coframe and scalar covariant derivative. -/
def scalarMomentumCoframeCovariantReadout
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (joint :
      LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier)) : ℝ :=
  |Matrix.det joint.1| *
    ((1 / 2 : ℝ) *
      ∑ first : LorentzianIndex,
        ∑ second : LorentzianIndex,
          ((lorentzianMetricOfCoframe joint.1)⁻¹ first second) *
            (scalarCoordinatePairingRe
                (scalarVariationDifferentialDirection direction
                  derivativeDirection first)
                (joint.2 second) +
              scalarCoordinatePairingRe
                (joint.2 first)
                (scalarVariationDifferentialDirection direction
                  derivativeDirection second)))

theorem scalarMomentumCoframeCovariantReadout_contDiffAt
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (covariant : LorentzianIndex → ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (scalarMomentumCoframeCovariantReadout direction derivativeDirection)
      (coframe, covariant) := by
  let volume := fun joint :
      LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier) =>
    |Matrix.det joint.1|
  let metric := fun joint :
      LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier) =>
      (lorentzianMetricOfCoframe joint.1)⁻¹
  let variation :=
    scalarVariationDifferentialDirection direction derivativeDirection
  let pairingTerm := fun first second
      (joint :
        LorentzianCoframe ×
          (LorentzianIndex → ScalarCoordinateCarrier)) =>
    scalarCoordinatePairingRe (variation first) (joint.2 second) +
      scalarCoordinatePairingRe (joint.2 first) (variation second)
  let weightedTerm := fun first second
      (joint :
        LorentzianCoframe ×
          (LorentzianIndex → ScalarCoordinateCarrier)) =>
    metric joint first second * pairingTerm first second joint
  let doubleSum := fun
      (joint :
        LorentzianCoframe ×
          (LorentzianIndex → ScalarCoordinateCarrier)) =>
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex, weightedTerm first second joint
  have volumeSmooth : ContDiffAt ℝ ∞ volume
      (coframe, covariant) := by
    exact
      (coframe_volume_contDiffAt coframe nondegenerate).comp
        (coframe, covariant) contDiffAt_fst
  have metricSmooth : ContDiffAt ℝ ∞ metric
      (coframe, covariant) := by
    unfold metric
    change ContDiffAt ℝ ∞
      ((fun candidate : LorentzianCoframe =>
          (lorentzianMetricOfCoframe candidate)⁻¹) ∘
        (fun joint :
          LorentzianCoframe ×
            (LorentzianIndex → ScalarCoordinateCarrier) =>
          joint.1))
      (coframe, covariant)
    exact
      (lorentzianMetric_inv_contDiffAt
        coframe nondegenerate).comp
          (coframe, covariant) contDiffAt_fst
  have metricEntrySmooth (first second : LorentzianIndex) :
      ContDiffAt ℝ ∞ (fun joint => metric joint first second)
        (coframe, covariant) :=
    contDiffAt_pi.mp (contDiffAt_pi.mp metricSmooth first) second
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ (fun joint :
        LorentzianCoframe ×
          (LorentzianIndex → ScalarCoordinateCarrier) =>
        joint.2 formDirection) := by
    fun_prop
  have pairingTermSmooth (first second : LorentzianIndex) :
      ContDiff ℝ ∞ (pairingTerm first second) := by
    unfold pairingTerm
    let pairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap
    have leftSmooth : ContDiff ℝ ∞
        (fun joint :
          LorentzianCoframe ×
            (LorentzianIndex → ScalarCoordinateCarrier) =>
          pairing (variation first) (joint.2 second)) :=
      (contDiff_const :
        ContDiff ℝ ∞
          (fun _ :
            LorentzianCoframe ×
              (LorentzianIndex → ScalarCoordinateCarrier) =>
            pairing (variation first))).clm_apply
        (covariantSmooth second)
    have rightSmooth : ContDiff ℝ ∞
        (fun joint :
          LorentzianCoframe ×
            (LorentzianIndex → ScalarCoordinateCarrier) =>
          pairing (joint.2 first) (variation second)) :=
      (contDiff_const :
        ContDiff ℝ ∞
          (fun _ :
            LorentzianCoframe ×
              (LorentzianIndex → ScalarCoordinateCarrier) =>
            pairing.flip (variation second))).clm_apply
        (covariantSmooth first)
    exact leftSmooth.add rightSmooth
  have weightedTermSmooth (first second : LorentzianIndex) :
      ContDiffAt ℝ ∞ (weightedTerm first second)
        (coframe, covariant) :=
    (metricEntrySmooth first second).mul
      (pairingTermSmooth first second).contDiffAt
  have doubleSumSmooth : ContDiffAt ℝ ∞ doubleSum
      (coframe, covariant) := by
    unfold doubleSum
    apply ContDiffAt.sum
    intro first _
    apply ContDiffAt.sum
    intro second _
    exact weightedTermSmooth first second
  have readoutEquality :
      scalarMomentumCoframeCovariantReadout direction derivativeDirection =
        fun joint => volume joint * ((1 / 2 : ℝ) * doubleSum joint) := by
    funext joint
    rfl
  rw [readoutEquality]
  exact volumeSmooth.mul (contDiffAt_const.mul doubleSumSmooth)

theorem scalarMomentumCoframeCovariantReadout_contDiffAt_one
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (covariant : LorentzianIndex → ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (scalarMomentumCoframeCovariantReadout direction derivativeDirection)
      ((1 : LorentzianCoframe), covariant) := by
  exact scalarMomentumCoframeCovariantReadout_contDiffAt direction
    derivativeDirection 1 (by norm_num) covariant

theorem scalarDifferentialMomentum_eq_readout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source configuration direction
        derivativeDirection =
      scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
        fun point =>
          (configuration.coframe point,
            holonomicScalarCovariantDerivative configuration point) := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative generatedVolumeDensity
    scalarMomentumCoframeCovariantReadout
  simp only [Function.comp_apply, toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]

end

end SaturationMonoid.PhysicsCore.StageNineScalarMomentumCoframeReadout
