import H0mework.Physics.GaugeAction.P286GaugeConnectionPointwiseEquation
import H0mework.Physics.Geometry.FullMotherDescentAndTransport

/-!
# S9-C3a4c: generated-chart transport of the P286 connection equation

The actual source-generated transition transports scalar and Dirac current
jets from canonical chart `0` to every generated chart.  P286 curvature,
auxiliary, momentum, and one-form directions are moving-frame-relative
coordinates.  The transition lies in the embedded hypercharge subgroup and
its adjoint action fixes every P286 Lie direction; keeping those relative
coordinates unchanged is therefore a theorem, not a supplied invariance
receipt.

The transported local first-variation density is proved equal to the
canonical density.  Consequently the transported Euler--Lagrange coefficient
is exactly the canonical coefficient in every generated chart.  Combining
this transporter with the already derived action-stationarity, weak-equation,
IBP, and fundamental-lemma chain produces all chartwise pointwise equations.
No chartwise equation, current, transition, or covariance certificate is an
input.

This module transports already holonomic jets; it does not install an
independent first-jet mouth or claim that chart transport is a new physical
producer.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionChartTransport

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineFullMotherDescentAndTransport
open StageNineGlobalIntegratedAction
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNinePlebanskiMultiplierVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionWeakEquation
open StageNineP286GaugeConnectionPointwiseEquation
open DiracExteriorMatterAction
open SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorMatterGaugeCovariantJet

noncomputable section

set_option maxHeartbeats 600000

theorem generatedTransition_fixes_p286MotherDirection
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (direction : P286LieBlockData) :
    motherGaugeConjugate (generatedTransition source initial terminal point)
        (p286LieBlockEmbed direction) =
      p286LieBlockEmbed direction := by
  apply Subtype.ext
  have commutes :
      (generatedTransition source initial terminal point :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          (p286LieBlockEmbed direction :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) =
        (p286LieBlockEmbed direction :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          generatedTransition source initial terminal point := by
    simpa [generatedTransition] using
      (embeddedP286HyperchargeElement_commutes_p286LieBlockEmbed
        (Circle.exp
          ((chartWeight terminal - chartWeight initial) *
            source.continuousContactRate * point 0)) direction).eq
  have unitary :
      (generatedTransition source initial terminal point :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          star (generatedTransition source initial terminal point :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup
        (generatedTransition source initial terminal point).property)
  change
    (generatedTransition source initial terminal point :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          (p286LieBlockEmbed direction :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          star (generatedTransition source initial terminal point :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      (p286LieBlockEmbed direction :
        Matrix SU7MotherIndex SU7MotherIndex ℂ)
  rw [commutes, Matrix.mul_assoc, unitary, Matrix.mul_one]

def transportScalarGaugeConnectionVariation
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    LorentzianIndex → ScalarCoordinateCarrier :=
  fun direction =>
    scalarCoordinateAction
      (generatedTransition source initial terminal point)
      (variation direction)

def transportMatterGaugeConnectionVariation
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    LorentzianIndex → DiracExteriorMatterCarrier :=
  fun direction =>
    diracExteriorMatterGaugeRepresentation
      (generatedTransition source initial terminal point)
      (variation direction)

theorem scalarGaugeConnectionKineticFirstVariationDensity_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source terminal point
        (transportContinuumPointField source initial terminal point field)
        (transportScalarGaugeConnectionVariation source initial terminal point
          variation) =
      scalarGaugeConnectionKineticFirstVariationDensity source initial point
        field variation := by
  have variationEquality :
      scalarFrameRelativeCovariantDerivative source terminal point
          (transportScalarGaugeConnectionVariation source initial terminal
            point variation) =
        scalarFrameRelativeCovariantDerivative source initial point variation := by
    funext direction
    exact scalarFrameRelativeCoordinates_overlap source initial terminal point
      (variation direction)
  have fieldEquality :
      scalarFrameRelativeCovariantDerivative source terminal point
          (transportContinuumPointField source initial terminal point field).scalarCovariantDerivative =
        scalarFrameRelativeCovariantDerivative source initial point
          field.scalarCovariantDerivative := by
    funext direction
    exact scalarFrameRelativeCovariantDerivative_overlap source initial terminal
      point field.scalarCovariantDerivative direction
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [variationEquality, fieldEquality]
  rfl

theorem matterGaugeKineticSum_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeKineticSum source terminal point
        (transportContinuumPointField source initial terminal point field)
        (transportMatterGaugeConnectionVariation source initial terminal point
          variation) =
      matterGaugeKineticSum source initial point field variation := by
  have variationEquality :
      matterDerivativeFrameRelative source terminal point
          (transportMatterGaugeConnectionVariation source initial terminal point
            variation) =
        matterDerivativeFrameRelative source initial point variation := by
    funext direction
    exact matterFrameRelative_overlap source initial terminal point
      (variation direction)
  unfold matterGaugeKineticSum
  rw [variationEquality]
  rfl

theorem matterGaugeConnectionFirstVariationDensity_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity source terminal point
        (transportContinuumPointField source initial terminal point field)
        (transportMatterGaugeConnectionVariation source initial terminal point
          variation) =
      matterGaugeConnectionFirstVariationDensity source initial point field
        variation := by
  have kineticEquality := matterGaugeKineticSum_overlap source initial terminal
    point field variation
  have dualEquality := matterDualFrameRelative_overlap source initial terminal
    point field.conjugateMatter
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [kineticEquality]
  simpa only [transportContinuumPointField] using congrArg
    (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier =>
      (dual (Complex.I •
        matterGaugeKineticSum source initial point field variation)).re)
    dualEquality

theorem p286GaugeConnectionFirstVariationDensity_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (curvatureVariation : P286GaugeTwoForm)
    (scalarVariation : LorentzianIndex → ScalarCoordinateCarrier)
    (matterVariation : LorentzianIndex → DiracExteriorMatterCarrier) :
    p286GaugeConnectionFirstVariationDensity source terminal point
        (transportContinuumPointField source initial terminal point field)
        curvatureVariation
        (transportScalarGaugeConnectionVariation source initial terminal point
          scalarVariation)
        (transportMatterGaugeConnectionVariation source initial terminal point
          matterVariation) =
      p286GaugeConnectionFirstVariationDensity source initial point field
        curvatureVariation scalarVariation matterVariation := by
  rw [p286GaugeConnectionFirstVariationDensity,
    p286GaugeConnectionFirstVariationDensity,
    scalarGaugeConnectionKineticFirstVariationDensity_overlap,
    matterGaugeConnectionFirstVariationDensity_overlap]
  rfl

def generatedChartP286GaugeConnectionAlgebraicCurrentCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (chart : StageNineChart)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  p286GaugeConnectionFirstVariationDensity source chart point
    (transportContinuumPointField source 0 chart point
      (toContinuumPointField configuration point))
    (p286GaugeConnectionAlgebraicCurvatureDirection
      configuration direction point)
    (transportScalarGaugeConnectionVariation source 0 chart point
      (holonomicScalarGaugeConnectionVariation configuration
        (fun _ => direction) point))
    (transportMatterGaugeConnectionVariation source 0 chart point
      (holonomicMatterGaugeConnectionVariation configuration
        (fun _ => direction) point))

theorem generatedChartP286GaugeConnectionAlgebraicCurrentCoefficient_eq_canonical
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (chart : StageNineChart)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    generatedChartP286GaugeConnectionAlgebraicCurrentCoefficient source
        configuration chart direction point =
      p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        direction point := by
  unfold generatedChartP286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionAlgebraicCurrentCoefficient
  exact p286GaugeConnectionFirstVariationDensity_overlap source 0 chart point
    (toContinuumPointField configuration point)
    (p286GaugeConnectionAlgebraicCurvatureDirection configuration direction point)
    (holonomicScalarGaugeConnectionVariation configuration
      (fun _ => direction) point)
    (holonomicMatterGaugeConnectionVariation configuration
      (fun _ => direction) point)

def generatedChartP286GaugeConnectionEulerLagrangeCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (chart : StageNineChart)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  generatedChartP286GaugeConnectionAlgebraicCurrentCoefficient source
      configuration chart direction point -
    p286GaugeConnectionBFDifferentialMomentumDivergence configuration
      direction point

theorem generatedChartP286GaugeConnectionEulerLagrangeCoefficient_eq_canonical
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (chart : StageNineChart)
    (direction : P286GaugeOneForm) :
    generatedChartP286GaugeConnectionEulerLagrangeCoefficient source
        configuration chart direction =
      p286GaugeConnectionEulerLagrangeCoefficient source configuration
        direction := by
  funext point
  unfold generatedChartP286GaugeConnectionEulerLagrangeCoefficient
    p286GaugeConnectionEulerLagrangeCoefficient
  rw [generatedChartP286GaugeConnectionAlgebraicCurrentCoefficient_eq_canonical]

def GeneratedChartP286GaugeConnectionPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (chart : StageNineChart) : Prop :=
  ∀ direction : P286GaugeOneForm,
    generatedChartP286GaugeConnectionEulerLagrangeCoefficient source
      configuration chart direction = 0

theorem canonicalP286GaugeConnectionPointwiseEquation_iff_generatedChart
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (chart : StageNineChart) :
    CanonicalP286GaugeConnectionPointwiseEquation source configuration ↔
      GeneratedChartP286GaugeConnectionPointwiseEquation source configuration
        chart := by
  constructor <;> intro equation direction
  · rw [generatedChartP286GaugeConnectionEulerLagrangeCoefficient_eq_canonical]
    exact equation direction
  · rw [← generatedChartP286GaugeConnectionEulerLagrangeCoefficient_eq_canonical
      source configuration chart direction]
    exact equation direction

def AllGeneratedChartsP286GaugeConnectionPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ chart : StageNineChart,
    GeneratedChartP286GaugeConnectionPointwiseEquation source configuration
      chart

theorem canonicalP286GaugeConnectionPointwiseEquation_transports_to_allGeneratedCharts
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (equation : CanonicalP286GaugeConnectionPointwiseEquation source
      configuration) :
    AllGeneratedChartsP286GaugeConnectionPointwiseEquation source
      configuration := by
  intro chart
  exact (canonicalP286GaugeConnectionPointwiseEquation_iff_generatedChart
    source configuration chart).mp equation

theorem canonicalP286GaugeConnectionActionStationary_implies_allGeneratedChartsPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalP286GaugeConnectionActionStationary source
      configuration) :
    AllGeneratedChartsP286GaugeConnectionPointwiseEquation source
      configuration := by
  apply canonicalP286GaugeConnectionPointwiseEquation_transports_to_allGeneratedCharts
  apply canonicalP286GaugeConnectionWeakEquation_implies_pointwiseEquation
    source configuration smooth nondegenerate
  exact canonicalP286GaugeConnectionActionStationary_implies_weakEquation
    source configuration smooth nondegenerate densityIntegrable stationary

end

end SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionChartTransport
