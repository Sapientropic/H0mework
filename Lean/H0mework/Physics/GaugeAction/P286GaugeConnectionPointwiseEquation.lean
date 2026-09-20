import H0mework.Physics.GaugeAction.P286GaugeConnectionMomentumRegularity

/-!
# S9-C3a4b: pointwise P286 connection equation by genuine IBP

One primitive compactly supported connection variation is specialized to a
smooth scalar bump times an arbitrary constant P286 one-form direction.  Its
actual curvature, scalar, and Dirac variations are split into derivative and
algebraic channels.  The derivative coefficient is exactly the smooth BF
momentum generated in C3a4a.

The canonical weak equation is then integrated by parts in every spacetime
direction.  All continuity, compact support, and integrability obligations
are generated internally.  The smooth-bump fundamental lemma yields the
pointwise directional Euler--Lagrange equation with BF divergence plus the
scalar and Dirac currents; no current or equation certificate is supplied.

Gauge-covariant transport from canonical generated chart `0` remains a
downstream checkpoint.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionPointwiseEquation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNinePlebanskiMultiplierVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionWeakEquation
open StageNineP286GaugeConnectionMomentumRegularity
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open DiracExteriorMatterAction
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

set_option maxHeartbeats 600000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286GaugeConnectionActionVariation.p286CoordinateIndexFintype

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

def scalarTimesP286GaugeConnectionVariation
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation P286GaugeOneForm where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

@[simp] theorem scalarTimesP286GaugeConnectionVariation_apply
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    scalarTimesP286GaugeConnectionVariation direction variation point =
      variation point • direction :=
  rfl

theorem p286GaugeVariationCoordinateDerivative_scalarTimes
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative
        (scalarTimesP286GaugeConnectionVariation direction variation)
        point derivativeDirection formDirection =
      fieldDirectionalDerivative variation point derivativeDirection •
        direction formDirection := by
  have differentiable : DifferentiableAt ℝ
      (variation : BasePoint → ℝ) point :=
    (variation.smooth.differentiable (by simp)).differentiableAt
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  rw [show (fun candidate =>
      scalarTimesP286GaugeConnectionVariation direction variation candidate
        formDirection) =
      fun candidate => variation candidate • direction formDirection by rfl]
  rw [fderiv_smul_const differentiable]
  rfl

def p286GaugeExteriorDerivativeDirection
    (derivativeDirection : LorentzianIndex)
    (direction : P286GaugeOneForm) : P286GaugeTwoForm :=
  fun pair =>
    (if derivativeDirection = pairFirst pair then
      direction (pairSecond pair) else 0) -
    (if derivativeDirection = pairSecond pair then
      direction (pairFirst pair) else 0)

def p286GaugeConnectionExteriorDerivativeVariation
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    P286GaugeTwoForm :=
  fun pair =>
    p286GaugeVariationCoordinateDerivative variation point
        (pairFirst pair) (pairSecond pair) -
      p286GaugeVariationCoordinateDerivative variation point
        (pairSecond pair) (pairFirst pair)

def p286GaugeConnectionAlgebraicCurvatureVariation
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateLieBracket
      (variation point (pairFirst pair))
      (holonomicP286GaugeConnectionCoordinate configuration point
        (pairSecond pair)) +
    p286CoordinateLieBracket
      (holonomicP286GaugeConnectionCoordinate configuration point
        (pairFirst pair))
      (variation point (pairSecond pair))

def p286GaugeConnectionAlgebraicCurvatureDirection
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    P286GaugeTwoForm :=
  p286GaugeConnectionAlgebraicCurvatureVariation configuration
    (fun _ => direction) point

theorem p286GaugeConnectionExteriorDerivativeVariation_scalarTimes
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    p286GaugeConnectionExteriorDerivativeVariation
        (scalarTimesP286GaugeConnectionVariation direction variation) point =
      ∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection •
          p286GaugeExteriorDerivativeDirection derivativeDirection direction := by
  funext pair
  unfold p286GaugeConnectionExteriorDerivativeVariation
  rw [p286GaugeVariationCoordinateDerivative_scalarTimes,
    p286GaugeVariationCoordinateDerivative_scalarTimes]
  fin_cases pair <;>
    simp [p286GaugeExteriorDerivativeDirection, Fin.sum_univ_four,
      pairFirst, pairSecond] <;>
    module

theorem p286GaugeConnectionAlgebraicCurvatureVariation_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurvatureVariation configuration
        (scalarTimesP286GaugeConnectionVariation direction variation) point =
      variation point •
        p286GaugeConnectionAlgebraicCurvatureDirection
          configuration direction point := by
  funext pair
  change
    p286CoordinateLieBracket
          (variation point • direction (pairFirst pair))
          (holonomicP286GaugeConnectionCoordinate configuration point
            (pairSecond pair)) +
        p286CoordinateLieBracket
          (holonomicP286GaugeConnectionCoordinate configuration point
            (pairFirst pair))
          (variation point • direction (pairSecond pair)) =
      variation point •
        (p286CoordinateLieBracket
            (direction (pairFirst pair))
            (holonomicP286GaugeConnectionCoordinate configuration point
              (pairSecond pair)) +
          p286CoordinateLieBracket
            (holonomicP286GaugeConnectionCoordinate configuration point
              (pairFirst pair))
            (direction (pairSecond pair)))
  simp only [
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right]
  module

theorem p286GaugeConnectionLinearCurvatureVariation_eq_parts
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionLinearCurvatureVariation configuration variation point =
      p286GaugeConnectionExteriorDerivativeVariation variation point +
        p286GaugeConnectionAlgebraicCurvatureVariation
          configuration variation point := by
  funext pair
  unfold p286GaugeConnectionLinearCurvatureVariation
    p286GaugeConnectionExteriorDerivativeVariation
    p286GaugeConnectionAlgebraicCurvatureVariation
  simp only [Pi.add_apply]
  abel

theorem p286GaugeConnectionLinearCurvatureVariation_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    p286GaugeConnectionLinearCurvatureVariation configuration
        (scalarTimesP286GaugeConnectionVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection •
          p286GaugeExteriorDerivativeDirection derivativeDirection direction) +
      variation point •
        p286GaugeConnectionAlgebraicCurvatureDirection
          configuration direction point := by
  rw [p286GaugeConnectionLinearCurvatureVariation_eq_parts,
    p286GaugeConnectionExteriorDerivativeVariation_scalarTimes,
    p286GaugeConnectionAlgebraicCurvatureVariation_scalarTimes]

theorem holonomicScalarGaugeConnectionVariation_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicScalarGaugeConnectionVariation configuration
        (scalarTimesP286GaugeConnectionVariation direction variation) point =
      variation point •
        holonomicScalarGaugeConnectionVariation configuration
          (fun _ => direction) point := by
  funext formDirection
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  rw [show scalarTimesP286GaugeConnectionVariation direction variation point
      formDirection = variation point • direction formDirection by rfl]
  rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_real_smul]
  rfl

theorem holonomicMatterGaugeConnectionVariation_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicMatterGaugeConnectionVariation configuration
        (scalarTimesP286GaugeConnectionVariation direction variation) point =
      variation point •
        holonomicMatterGaugeConnectionVariation configuration
          (fun _ => direction) point := by
  funext formDirection
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  rw [show scalarTimesP286GaugeConnectionVariation direction variation point
      formDirection = variation point • direction formDirection by rfl]
  rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul]
  rfl

theorem p286GaugeBFCurvatureIncrementDensity_add
    (coframe : LorentzianCoframe)
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (auxiliary first second : P286GaugeTwoForm) :
    p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
        (first + second) =
      p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
          first +
        p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
          second := by
  unfold p286GaugeBFCurvatureIncrementDensity
  rw [liftGaugeTwoFormOperator_add_p286,
    generatedGaugeTwoFormMetricPairing_p286_add_right]

theorem p286GaugeBFCurvatureIncrementDensity_smul
    (coframe : LorentzianCoframe)
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (auxiliary variation : P286GaugeTwoForm) (parameter : ℝ) :
    p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
        (parameter • variation) =
      parameter *
        p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
          variation := by
  unfold p286GaugeBFCurvatureIncrementDensity
  rw [liftGaugeTwoFormOperator_smul_p286,
    generatedGaugeTwoFormMetricPairing_p286_smul_right]

def p286GaugeBFCurvatureIncrementLinear
    (coframe : LorentzianCoframe)
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (auxiliary : P286GaugeTwoForm) : P286GaugeTwoForm →ₗ[ℝ] ℝ where
  toFun := fun variation =>
    p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
      variation
  map_add' := p286GaugeBFCurvatureIncrementDensity_add _ _ _
  map_smul' := by
    intro parameter variation
    simpa [smul_eq_mul] using
      p286GaugeBFCurvatureIncrementDensity_smul coframe spacetimeHodge
        auxiliary variation parameter

@[simp] theorem p286GaugeBFCurvatureIncrementLinear_apply
    (coframe : LorentzianCoframe)
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (auxiliary variation : P286GaugeTwoForm) :
    p286GaugeBFCurvatureIncrementLinear coframe spacetimeHodge auxiliary
        variation =
      p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
        variation :=
  rfl

theorem weightedDoubleSum_real_linear
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

theorem scalarGaugeConnectionKineticFirstVariationDensity_real_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source chart point field
        (parameter • variation) =
      parameter *
        scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [scalarFrameRelativeCovariantDerivative_real_smul]
  simp only [Pi.smul_apply,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp_rw [← Matrix.of_symm_apply]
  rw [weightedDoubleSum_real_linear]
  ring

theorem matterGaugeConnectionFirstVariationDensity_real_smul
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
  rw [vectorEquality,
    matterDualFrameRelative_real_smul]
  simp [Complex.mul_re]

theorem p286GaugeBFCurvatureIncrementDensity_sum_add_smul
    {Index : Type*} [Fintype Index]
    (coframe : LorentzianCoframe)
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (auxiliary : P286GaugeTwoForm)
    (coefficient : Index → ℝ)
    (direction : Index → P286GaugeTwoForm)
    (parameter : ℝ) (residual : P286GaugeTwoForm) :
    p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
        ((∑ index : Index, coefficient index • direction index) +
          parameter • residual) =
      (∑ index : Index,
        coefficient index *
          p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
            (direction index)) +
        parameter *
          p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary
            residual := by
  change
    p286GaugeBFCurvatureIncrementLinear coframe spacetimeHodge auxiliary
        ((∑ index : Index, coefficient index • direction index) +
          parameter • residual) = _
  rw [map_add, map_sum, map_smul]
  simp only [p286GaugeBFCurvatureIncrementLinear_apply, smul_eq_mul,
    map_smul]

theorem p286GaugeConnectionBFDifferentialMomentum_eq_density
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeTwoForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum configuration direction point =
      generatedVolumeDensity (toContinuumPointField configuration point) *
        p286GaugeBFCurvatureIncrementDensity
          (configuration.coframe point)
          (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (holonomicP286GaugeAuxiliaryCoordinate configuration point)
          direction := by
  unfold p286GaugeConnectionBFDifferentialMomentum
    p286GaugeBFCurvatureIncrementDensity
  rw [p286GaugeAuxiliaryHodgePairingPolynomial_eq
    (configuration.coframe point) (nondegenerate point)]

def p286GaugeConnectionAlgebraicCurrentCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  p286GaugeConnectionFirstVariationDensity source 0 point
    (toContinuumPointField configuration point)
    (p286GaugeConnectionAlgebraicCurvatureDirection
      configuration direction point)
    (holonomicScalarGaugeConnectionVariation configuration
      (fun _ => direction) point)
    (holonomicMatterGaugeConnectionVariation configuration
      (fun _ => direction) point)

/-- The algebraic P286 connection current is local in exactly the listed
contact data.  Gravity curvature and the linear-Plebanski multiplier are not
accepted because this action coefficient does not consume them. -/
theorem p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEq : first.coframe point = second.coframe point)
    (gaugeConnectionEq :
      first.gaugeConnection point = second.gaugeConnection point)
    (gaugeAuxiliaryEq :
      first.gaugeAuxiliary point = second.gaugeAuxiliary point)
    (scalarEq : first.scalar point = second.scalar point)
    (scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative first point =
        holonomicScalarCovariantDerivative second point)
    (matterEq : first.matter point = second.matter point)
    (conjugateEq :
      first.conjugateMatter point = second.conjugateMatter point)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source first direction
        point =
      p286GaugeConnectionAlgebraicCurrentCoefficient source second direction
        point := by
  have curvatureVariationEq :
      p286GaugeConnectionAlgebraicCurvatureDirection first direction point =
        p286GaugeConnectionAlgebraicCurvatureDirection second direction
          point := by
    unfold p286GaugeConnectionAlgebraicCurvatureDirection
      p286GaugeConnectionAlgebraicCurvatureVariation
      holonomicP286GaugeConnectionCoordinate
    rw [gaugeConnectionEq]
  have scalarVariationEq :
      holonomicScalarGaugeConnectionVariation first (fun _ => direction)
          point =
        holonomicScalarGaugeConnectionVariation second (fun _ => direction)
          point := by
    unfold holonomicScalarGaugeConnectionVariation
    rw [scalarEq]
  have matterVariationEq :
      holonomicMatterGaugeConnectionVariation first (fun _ => direction)
          point =
        holonomicMatterGaugeConnectionVariation second (fun _ => direction)
          point := by
    unfold holonomicMatterGaugeConnectionVariation
    rw [matterEq]
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionFirstVariationDensity generatedVolumeDensity
    p286AuxiliaryCoordinate
    scalarGaugeConnectionKineticFirstVariationDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  rw [curvatureVariationEq, scalarVariationEq, matterVariationEq]
  simp only [toContinuumPointField]
  rw [coframeEq, gaugeAuxiliaryEq, scalarCovariantDerivativeEq, conjugateEq]

theorem holonomicP286GaugeConnectionFirstVariationDensity_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicP286GaugeConnectionFirstVariationDensity source 0 configuration
        (scalarTimesP286GaugeConnectionVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          p286GaugeConnectionBFDifferentialMomentum configuration
            (p286GaugeExteriorDerivativeDirection derivativeDirection direction)
            point) +
        variation point *
          p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
            direction point := by
  unfold holonomicP286GaugeConnectionFirstVariationDensity
  rw [p286GaugeConnectionLinearCurvatureVariation_scalarTimes,
    holonomicScalarGaugeConnectionVariation_scalarTimes,
    holonomicMatterGaugeConnectionVariation_scalarTimes]
  unfold p286GaugeConnectionFirstVariationDensity
  rw [p286GaugeBFCurvatureIncrementDensity_sum_add_smul,
    scalarGaugeConnectionKineticFirstVariationDensity_real_smul,
    matterGaugeConnectionFirstVariationDensity_real_smul]
  simp_rw [p286GaugeConnectionBFDifferentialMomentum_eq_density
    configuration nondegenerate]
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionFirstVariationDensity
  rw [show (toContinuumPointField configuration point).coframe =
      configuration.coframe point by rfl]
  rw [show p286AuxiliaryCoordinate
      (toContinuumPointField configuration point) =
        holonomicP286GaugeAuxiliaryCoordinate configuration point by rfl]
  have sumEquality :
      generatedVolumeDensity (toContinuumPointField configuration point) *
          (∑ derivativeDirection : LorentzianIndex,
            fieldDirectionalDerivative variation point derivativeDirection *
              p286GaugeBFCurvatureIncrementDensity
                (configuration.coframe point)
                (coframeGaugeSpacetimeHodgeLinear
                  (configuration.coframe point))
                (holonomicP286GaugeAuxiliaryCoordinate configuration point)
                (p286GaugeExteriorDerivativeDirection derivativeDirection
                  direction)) =
        ∑ derivativeDirection : LorentzianIndex,
          fieldDirectionalDerivative variation point derivativeDirection *
            (generatedVolumeDensity
                (toContinuumPointField configuration point) *
              p286GaugeBFCurvatureIncrementDensity
                (configuration.coframe point)
                (coframeGaugeSpacetimeHodgeLinear
                  (configuration.coframe point))
                (holonomicP286GaugeAuxiliaryCoordinate configuration point)
                (p286GaugeExteriorDerivativeDirection derivativeDirection
                  direction)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro derivativeDirection _
    ring
  rw [← sumEquality]
  ring

theorem p286GaugeConnectionAlgebraicCurvatureDirection_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      p286GaugeConnectionAlgebraicCurvatureDirection
        configuration direction point := by
  have connectionContinuous :=
    holonomicP286GaugeConnectionCoordinate_continuous configuration smooth
  apply continuous_pi
  intro pair
  have connectionFirst : Continuous fun point =>
      holonomicP286GaugeConnectionCoordinate configuration point
        (pairFirst pair) :=
    (continuous_apply (pairFirst pair)).comp connectionContinuous
  have connectionSecond : Continuous fun point =>
      holonomicP286GaugeConnectionCoordinate configuration point
        (pairSecond pair) :=
    (continuous_apply (pairSecond pair)).comp connectionContinuous
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  exact (p286CoordinateLieBracket_apply_continuous _ _ continuous_const
      connectionSecond).add
    (p286CoordinateLieBracket_apply_continuous _ _ connectionFirst
      continuous_const)

theorem holonomicP286GaugeConnectionAlgebraicBFDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      p286GaugeBFCurvatureIncrementDensity
        (configuration.coframe point)
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (holonomicP286GaugeAuxiliaryCoordinate configuration point)
        (p286GaugeConnectionAlgebraicCurvatureDirection
          configuration direction point) := by
  have auxiliaryContinuous :=
    holonomicP286GaugeAuxiliaryCoordinate_continuous configuration smooth
  have algebraicContinuous :=
    p286GaugeConnectionAlgebraicCurvatureDirection_continuous configuration
      smooth direction
  have hodgeAlgebraicContinuous :=
    holonomicLiftGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate _ algebraicContinuous
  have pairingContinuous :=
    generatedGaugeTwoFormMetricPairing_p286_apply_continuous configuration
      smooth _ _ auxiliaryContinuous hodgeAlgebraicContinuous
  exact pairingContinuous.congr fun point => rfl

theorem holonomicScalarGaugeConnectionConstantDirection_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      holonomicScalarGaugeConnectionVariation configuration
        (fun _ => direction) point formDirection := by
  have scalarContinuous : Continuous configuration.scalar :=
    smooth.2.2.2.2.2.2.1.continuous
  have actual := scalarP286Action_apply_continuous
    (fun _ : BasePoint => direction formDirection) configuration.scalar
      continuous_const scalarContinuous
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  change Continuous fun point =>
    scalarP286ActionBilinear (direction formDirection)
      (configuration.scalar point)
  exact actual

theorem holonomicScalarGaugeConnectionAlgebraicDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicScalarGaugeConnectionVariation configuration
          (fun _ => direction) point) := by
  have metricInverseContinuous :=
    holonomicLorentzianMetric_inv_continuous configuration smooth nondegenerate
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
      (holonomicScalarGaugeConnectionConstantDirection_continuous configuration
        smooth direction first)
      (holonomicScalarCovariantDerivative_continuous configuration smooth
        second)
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarCovariantDerivative_continuous configuration smooth
        first)
      (holonomicScalarGaugeConnectionConstantDirection_continuous configuration
        smooth direction second)

theorem holonomicMatterGaugeConnectionConstantDirection_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (holonomicMatterGaugeConnectionVariation configuration
          (fun _ => direction) point formDirection) := by
  have matterContinuous : Continuous fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1.continuous
  have actual := matterP286ActionCoordinate_apply_continuous
    (fun _ : BasePoint => direction formDirection)
    (fun point => matterCoordinateEquiv (configuration.matter point))
    continuous_const matterContinuous
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  exact actual.congr fun point => by
    change
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm (direction formDirection)))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) =
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm (direction formDirection)))
            (configuration.matter point))
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem holonomicMatterGaugeConstantDirectionKineticSummand_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            formDirection)
          (holonomicMatterGaugeConnectionVariation configuration
            (fun _ => direction) point formDirection)) :=
  diracMatrixMatterCoordinate_raw_apply_continuous _ _
    (holonomicInverseCoframeDiracGamma_continuous configuration smooth
      nondegenerate formDirection)
    (holonomicMatterGaugeConnectionConstantDirection_coordinate_continuous
      configuration smooth direction formDirection)

theorem holonomicMatterGaugeConstantDirectionKineticSum_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterGaugeConnectionVariation configuration
            (fun _ => direction) point)) := by
  have sumContinuous : Continuous fun point =>
      ∑ formDirection : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (holonomicMatterGaugeConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
    apply continuous_finsetSum
    intro formDirection _
    exact holonomicMatterGaugeConstantDirectionKineticSummand_continuous
      configuration smooth nondegenerate direction formDirection
  exact sumContinuous.congr fun point => by
    unfold matterGaugeKineticSum matterDerivativeFrameRelative
    simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]

theorem holonomicMatterGaugeConstantDirectionVector_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeConnectionVariationVector source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterGaugeConnectionVariation configuration
            (fun _ => direction) point)) := by
  have kineticContinuous :=
    holonomicMatterGaugeConstantDirectionKineticSum_continuous source
      configuration smooth nondegenerate direction
  have coordinateContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterGaugeConnectionVariation configuration
            (fun _ => direction) point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticContinuous).congr fun point => rfl
  unfold matterGaugeConnectionVariationVector
  exact coordinateContinuous.congr fun point => by rw [map_smul]

theorem holonomicMatterGaugeConnectionAlgebraicDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      matterGaugeConnectionFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicMatterGaugeConnectionVariation configuration
          (fun _ => direction) point) := by
  let vector := fun point =>
    matterGaugeConnectionVariationVector source 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterGaugeConnectionVariation configuration
        (fun _ => direction) point)
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    holonomicMatterGaugeConstantDirectionVector_continuous source
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

theorem p286GaugeConnectionAlgebraicCurrentCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous
      (p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        direction) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      abs (Matrix.det (configuration.coframe point)) :=
    coframeContinuous.matrix_det.abs
  have bfContinuous :=
    holonomicP286GaugeConnectionAlgebraicBFDensity_continuous configuration
      smooth nondegenerate direction
  have scalarContinuous :=
    holonomicScalarGaugeConnectionAlgebraicDensity_continuous source
      configuration smooth nondegenerate direction
  have matterContinuous :=
    holonomicMatterGaugeConnectionAlgebraicDensity_continuous source
      configuration smooth nondegenerate direction
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionFirstVariationDensity generatedVolumeDensity
  have actual := volumeContinuous.mul
    ((bfContinuous.add scalarContinuous).add matterContinuous)
  exact actual.congr fun point => rfl

def p286GaugeConnectionBFDifferentialMomentumDivergence
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (p286GaugeConnectionBFDifferentialMomentum configuration
        (p286GaugeExteriorDerivativeDirection derivativeDirection direction))
      point derivativeDirection

def p286GaugeConnectionEulerLagrangeCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
      direction point -
    p286GaugeConnectionBFDifferentialMomentumDivergence configuration
      direction point

theorem p286GaugeConnectionBFDifferentialMomentumDivergence_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous
      (p286GaugeConnectionBFDifferentialMomentumDivergence configuration
        direction) := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply continuous_finsetSum
  intro derivativeDirection _
  have momentumSmooth :=
    p286GaugeConnectionBFDifferentialMomentum_contDiff configuration smooth
      nondegenerate
      (p286GaugeExteriorDerivativeDirection derivativeDirection direction)
  have derivativeContinuous : Continuous fun point =>
      fderiv ℝ
        (p286GaugeConnectionBFDifferentialMomentum configuration
          (p286GaugeExteriorDerivativeDirection derivativeDirection direction))
        point := momentumSmooth.continuous_fderiv (by simp)
  unfold fieldDirectionalDerivative
  exact derivativeContinuous.clm_apply continuous_const

theorem p286GaugeConnectionEulerLagrangeCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous
      (p286GaugeConnectionEulerLagrangeCoefficient source configuration
        direction) :=
  (p286GaugeConnectionAlgebraicCurrentCoefficient_continuous source
    configuration smooth nondegenerate direction).sub
      (p286GaugeConnectionBFDifferentialMomentumDivergence_continuous
        configuration smooth nondegenerate direction)

theorem compactScalar_mul_continuous_integrable
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

theorem compactScalarDerivative_mul_continuous_integrable
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

theorem p286GaugeConnectionBFDifferentialMomentum_integrationByParts
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (derivativeDirection : LorentzianIndex) :
    (∫ point : BasePoint,
      fieldDirectionalDerivative variation point derivativeDirection *
        p286GaugeConnectionBFDifferentialMomentum configuration
          (p286GaugeExteriorDerivativeDirection derivativeDirection direction)
          point) =
      -(∫ point : BasePoint,
        variation point *
          fieldDirectionalDerivative
            (p286GaugeConnectionBFDifferentialMomentum configuration
              (p286GaugeExteriorDerivativeDirection derivativeDirection
                direction))
            point derivativeDirection) := by
  have actual := compactSupport_integrationByParts
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (p286GaugeConnectionBFDifferentialMomentum configuration
      (p286GaugeExteriorDerivativeDirection derivativeDirection direction))
    variation
    (p286GaugeConnectionBFDifferentialMomentum_contDiff configuration smooth
      nondegenerate
      (p286GaugeExteriorDerivativeDirection derivativeDirection direction))
    derivativeDirection
  simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    fieldDirectionalDerivative, mul_comm] using actual

theorem canonicalP286GaugeConnectionWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalP286GaugeConnectionWeakEquation source
      configuration)
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        p286GaugeConnectionEulerLagrangeCoefficient source configuration
          direction point) = 0 := by
  let momentum := fun derivativeDirection : LorentzianIndex =>
    p286GaugeConnectionBFDifferentialMomentum configuration
      (p286GaugeExteriorDerivativeDirection derivativeDirection direction)
  let momentumDerivative := fun derivativeDirection : LorentzianIndex =>
    fun point => fieldDirectionalDerivative (momentum derivativeDirection)
      point derivativeDirection
  let algebraic :=
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
      direction
  have momentumContinuous : ∀ derivativeDirection,
      Continuous (momentum derivativeDirection) := fun derivativeDirection =>
    (p286GaugeConnectionBFDifferentialMomentum_contDiff configuration smooth
      nondegenerate
      (p286GaugeExteriorDerivativeDirection derivativeDirection direction)).continuous
  have momentumDerivativeContinuous : ∀ derivativeDirection,
      Continuous (momentumDerivative derivativeDirection) := by
    intro derivativeDirection
    have momentumSmooth :=
      p286GaugeConnectionBFDifferentialMomentum_contDiff configuration smooth
        nondegenerate
        (p286GaugeExteriorDerivativeDirection derivativeDirection direction)
    unfold momentumDerivative momentum fieldDirectionalDerivative
    exact (momentumSmooth.continuous_fderiv (by simp)).clm_apply
      continuous_const
  have derivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point := fun derivativeDirection =>
    compactScalarDerivative_mul_continuous_integrable variation
      (momentum derivativeDirection) (momentumContinuous derivativeDirection)
      derivativeDirection
  have derivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      derivativeTermIntegrable derivativeDirection
  have algebraicContinuous : Continuous algebraic :=
    p286GaugeConnectionAlgebraicCurrentCoefficient_continuous source
      configuration smooth nondegenerate direction
  have algebraicTermIntegrable : Integrable fun point =>
      variation point * algebraic point :=
    compactScalar_mul_continuous_integrable variation algebraic
      algebraicContinuous
  have momentumDerivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        variation point * momentumDerivative derivativeDirection point :=
    fun derivativeDirection =>
      compactScalar_mul_continuous_integrable variation
        (momentumDerivative derivativeDirection)
        (momentumDerivativeContinuous derivativeDirection)
  have momentumDerivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        variation point * momentumDerivative derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      momentumDerivativeTermIntegrable derivativeDirection
  have weakDirection := weakEquation
    (scalarTimesP286GaugeConnectionVariation direction variation)
  rw [show (fun point : BasePoint =>
      holonomicP286GaugeConnectionFirstVariationDensity source 0 configuration
        (scalarTimesP286GaugeConnectionVariation direction variation) point) =
      fun point =>
        (∑ derivativeDirection : LorentzianIndex,
          fieldDirectionalDerivative variation point derivativeDirection *
            momentum derivativeDirection point) +
          variation point * algebraic point by
    funext point
    exact holonomicP286GaugeConnectionFirstVariationDensity_scalarTimes source
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
    exact p286GaugeConnectionBFDifferentialMomentum_integrationByParts
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
          p286GaugeConnectionEulerLagrangeCoefficient source configuration
            direction point) =
      fun point =>
        variation point * algebraic point -
          ∑ derivativeDirection : LorentzianIndex,
            variation point * momentumDerivative derivativeDirection point := by
    funext point
    unfold p286GaugeConnectionEulerLagrangeCoefficient
      p286GaugeConnectionBFDifferentialMomentumDivergence
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

def CanonicalP286GaugeConnectionPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionEulerLagrangeCoefficient source configuration
      direction = 0

theorem canonicalP286GaugeConnectionWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalP286GaugeConnectionWeakEquation source
      configuration) :
    CanonicalP286GaugeConnectionPointwiseEquation source configuration := by
  intro direction
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (p286GaugeConnectionEulerLagrangeCoefficient source configuration
      direction)
    (p286GaugeConnectionEulerLagrangeCoefficient_continuous source
      configuration smooth nondegenerate direction)
  intro variation
  exact canonicalP286GaugeConnectionWeakEquation_direction_integral source
    configuration smooth nondegenerate weakEquation direction variation

end

end SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionPointwiseEquation
