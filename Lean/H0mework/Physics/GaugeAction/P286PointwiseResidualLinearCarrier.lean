import H0mework.Physics.GaugeAction.P286GaugeConnectionPointwiseEquation

/-!
# S9-C3h80: the full P286 pointwise residual is a linear carrier

The C3h79 commutator probe detects one nonzero evaluation of the P286
connection Euler--Lagrange residual.  One evaluation is not yet a support
classifier and cannot canonically select a repair jet.  This module closes the
missing typed boundary first: for every smooth nondegenerate configuration,
the complete P286 Euler--Lagrange coefficient is linear in the connection
direction.

The resulting map is an action-derived residual carrier

`P286GaugeOneForm →ₗ[ℝ] (BasePoint → ℝ)`.

It is a readout of the already-defined joint action.  It neither adds a source
slot nor chooses a repair direction, coefficient, branch, or inverse.  The
smoothness and nondegeneracy hypotheses are explicit because Mathlib's total
`fderiv` is not unconditionally additive on arbitrary functions.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286PointwiseResidualLinearCarrier

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open DiracExteriorMatterAction
open scoped ContDiff ComplexConjugate

noncomputable section

set_option maxHeartbeats 600000

private theorem scalarGaugeConnectionKineticFirstVariationDensity_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (first second : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source chart point field
        (first + second) =
      scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field first +
        scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field second := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [scalarFrameRelativeCovariantDerivative_add]
  simp only [Pi.add_apply, scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro firstDirection _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro secondDirection _
  ring

private theorem matterGaugeConnectionFirstVariationDensity_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (first second : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity source chart point field
        (first + second) =
      matterGaugeConnectionFirstVariationDensity source chart point field
          first +
        matterGaugeConnectionFirstVariationDensity source chart point field
          second := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [matterGaugeKineticSum_add, smul_add, map_add]
  exact Complex.add_re _ _

private theorem p286GaugeConnectionFirstVariationDensity_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (firstCurvature secondCurvature : P286GaugeTwoForm)
    (firstScalar secondScalar : LorentzianIndex → ScalarCoordinateCarrier)
    (firstMatter secondMatter :
      LorentzianIndex → DiracExteriorMatterCarrier) :
    p286GaugeConnectionFirstVariationDensity source chart point field
        (firstCurvature + secondCurvature)
        (firstScalar + secondScalar) (firstMatter + secondMatter) =
      p286GaugeConnectionFirstVariationDensity source chart point field
          firstCurvature firstScalar firstMatter +
        p286GaugeConnectionFirstVariationDensity source chart point field
          secondCurvature secondScalar secondMatter := by
  unfold p286GaugeConnectionFirstVariationDensity
  rw [p286GaugeBFCurvatureIncrementDensity_add,
    scalarGaugeConnectionKineticFirstVariationDensity_add,
    matterGaugeConnectionFirstVariationDensity_add]
  ring

private theorem p286GaugeConnectionFirstVariationDensity_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℝ) (curvature : P286GaugeTwoForm)
    (scalar : LorentzianIndex → ScalarCoordinateCarrier)
    (matter : LorentzianIndex → DiracExteriorMatterCarrier) :
    p286GaugeConnectionFirstVariationDensity source chart point field
        (parameter • curvature) (parameter • scalar) (parameter • matter) =
      parameter *
        p286GaugeConnectionFirstVariationDensity source chart point field
          curvature scalar matter := by
  unfold p286GaugeConnectionFirstVariationDensity
  rw [p286GaugeBFCurvatureIncrementDensity_smul,
    scalarGaugeConnectionKineticFirstVariationDensity_real_smul,
    matterGaugeConnectionFirstVariationDensity_real_smul]
  ring

private theorem p286GaugeExteriorDerivativeDirection_add
    (derivativeDirection : LorentzianIndex)
    (first second : P286GaugeOneForm) :
    p286GaugeExteriorDerivativeDirection derivativeDirection
        (first + second) =
      p286GaugeExteriorDerivativeDirection derivativeDirection first +
        p286GaugeExteriorDerivativeDirection derivativeDirection second := by
  funext pair
  unfold p286GaugeExteriorDerivativeDirection
  simp only [Pi.add_apply]
  split <;> split <;> module

private theorem p286GaugeExteriorDerivativeDirection_smul
    (derivativeDirection : LorentzianIndex)
    (parameter : ℝ) (direction : P286GaugeOneForm) :
    p286GaugeExteriorDerivativeDirection derivativeDirection
        (parameter • direction) =
      parameter •
        p286GaugeExteriorDerivativeDirection derivativeDirection direction := by
  funext pair
  unfold p286GaugeExteriorDerivativeDirection
  simp only [Pi.smul_apply]
  split <;> split <;> module

private theorem p286GaugeConnectionAlgebraicCurvatureDirection_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurvatureDirection configuration
        (first + second) point =
      p286GaugeConnectionAlgebraicCurvatureDirection configuration first
          point +
        p286GaugeConnectionAlgebraicCurvatureDirection configuration second
          point := by
  funext pair
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  simp only [Pi.add_apply]
  rw [p286CoordinateLieBracket_add_left,
    p286CoordinateLieBracket_add_right]
  module

private theorem p286GaugeConnectionAlgebraicCurvatureDirection_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ) (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurvatureDirection configuration
        (parameter • direction) point =
      parameter •
        p286GaugeConnectionAlgebraicCurvatureDirection configuration direction
          point := by
  funext pair
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  simp only [Pi.smul_apply]
  rw [p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right]
  module

private theorem holonomicScalarGaugeConnectionVariation_const_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm) (point : BasePoint) :
    holonomicScalarGaugeConnectionVariation configuration
        (fun _ => first + second) point =
      holonomicScalarGaugeConnectionVariation configuration (fun _ => first)
          point +
        holonomicScalarGaugeConnectionVariation configuration
          (fun _ => second) point := by
  funext formDirection
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.add_apply]
  rw [p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
    scalarMotherLieAction_add]

private theorem holonomicScalarGaugeConnectionVariation_const_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ) (direction : P286GaugeOneForm) (point : BasePoint) :
    holonomicScalarGaugeConnectionVariation configuration
        (fun _ => parameter • direction) point =
      parameter •
        holonomicScalarGaugeConnectionVariation configuration
          (fun _ => direction) point := by
  funext formDirection
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.smul_apply]
  rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_real_smul]

private theorem holonomicMatterGaugeConnectionVariation_const_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm) (point : BasePoint) :
    holonomicMatterGaugeConnectionVariation configuration
        (fun _ => first + second) point =
      holonomicMatterGaugeConnectionVariation configuration (fun _ => first)
          point +
        holonomicMatterGaugeConnectionVariation configuration
          (fun _ => second) point := by
  funext formDirection
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.add_apply]
  rw [p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
    diracExteriorMotherLieAction_add]
  rfl

private theorem holonomicMatterGaugeConnectionVariation_const_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ) (direction : P286GaugeOneForm) (point : BasePoint) :
    holonomicMatterGaugeConnectionVariation configuration
        (fun _ => parameter • direction) point =
      parameter •
        holonomicMatterGaugeConnectionVariation configuration
          (fun _ => direction) point := by
  funext formDirection
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.smul_apply]
  rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul]
  rfl

private theorem p286GaugeConnectionBFDifferentialMomentum_add
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (first second : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum configuration
        (first + second) =
      p286GaugeConnectionBFDifferentialMomentum configuration first +
        p286GaugeConnectionBFDifferentialMomentum configuration second := by
  funext point
  simp only [Pi.add_apply]
  rw [p286GaugeConnectionBFDifferentialMomentum_eq_density configuration
      nondegenerate,
    p286GaugeConnectionBFDifferentialMomentum_eq_density configuration
      nondegenerate,
    p286GaugeConnectionBFDifferentialMomentum_eq_density configuration
      nondegenerate,
    p286GaugeBFCurvatureIncrementDensity_add]
  ring

private theorem p286GaugeConnectionBFDifferentialMomentum_smul
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (parameter : ℝ) (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum configuration
        (parameter • direction) =
      parameter •
        p286GaugeConnectionBFDifferentialMomentum configuration direction := by
  funext point
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [p286GaugeConnectionBFDifferentialMomentum_eq_density configuration
      nondegenerate,
    p286GaugeConnectionBFDifferentialMomentum_eq_density configuration
      nondegenerate,
    p286GaugeBFCurvatureIncrementDensity_smul]
  ring

private theorem fieldDirectionalDerivative_add_smul
    (first second : BasePoint → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (firstScalar secondScalar : ℝ)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (firstScalar • first + secondScalar • second) point direction =
      firstScalar * fieldDirectionalDerivative first point direction +
        secondScalar * fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ
      (fun candidate =>
        firstScalar • first candidate + secondScalar • second candidate)
      point) (coordinateDirection direction) = _
  rw [fderiv_fun_add
      ((ContDiff.const_smul firstScalar firstSmooth).differentiable
        (by simp) point)
      ((ContDiff.const_smul secondScalar secondSmooth).differentiable
        (by simp) point)]
  change
    (fderiv ℝ (fun candidate => firstScalar * first candidate) point +
      fderiv ℝ (fun candidate => secondScalar * second candidate) point)
        (coordinateDirection direction) = _
  rw [fderiv_const_mul (firstSmooth.differentiable (by simp) point)
      firstScalar,
    fderiv_const_mul (secondSmooth.differentiable (by simp) point)
      secondScalar]
  rfl

private theorem p286GaugeConnectionAlgebraicCurrentCoefficient_add
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        (first + second) point =
      p286GaugeConnectionAlgebraicCurrentCoefficient source configuration first
          point +
        p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
          second point := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [p286GaugeConnectionAlgebraicCurvatureDirection_add,
    holonomicScalarGaugeConnectionVariation_const_add,
    holonomicMatterGaugeConnectionVariation_const_add,
    p286GaugeConnectionFirstVariationDensity_add]

private theorem p286GaugeConnectionAlgebraicCurrentCoefficient_smul
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ) (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        (parameter • direction) point =
      parameter *
        p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
          direction point := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [p286GaugeConnectionAlgebraicCurvatureDirection_smul,
    holonomicScalarGaugeConnectionVariation_const_smul,
    holonomicMatterGaugeConnectionVariation_const_smul,
    p286GaugeConnectionFirstVariationDensity_smul]

private theorem p286GaugeConnectionBFDifferentialMomentumDivergence_add
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (first second : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentumDivergence configuration
        (first + second) point =
      p286GaugeConnectionBFDifferentialMomentumDivergence configuration first
          point +
        p286GaugeConnectionBFDifferentialMomentumDivergence configuration
          second point := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [p286GaugeExteriorDerivativeDirection_add,
    p286GaugeConnectionBFDifferentialMomentum_add configuration nondegenerate]
  have firstSmooth := p286GaugeConnectionBFDifferentialMomentum_contDiff
    configuration smooth nondegenerate
    (p286GaugeExteriorDerivativeDirection derivativeDirection first)
  have secondSmooth := p286GaugeConnectionBFDifferentialMomentum_contDiff
    configuration smooth nondegenerate
    (p286GaugeExteriorDerivativeDirection derivativeDirection second)
  simpa using fieldDirectionalDerivative_add_smul
    (p286GaugeConnectionBFDifferentialMomentum configuration
      (p286GaugeExteriorDerivativeDirection derivativeDirection first))
    (p286GaugeConnectionBFDifferentialMomentum configuration
      (p286GaugeExteriorDerivativeDirection derivativeDirection second))
    firstSmooth secondSmooth 1 1 point derivativeDirection

private theorem p286GaugeConnectionBFDifferentialMomentumDivergence_smul
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (parameter : ℝ) (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentumDivergence configuration
        (parameter • direction) point =
      parameter *
        p286GaugeConnectionBFDifferentialMomentumDivergence configuration
          direction point := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [p286GaugeExteriorDerivativeDirection_smul,
    p286GaugeConnectionBFDifferentialMomentum_smul configuration
      nondegenerate]
  have momentumSmooth := p286GaugeConnectionBFDifferentialMomentum_contDiff
    configuration smooth nondegenerate
    (p286GaugeExteriorDerivativeDirection derivativeDirection direction)
  have scaledDerivative := fieldDirectionalDerivative_add_smul
    (p286GaugeConnectionBFDifferentialMomentum configuration
      (p286GaugeExteriorDerivativeDirection derivativeDirection direction))
    (p286GaugeConnectionBFDifferentialMomentum configuration
      (p286GaugeExteriorDerivativeDirection derivativeDirection direction))
    momentumSmooth momentumSmooth parameter 0 point derivativeDirection
  simpa only [zero_smul, add_zero, Pi.smul_apply, smul_eq_mul, zero_mul]
    using scaledDerivative

private theorem p286GaugeConnectionEulerLagrangeCoefficient_add
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (first second : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionEulerLagrangeCoefficient source configuration
        (first + second) point =
      p286GaugeConnectionEulerLagrangeCoefficient source configuration first
          point +
        p286GaugeConnectionEulerLagrangeCoefficient source configuration second
          point := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_add,
    p286GaugeConnectionBFDifferentialMomentumDivergence_add configuration
      smooth nondegenerate]
  ring

private theorem p286GaugeConnectionEulerLagrangeCoefficient_smul
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (parameter : ℝ) (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionEulerLagrangeCoefficient source configuration
        (parameter • direction) point =
      parameter *
        p286GaugeConnectionEulerLagrangeCoefficient source configuration
          direction point := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_smul,
    p286GaugeConnectionBFDifferentialMomentumDivergence_smul configuration
      smooth nondegenerate]
  ring

/-- The complete action-derived P286 connection Euler--Lagrange residual,
bundled as a real-linear map in the connection direction. -/
def p286GaugeConnectionEulerLagrangeLinearMap
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    P286GaugeOneForm →ₗ[ℝ] (BasePoint → ℝ) where
  toFun := p286GaugeConnectionEulerLagrangeCoefficient source configuration
  map_add' := by
    intro first second
    funext point
    exact p286GaugeConnectionEulerLagrangeCoefficient_add source configuration
      smooth nondegenerate first second point
  map_smul' := by
    intro parameter direction
    funext point
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using
      p286GaugeConnectionEulerLagrangeCoefficient_smul source configuration
        smooth nondegenerate parameter direction point

@[simp] theorem p286GaugeConnectionEulerLagrangeLinearMap_apply
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionEulerLagrangeLinearMap source configuration smooth
        nondegenerate direction point =
      p286GaugeConnectionEulerLagrangeCoefficient source configuration
        direction point :=
  rfl

/-- Point evaluation of the full residual carrier.  This is a dual readout,
not a selected repair direction. -/
def p286GaugeConnectionEulerLagrangeAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (point : BasePoint) : Module.Dual ℝ P286GaugeOneForm where
  toFun := fun direction =>
    p286GaugeConnectionEulerLagrangeLinearMap source configuration smooth
      nondegenerate direction point
  map_add' := by
    intro first second
    exact congrFun
      (map_add
        (p286GaugeConnectionEulerLagrangeLinearMap source configuration smooth
          nondegenerate) first second) point
  map_smul' := by
    intro parameter direction
    simpa only [Pi.smul_apply, RingHom.id_apply] using congrFun
      (map_smul
        (p286GaugeConnectionEulerLagrangeLinearMap source configuration smooth
          nondegenerate) parameter direction) point

@[simp] theorem p286GaugeConnectionEulerLagrangeAt_apply
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (point : BasePoint) (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeAt source configuration smooth
        nondegenerate point direction =
      p286GaugeConnectionEulerLagrangeCoefficient source configuration
        direction point :=
  rfl

end

end SaturationMonoid.PhysicsCore.StageNineP286PointwiseResidualLinearCarrier
