import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.Matter.MatterPointwiseEquation
import H0mework.Physics.GaugeAction.P286GaugeConnectionMomentumRegularity
import H0mework.Physics.Geometry.ScalarPointwiseEquation

/-!
# Stage-9 P286 algebraic-current regularity

The P286 temporal-Gauss tangency gate differentiates the algebraic connection
current on an already generated actual.  The historical pointwise-equation
API exposed continuity only.  This module proves the missing smoothness from
the primitive smooth fields and the nondegenerate coframe:

```text
smooth primitive actual + nondegenerate coframe
→ smooth gauge-BF algebraic source
→ smooth scalar current
→ smooth matter current
→ smooth complete P286 algebraic current.
```

No equation, current-conservation receipt, residual zero, target tangent, or
repair is accepted.  These are regularity transporters only.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionAlgebraicCurrentRegularity

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeScalarMatterRegularity
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterPointwiseEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance p286AlgebraicRegularityModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286AlgebraicRegularityCoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Gauge-BF algebraic source -/

theorem holonomicP286GaugeConnectionCoordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞
      (holonomicP286GaugeConnectionCoordinate configuration) := by
  apply contDiff_pi'
  intro direction
  exact smooth.2.2.2.2.1 direction

theorem p286GaugeConnectionAlgebraicCurvatureDirection_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeConnectionAlgebraicCurvatureDirection
        configuration direction point := by
  apply contDiff_pi'
  intro pair
  have connectionSmooth :=
    holonomicP286GaugeConnectionCoordinate_contDiff configuration smooth
  have firstBracket : ContDiff ℝ ∞ fun point =>
      p286CoordinateLieBracket
        (direction (pairFirst pair))
        (holonomicP286GaugeConnectionCoordinate configuration point
          (pairSecond pair)) := by
    exact
      (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
          direction (pairFirst pair))).clm_apply
        (contDiff_pi.mp connectionSmooth (pairSecond pair))
  have secondBracket : ContDiff ℝ ∞ fun point =>
      p286CoordinateLieBracket
        (holonomicP286GaugeConnectionCoordinate configuration point
          (pairFirst pair))
        (direction (pairSecond pair)) := by
    exact
      (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_pi.mp connectionSmooth (pairFirst pair))).clm_apply
        (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
          direction (pairSecond pair))
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  exact firstBracket.add secondBracket

/-- Smooth coframe-Hodge pairing for two independently smooth P286 two-form
fields.  This is the polynomial core used below; it assumes no equation or
residual-zero law. -/
theorem p286GaugeAuxiliaryHodgePairingPolynomial_variable_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (first residual : BasePoint → P286GaugeTwoForm)
    (firstSmooth : ContDiff ℝ ∞ first)
    (residualSmooth : ContDiff ℝ ∞ residual) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeAuxiliaryHodgePairingPolynomial
        (configuration.coframe point) (first point) (residual point) := by
  have firstTransformSmooth :=
    holonomicLiftCoframeTwoFormLinear_apply_contDiff configuration smooth
      first firstSmooth
  have residualTransformSmooth :=
    holonomicLiftCoframeTwoFormLinear_apply_contDiff configuration smooth
      residual residualSmooth
  have hodgeResidualTransformSmooth :=
    liftGaugeTwoFormOperator_apply_contDiff_p286 lorentzianCoframeHodge
      (fun point => liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point))
        (residual point))
      residualTransformSmooth
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  apply ContDiff.sum
  intro pair _
  apply contDiff_const.mul
  exact p286CoordinateLiePairing_apply_contDiff
    (fun point => liftGaugeTwoFormOperator
      (coframeTwoFormLinear (configuration.coframe point))
      (first point) pair)
    (fun point => liftGaugeTwoFormOperator lorentzianCoframeHodge
      (liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point))
        (residual point)) pair)
    (contDiff_pi.mp firstTransformSmooth pair)
    (contDiff_pi.mp hodgeResidualTransformSmooth pair)

/-- Smooth BF momentum with a smooth, point-dependent test two-form. -/
theorem p286GaugeConnectionBFDifferentialMomentum_variable_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : BasePoint → P286GaugeTwoForm)
    (directionSmooth : ContDiff ℝ ∞ direction) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeConnectionBFDifferentialMomentum configuration
        (direction point) point := by
  have auxiliarySmooth :=
    holonomicP286GaugeAuxiliaryCoordinate_contDiff configuration smooth
  have auxiliaryTransformSmooth :=
    holonomicLiftCoframeTwoFormLinear_apply_contDiff configuration smooth
      (holonomicP286GaugeAuxiliaryCoordinate configuration) auxiliarySmooth
  have directionTransformSmooth :=
    holonomicLiftCoframeTwoFormLinear_apply_contDiff configuration smooth
      direction directionSmooth
  have hodgeDirectionTransformSmooth :=
    liftGaugeTwoFormOperator_apply_contDiff_p286 lorentzianCoframeHodge
      (fun point => liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point))
        (direction point))
      directionTransformSmooth
  have volumeSmooth := holonomicGeneratedVolumeDensity_contDiff
    configuration smooth nondegenerate
  unfold p286GaugeConnectionBFDifferentialMomentum
    p286GaugeAuxiliaryHodgePairingPolynomial
  apply volumeSmooth.mul
  apply ContDiff.sum
  intro pair _
  apply contDiff_const.mul
  exact p286CoordinateLiePairing_apply_contDiff
    (fun point => liftGaugeTwoFormOperator
      (coframeTwoFormLinear (configuration.coframe point))
      (holonomicP286GaugeAuxiliaryCoordinate configuration point) pair)
    (fun point => liftGaugeTwoFormOperator lorentzianCoframeHodge
      (liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point))
        (direction point)) pair)
    (contDiff_pi.mp auxiliaryTransformSmooth pair)
    (contDiff_pi.mp hodgeDirectionTransformSmooth pair)

theorem p286GaugeBFAlgebraicCoefficient_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞
      (p286GaugeBFAlgebraicCoefficient configuration direction) := by
  rw [show
    p286GaugeBFAlgebraicCoefficient configuration direction =
      fun point =>
        p286GaugeConnectionBFDifferentialMomentum configuration
          (p286GaugeConnectionAlgebraicCurvatureDirection
            configuration direction point)
          point by
    funext point
    exact
      (p286GaugeConnectionBFDifferentialMomentum_eq_density
        configuration nondegenerate
        (p286GaugeConnectionAlgebraicCurvatureDirection
          configuration direction point)
        point).symm]
  exact p286GaugeConnectionBFDifferentialMomentum_variable_contDiff
    configuration smooth nondegenerate
    (p286GaugeConnectionAlgebraicCurvatureDirection
      configuration direction)
    (p286GaugeConnectionAlgebraicCurvatureDirection_contDiff
      configuration smooth direction)

/-! ## Scalar current -/

theorem holonomicScalarGaugeConnectionConstantDirection_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞ fun point =>
      holonomicScalarGaugeConnectionVariation configuration
        (fun _ => direction) point := by
  apply contDiff_pi'
  intro formDirection
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have actual :=
    (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
      |>.toContinuousBilinearMap |>.contDiff |>.comp
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
        direction formDirection)).clm_apply scalarSmooth
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  change ContDiff ℝ ∞ fun point =>
    scalarMotherLieAction
      (p286LieBlockEmbed
        (p286CoordinateEquiv.symm (direction formDirection)))
      (configuration.scalar point)
  exact actual

theorem p286ScalarCurrentCoefficient_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞
      (p286ScalarCurrentCoefficient source configuration direction) := by
  have volumeSmooth := holonomicGeneratedVolumeDensity_contDiff
    configuration smooth nondegenerate
  have metricInverseSmooth := holonomicLorentzianMetric_inv_contDiff
    configuration smooth nondegenerate
  have variationSmooth :=
    holonomicScalarGaugeConnectionConstantDirection_contDiff
      configuration smooth direction
  unfold p286ScalarCurrentCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField,
    scalarFrameRelativeCovariantDerivative,
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
  · exact scalarCoordinatePairingRe_apply_contDiff _ _
      (contDiff_pi.mp variationSmooth first)
      (holonomicScalarCovariantDerivative_contDiff configuration smooth second)
  · exact scalarCoordinatePairingRe_apply_contDiff _ _
      (holonomicScalarCovariantDerivative_contDiff configuration smooth first)
      (contDiff_pi.mp variationSmooth second)

/-! ## Exterior-matter current -/

theorem holonomicMatterGaugeConnectionConstantDirection_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (holonomicMatterGaugeConnectionVariation configuration
          (fun _ => direction) point formDirection) := by
  have matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1
  have actual :=
    (StageNineP286GaugeConnectionVariationDensity.matterP286ActionCoordinateBilinear
      |>.toContinuousBilinearMap |>.contDiff |>.comp
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
        direction formDirection)).clm_apply matterSmooth
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  change ContDiff ℝ ∞ fun point =>
    matterCoordinateEquiv
      (diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm (direction formDirection)))
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv (configuration.matter point)))) at actual
  simpa only [matterCoordinateEquiv.symm_apply_apply] using actual

theorem p286MatterCurrentCoefficient_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞
      (p286MatterCurrentCoefficient source configuration direction) := by
  let vector : BasePoint → DiracExteriorMatterCarrier := fun point =>
    matterGaugeConnectionVariationVector source 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterGaugeConnectionVariation configuration
        (fun _ => direction) point)
  have gammaVariationCoordinateSmooth
      (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (holonomicMatterGaugeConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
    have variationSmooth :=
      holonomicMatterGaugeConnectionConstantDirection_coordinate_contDiff
        configuration smooth direction formDirection
    have inverseSmooth :=
      holonomicCoframe_inv_contDiff configuration smooth nondegenerate
    rw [show (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (holonomicMatterGaugeConnectionVariation configuration
              (fun _ => direction) point formDirection))) =
      fun point =>
        ∑ internal : LorentzianIndex,
          ((configuration.coframe point)⁻¹ formDirection internal : ℂ) •
            matterCoordinateEquiv
              (diracMatrixMatterAction (diracGamma internal)
                (holonomicMatterGaugeConnectionVariation configuration
                  (fun _ => direction) point formDirection)) by
      funext point
      let variation :=
        holonomicMatterGaugeConnectionVariation configuration
          (fun _ => direction) point formDirection
      have expansion (indices : Finset LorentzianIndex) :
          matterCoordinateEquiv
              (diracMatrixMatterAction
                (∑ internal ∈ indices,
                  ((configuration.coframe point)⁻¹
                    formDirection internal : ℂ) • diracGamma internal)
                variation) =
            ∑ internal ∈ indices,
              ((configuration.coframe point)⁻¹ formDirection internal : ℂ) •
                matterCoordinateEquiv
                  (diracMatrixMatterAction (diracGamma internal)
                    variation) := by
        induction indices using Finset.induction_on with
        | empty =>
            simp only [Finset.sum_empty]
            have actionZero :
                diracMatrixMatterAction 0 variation = 0 := by
              funext row
              simp [diracMatrixMatterAction]
            rw [actionZero, map_zero]
        | @insert internal indices absent inductionHypothesis =>
            simp only [Finset.sum_insert absent]
            rw [
              StageNineP286GaugeConnectionVariationDensity.diracMatrixMatterAction_add_matrix,
              map_add,
              StageNineP286GaugeConnectionVariationDensity.diracMatrixMatterAction_smul_matrix,
              map_smul,
              inductionHypothesis]
      simpa only [inverseCoframeDiracGamma, Finset.sum_filter,
        Finset.filter_true_of_mem] using expansion Finset.univ]
    apply ContDiff.sum
    intro internal _
    have coefficientSmooth : ContDiff ℝ ∞ fun point =>
        ((configuration.coframe point)⁻¹ formDirection internal : ℂ) := by
      exact Complex.ofRealCLM.contDiff.comp
        (contDiff_pi.mp (contDiff_pi.mp inverseSmooth formDirection) internal)
    let actionLinear : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
      (StageNineCoframeScalarMatterRegularity.diracMatrixMatterCoordinateRealBilinear
        (diracGamma internal)).toContinuousLinearMap
    have actionSmooth : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma internal)
            (holonomicMatterGaugeConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
      have actual := actionLinear.contDiff.comp variationSmooth
      change ContDiff ℝ ∞
        ((fun matter =>
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma internal)
              (matterCoordinateEquiv.symm matter))) ∘
          fun point =>
            matterCoordinateEquiv
              (holonomicMatterGaugeConnectionVariation configuration
                (fun _ => direction) point formDirection)) at actual
      rw [show
        ((fun matter =>
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma internal)
              (matterCoordinateEquiv.symm matter))) ∘
          fun point =>
            matterCoordinateEquiv
              (holonomicMatterGaugeConnectionVariation configuration
                (fun _ => direction) point formDirection)) =
        fun point =>
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma internal)
              (holonomicMatterGaugeConnectionVariation configuration
                (fun _ => direction) point formDirection)) by
        funext point
        simp only [Function.comp_apply,
          matterCoordinateEquiv.symm_apply_apply]] at actual
      exact actual
    exact coefficientSmooth.smul actionSmooth
  have sumSmooth : ContDiff ℝ ∞ fun point =>
      ∑ formDirection : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (holonomicMatterGaugeConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
    apply ContDiff.sum
    intro formDirection _
    exact gammaVariationCoordinateSmooth formDirection
  have vectorCoordinateSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (vector point) := by
    have withISmooth : ContDiff ℝ ∞ fun point =>
        Complex.I •
          ∑ formDirection : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction
                (inverseCoframeDiracGamma
                  { coframe := configuration.coframe point, derivative := 0 }
                  formDirection)
                (holonomicMatterGaugeConnectionVariation configuration
                  (fun _ => direction) point formDirection)) :=
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint => Complex.I).smul
        sumSmooth
    dsimp [vector]
    unfold matterGaugeConnectionVariationVector matterGaugeKineticSum
      matterDerivativeFrameRelative
    simp only [toContinuumPointField, matterFrameRelative_zeroChart,
      map_sum, map_smul]
    exact withISmooth
  have pairingSumSmooth : ContDiff ℝ ∞ fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply ContDiff.sum
    intro index _
    let coordinateLinear : MatterCoordinateCarrier →L[ℝ] ℂ :=
      (PiLp.projₗ (𝕜 := ℂ) 2
        (fun _ : MatterCoordinateIndex => ℂ) index)
        |>.toContinuousLinearMap |>.restrictScalars ℝ
    have vectorEntrySmooth : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv (vector point) index :=
      coordinateLinear.contDiff.comp vectorCoordinateSmooth
    exact vectorEntrySmooth.mul (smooth.2.2.2.2.2.2.2.2 index)
  have dualPairingSmooth : ContDiff ℝ ∞ fun point =>
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
    exact pairingSumSmooth
  have realPairingSmooth : ContDiff ℝ ∞ fun point =>
      (configuration.conjugateMatter point (vector point)).re :=
    Complex.reCLM.contDiff.comp dualPairingSmooth
  have volumeSmooth := holonomicGeneratedVolumeDensity_contDiff
    configuration smooth nondegenerate
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart]
  change ContDiff ℝ ∞ fun point =>
    |Matrix.det (configuration.coframe point)| *
      (configuration.conjugateMatter point (vector point)).re
  exact volumeSmooth.mul realPairingSmooth

/-! ## Complete algebraic current -/

theorem p286GaugeConnectionAlgebraicCurrentCoefficient_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞
      (p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        direction) := by
  rw [show
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        direction =
      p286GaugeBFAlgebraicCoefficient configuration direction +
        p286ScalarCurrentCoefficient source configuration direction +
        p286MatterCurrentCoefficient source configuration direction by
    funext point
    exact p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors
      source configuration direction point]
  exact
    ((p286GaugeBFAlgebraicCoefficient_contDiff configuration smooth
      nondegenerate direction).add
      (p286ScalarCurrentCoefficient_contDiff source configuration smooth
        nondegenerate direction)).add
      (p286MatterCurrentCoefficient_contDiff source configuration smooth
        nondegenerate direction)

end

end
  SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionAlgebraicCurrentRegularity
