import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.Lorentz.LorentzConnectionMomentumRegularity

/-!
# Stage-9 Lorentz algebraic-current regularity

The Lorentz temporal-Gauss tangency gate differentiates the complete
algebraic connection current on an already generated actual.  The historical
pointwise-equation API exposed continuity only.  This module derives the
missing smoothness from the primitive smooth fields and the nondegenerate
coframe:

```text
smooth primitive actual + nondegenerate coframe
→ smooth gravity-BF algebraic source
→ smooth exterior-matter spin source
→ smooth complete Lorentz algebraic current.
```

No equation, Ward identity, residual zero, target tangent, or repair is
accepted.  These are regularity transporters only.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineLorentzConnectionAlgebraicCurrentRegularity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeScalarMatterRegularity
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionVariationDensity
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance lorentzAlgebraicRegularityMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Gravity-BF algebraic source -/

/-- The algebraic Lorentz-curvature direction is smooth when the primitive
connection is smooth.  The test one-form is fixed and supplies no receipt. -/
theorem lorentzConnectionAlgebraicCurvatureDirection_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞ fun point =>
      lorentzConnectionAlgebraicCurvatureDirection
        configuration direction point := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  unfold lorentzConnectionAlgebraicCurvatureDirection
    lorentzConnectionAlgebraicCurvatureVariation
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.sum
  intro middle _
  exact
    (((contDiff_const.mul
          (smooth.2.1 (pairSecond spacetimePair) middle
            (pairSecond internalPair))).add
        ((smooth.2.1 (pairFirst spacetimePair)
            (pairFirst internalPair) middle).mul contDiff_const)).sub
      (contDiff_const.mul
        (smooth.2.1 (pairFirst spacetimePair) middle
          (pairSecond internalPair)))).sub
      ((smooth.2.1 (pairSecond spacetimePair)
        (pairFirst internalPair) middle).mul contDiff_const)

/-- Smooth Lorentz BF momentum with a smooth point-dependent physical
bivector direction. -/
theorem lorentzConnectionBFDifferentialMomentum_variable_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : BasePoint → PhysicalBivector)
    (directionSmooth : ContDiff ℝ ∞ direction) :
    ContDiff ℝ ∞ fun point =>
      lorentzConnectionBFDifferentialMomentum configuration
        (direction point) point := by
  have auxiliarySmooth :=
    holonomicGravityAuxiliary_contDiff configuration smooth
  have auxiliaryTransformSmooth :=
    holonomicGravityCoframeTwoFormLinear_apply_contDiff configuration smooth
      configuration.gravityAuxiliary auxiliarySmooth
  have directionTransformSmooth :=
    holonomicGravityCoframeTwoFormLinear_apply_contDiff configuration smooth
      direction directionSmooth
  have hodgeDirectionTransformSmooth :=
    holonomicGravityFixedHodge_apply_contDiff
      (fun point => fun internalPair =>
        coframeTwoFormLinear (configuration.coframe point)
          (direction point internalPair))
      directionTransformSmooth
  have volumeSmooth :=
    holonomicGeneratedVolumeDensity_contDiff configuration smooth
      nondegenerate
  unfold lorentzConnectionBFDifferentialMomentum
    gravityAuxiliaryHodgePairingPolynomial
  apply volumeSmooth.mul
  apply ContDiff.sum
  intro internalPair _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro spacetimePair _
  exact
    (contDiff_const.mul
      (contDiff_pi.mp
        (contDiff_pi.mp auxiliaryTransformSmooth internalPair)
        spacetimePair)).mul
      (contDiff_pi.mp
        (contDiff_pi.mp hodgeDirectionTransformSmooth internalPair)
        spacetimePair)

theorem lorentzGravityBFAlgebraicCoefficient_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞
      (lorentzGravityBFAlgebraicCoefficient configuration direction) := by
  rw [show
    lorentzGravityBFAlgebraicCoefficient configuration direction =
      fun point =>
        lorentzConnectionBFDifferentialMomentum configuration
          (lorentzConnectionAlgebraicCurvatureDirection
            configuration direction point)
          point by
    funext point
    exact
      (lorentzConnectionBFDifferentialMomentum_eq_density
        configuration nondegenerate
        (lorentzConnectionAlgebraicCurvatureDirection
          configuration direction point)
        point).symm]
  exact lorentzConnectionBFDifferentialMomentum_variable_contDiff
    configuration smooth nondegenerate
    (lorentzConnectionAlgebraicCurvatureDirection configuration direction)
    (lorentzConnectionAlgebraicCurvatureDirection_contDiff
      configuration smooth direction)

/-! ## Exterior-matter spin source -/

theorem holonomicMatterLorentzConstantDirection_coordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (holonomicMatterLorentzConnectionVariation configuration
          (fun _ => direction) point formDirection) := by
  have matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1
  have actual :=
    (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
        diracSpinConnectionLift
          (lorentzSkewConnectionOfBivectorOneForm direction)
          formDirection)).clm_apply matterSmooth
  unfold holonomicMatterLorentzConnectionVariation
  change ContDiff ℝ ∞ fun point =>
    matterCoordinateEquiv
      (diracMatrixMatterAction
        (diracSpinConnectionLift
          (lorentzSkewConnectionOfBivectorOneForm direction)
          formDirection)
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv (configuration.matter point)))) at actual
  simpa only [matterCoordinateEquiv.symm_apply_apply] using actual

theorem lorentzMatterSpinSourceCoefficient_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞
      (lorentzMatterSpinSourceCoefficient source configuration direction) := by
  let vector : BasePoint → DiracExteriorMatterCarrier := fun point =>
    matterGaugeConnectionVariationVector source 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterLorentzConnectionVariation configuration
        (fun _ => direction) point)
  have gammaVariationCoordinateSmooth
      (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (holonomicMatterLorentzConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
    have variationSmooth :=
      holonomicMatterLorentzConstantDirection_coordinate_contDiff
        configuration smooth direction formDirection
    have inverseSmooth :=
      holonomicCoframe_inv_contDiff configuration smooth nondegenerate
    rw [show (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (holonomicMatterLorentzConnectionVariation configuration
              (fun _ => direction) point formDirection))) =
      fun point =>
        ∑ internal : LorentzianIndex,
          ((configuration.coframe point)⁻¹ formDirection internal : ℂ) •
            matterCoordinateEquiv
              (diracMatrixMatterAction (diracGamma internal)
                (holonomicMatterLorentzConnectionVariation configuration
                  (fun _ => direction) point formDirection)) by
      funext point
      let variation :=
        holonomicMatterLorentzConnectionVariation configuration
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
        ((configuration.coframe point)⁻¹ formDirection internal : ℂ) :=
      Complex.ofRealCLM.contDiff.comp
        (contDiff_pi.mp
          (contDiff_pi.mp inverseSmooth formDirection) internal)
    let actionLinear : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
      (diracMatrixMatterCoordinateRealBilinear
        (diracGamma internal)).toContinuousLinearMap
    have actionSmooth : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma internal)
            (holonomicMatterLorentzConnectionVariation configuration
              (fun _ => direction) point formDirection)) := by
      have actual := actionLinear.contDiff.comp variationSmooth
      change ContDiff ℝ ∞
        ((fun matter =>
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma internal)
              (matterCoordinateEquiv.symm matter))) ∘
          fun point =>
            matterCoordinateEquiv
              (holonomicMatterLorentzConnectionVariation configuration
                (fun _ => direction) point formDirection)) at actual
      rw [show
        ((fun matter =>
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma internal)
              (matterCoordinateEquiv.symm matter))) ∘
          fun point =>
            matterCoordinateEquiv
              (holonomicMatterLorentzConnectionVariation configuration
                (fun _ => direction) point formDirection)) =
        fun point =>
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma internal)
              (holonomicMatterLorentzConnectionVariation configuration
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
            (holonomicMatterLorentzConnectionVariation configuration
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
                (holonomicMatterLorentzConnectionVariation configuration
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
      fun point =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector point) index *
            configuration.conjugateMatter point
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))) by
      funext point
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        matterDual_coordinate_expansion
          (configuration.conjugateMatter point)
          (matterCoordinateEquiv (vector point))]
    exact pairingSumSmooth
  have realPairingSmooth : ContDiff ℝ ∞ fun point =>
      (configuration.conjugateMatter point (vector point)).re :=
    Complex.reCLM.contDiff.comp dualPairingSmooth
  have volumeSmooth :=
    holonomicGeneratedVolumeDensity_contDiff configuration smooth
      nondegenerate
  unfold lorentzMatterSpinSourceCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart]
  change ContDiff ℝ ∞ fun point =>
    |Matrix.det (configuration.coframe point)| *
      (configuration.conjugateMatter point (vector point)).re
  exact volumeSmooth.mul realPairingSmooth

/-! ## Complete algebraic current -/

theorem lorentzConnectionAlgebraicSpinCurrentCoefficient_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞
      (lorentzConnectionAlgebraicSpinCurrentCoefficient source configuration
        direction) := by
  rw [show
    lorentzConnectionAlgebraicSpinCurrentCoefficient source configuration
        direction =
      lorentzGravityBFAlgebraicCoefficient configuration direction +
        lorentzMatterSpinSourceCoefficient source configuration direction by
    funext point
    exact lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors
      source configuration direction point]
  exact
    (lorentzGravityBFAlgebraicCoefficient_contDiff configuration smooth
      nondegenerate direction).add
      (lorentzMatterSpinSourceCoefficient_contDiff source configuration smooth
        nondegenerate direction)

end

end
  SaturationMonoid.PhysicsCore.StageNineLorentzConnectionAlgebraicCurrentRegularity
