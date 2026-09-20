import H0mework.Physics.Matter.MatterVariation
import H0mework.Physics.GaugeAction.P286GaugeConnectionMomentumRegularity

/-!
# S9-C3c1b: pointwise adjoint matter equation by genuine IBP

The primitive matter variation is specialized to a compact smooth scalar bump
times an arbitrary constant direction in the actual matter-coordinate space.
Its covariant derivative is proved to split into the derivative of the bump
and the algebraic Lorentz/P286 action on that direction.

The coefficient of the bump derivative is a fermion momentum generated from
the dynamic inverse coframe and the independent conjugate field.  Its `C∞`
regularity is proved from primitive smoothness and nondegeneracy rather than
accepted as a current or regularity receipt.  Genuine four-dimensional
compact-support integration by parts and the internally proved smooth-bump
fundamental lemma then turn the weak equation into the pointwise adjoint
directional Euler--Lagrange equation.
-/

namespace SaturationMonoid.PhysicsCore.StageNineMatterPointwiseEquation

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
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineConjugateMatterVariation
open StageNineMatterVariation
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorBreakingYukawa
open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open DiracCliffordRepresentation
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

def scalarTimesMatterVariation
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation MatterCoordinateCarrier where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

@[simp] theorem scalarTimesMatterVariation_apply
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint) :
    scalarTimesMatterVariation direction variation point =
      variation point • direction :=
  rfl

theorem matterVariationCoordinateDerivative_scalarTimes
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint)
    (derivativeDirection : LorentzianIndex) :
    matterVariationCoordinateDerivative
        (scalarTimesMatterVariation direction variation) point
        derivativeDirection =
      fieldDirectionalDerivative variation point derivativeDirection •
        direction := by
  have differentiable : DifferentiableAt ℝ
      (variation : BasePoint → ℝ) point :=
    (variation.smooth.differentiable (by simp)).differentiableAt
  unfold matterVariationCoordinateDerivative fieldDirectionalDerivative
  change
    (fderiv ℝ (fun candidate => variation candidate • direction) point)
        (coordinateDirection derivativeDirection) = _
  rw [fderiv_smul_const differentiable]
  rfl

def holonomicMatterVariationAlgebraicDirection
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) (point : BasePoint)
    (formDirection : LorentzianIndex) : DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
      (diracSpinConnectionLift
        (configuration.gravityConnection point) formDirection)
      (matterCoordinateEquiv.symm direction) +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed
        (configuration.gaugeConnection point formDirection))
      (matterCoordinateEquiv.symm direction)

theorem holonomicMatterVariationCovariantDerivative_scalarTimes
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint)
    (formDirection : LorentzianIndex) :
    holonomicMatterVariationCovariantDerivative configuration
        (scalarTimesMatterVariation direction variation) point formDirection =
      fieldDirectionalDerivative variation point formDirection •
          matterCoordinateEquiv.symm direction +
        variation point •
          holonomicMatterVariationAlgebraicDirection configuration direction
            point formDirection := by
  unfold holonomicMatterVariationCovariantDerivative
    holonomicMatterVariationAlgebraicDirection
  rw [matterVariationCoordinateDerivative_scalarTimes]
  simp only [scalarTimesMatterVariation_apply,
    matterCoordinateEquiv_symm_real_smul]
  rw [diracMatrixMatterAction_real_smul,
    diracExteriorMotherLieAction_matter_real_smul]
  module

def matterDifferentialVariationVector
    (_source : SmoothUnifiedSource) (_point : BasePoint)
    (field : StageNineContinuumPointField)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) : DiracExteriorMatterCarrier :=
  Complex.I • diracMatrixMatterAction
    (inverseCoframeDiracGamma
      { coframe := field.coframe, derivative := 0 } derivativeDirection)
    (matterCoordinateEquiv.symm direction)

def matterAlgebraicVariationVector
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) (point : BasePoint) :
    DiracExteriorMatterCarrier :=
  matterFieldVariationVector source point
    (toContinuumPointField configuration point)
    (matterCoordinateEquiv.symm direction)
    (holonomicMatterVariationAlgebraicDirection configuration direction point)

theorem complex_smul_real_smul_comm
    (complex : ℂ) (real : ℝ) (matter : DiracExteriorMatterCarrier) :
    complex • (real • matter) = real • (complex • matter) := by
  change complex • ((real : ℂ) • matter) =
    (real : ℂ) • (complex • matter)
  module

theorem matter_real_smul_add
    (real : ℝ) (first second : DiracExteriorMatterCarrier) :
    real • (first + second) = real • first + real • second := by
  change (real : ℂ) • (first + second) =
    (real : ℂ) • first + (real : ℂ) • second
  exact smul_add (real : ℂ) first second

theorem matterGaugeKineticSum_coordinateDerivativeDirections
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (direction : MatterCoordinateCarrier)
    (coefficient : LorentzianIndex → ℝ) :
    matterGaugeKineticSum source 0 point field
        (fun derivativeDirection =>
          coefficient derivativeDirection •
            matterCoordinateEquiv.symm direction) =
      ∑ derivativeDirection : LorentzianIndex,
        coefficient derivativeDirection •
          diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := field.coframe, derivative := 0 }
              derivativeDirection)
            (matterCoordinateEquiv.symm direction) := by
  rw [matterGaugeKineticSum_zeroChart]
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact diracMatrixMatterAction_real_smul _ _ _

theorem matterFieldVariationVector_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint) :
    matterFieldVariationVector source point
        (toContinuumPointField configuration point)
        (matterCoordinateEquiv.symm
          (scalarTimesMatterVariation direction variation point))
        (holonomicMatterVariationCovariantDerivative configuration
          (scalarTimesMatterVariation direction variation) point) =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection •
          matterDifferentialVariationVector source point
            (toContinuumPointField configuration point) direction
            derivativeDirection) +
        variation point •
          matterAlgebraicVariationVector source configuration direction point := by
  simp only [scalarTimesMatterVariation_apply]
  rw [matterCoordinateEquiv_symm_real_smul]
  have covariantDerivativeEquality :
      holonomicMatterVariationCovariantDerivative configuration
          (scalarTimesMatterVariation direction variation) point =
        (fun formDirection =>
          fieldDirectionalDerivative variation point formDirection •
            matterCoordinateEquiv.symm direction) +
          variation point •
            holonomicMatterVariationAlgebraicDirection configuration direction
              point := by
    funext formDirection
    exact holonomicMatterVariationCovariantDerivative_scalarTimes configuration
      direction variation point formDirection
  unfold matterDifferentialVariationVector matterAlgebraicVariationVector
    matterFieldVariationVector
  rw [covariantDerivativeEquality, matterGaugeKineticSum_add,
    matterGaugeKineticSum_real_smul,
    matterGaugeKineticSum_coordinateDerivativeDirections,
    chiralExteriorYukawaAction_matter_real_smul]
  rw [smul_add, Finset.smul_sum]
  simp only [complex_smul_real_smul_comm, matter_real_smul_add]
  abel

def matterDifferentialMomentum
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (configuration.conjugateMatter point
      (matterDifferentialVariationVector source point
        (toContinuumPointField configuration point) direction
        derivativeDirection)).re

def matterAlgebraicDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (configuration.conjugateMatter point
      (matterAlgebraicVariationVector source configuration direction point)).re

theorem matterDual_real_smul
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) (matter : DiracExteriorMatterCarrier) :
    dual (parameter • matter) = (parameter : ℂ) * dual matter := by
  change dual ((parameter : ℂ) • matter) =
    (parameter : ℂ) • dual matter
  exact dual.map_smul (parameter : ℂ) matter

theorem holonomicMatterFirstVariationDensity_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) (point : BasePoint) :
    holonomicMatterFirstVariationDensity source configuration
        (scalarTimesMatterVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          matterDifferentialMomentum source configuration direction
            derivativeDirection point) +
        variation point *
          matterAlgebraicDirectionalCoefficient source configuration direction
            point := by
  unfold holonomicMatterFirstVariationDensity matterFirstVariationDensity
    matterDifferentialMomentum matterAlgebraicDirectionalCoefficient
  rw [matterFieldVariationVector_scalarTimes]
  rw [map_add, map_sum]
  simp only [Complex.add_re, Complex.re_sum]
  simp_rw [matterDual_real_smul]
  simp_rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [mul_add, Finset.mul_sum]
  simp only [toContinuumPointField]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro derivativeDirection _
    ring
  · ring

/-! ## Smooth differential momentum -/

theorem holonomicInverseCoframeDiracGamma_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      inverseCoframeDiracGamma
        { coframe := configuration.coframe point, derivative := 0 } direction := by
  have inverseSmooth := holonomicCoframe_inv_contDiff configuration smooth
    nondegenerate
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  unfold inverseCoframeDiracGamma
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiff.sum
  intro internal _
  have inverseEntrySmooth : ContDiff ℝ ∞ fun point =>
      (configuration.coframe point)⁻¹ direction internal :=
    contDiff_pi.mp (contDiff_pi.mp inverseSmooth direction) internal
  exact (Complex.ofRealCLM.contDiff.comp inverseEntrySmooth).mul contDiff_const

theorem matterDifferentialVariationVector_coordinate_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (matterDifferentialVariationVector source point
          (toContinuumPointField configuration point) direction
          derivativeDirection) := by
  have gammaSmooth := holonomicInverseCoframeDiracGamma_contDiff configuration
    smooth nondegenerate derivativeDirection
  let actionLinear : DiracMatrix →L[ℝ] MatterCoordinateCarrier :=
    ((LinearMap.flip diracMatrixMatterCoordinateBilinear)
      direction).toContinuousLinearMap.restrictScalars ℝ
  have actionSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            derivativeDirection)
          (matterCoordinateEquiv.symm direction)) := by
    change ContDiff ℝ ∞ fun point => actionLinear
      (inverseCoframeDiracGamma
        { coframe := configuration.coframe point, derivative := 0 }
        derivativeDirection)
    exact actionLinear.contDiff.comp gammaSmooth
  have withISmooth : ContDiff ℝ ∞ fun point =>
      Complex.I • matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            derivativeDirection)
          (matterCoordinateEquiv.symm direction)) :=
    (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint => (Complex.I : ℂ)).smul
      actionSmooth
  unfold matterDifferentialVariationVector
  simpa only [toContinuumPointField, map_smul] using withISmooth

theorem matterDifferentialMomentum_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiff ℝ ∞
      (matterDifferentialMomentum source configuration direction
        derivativeDirection) := by
  let vector := fun point =>
    matterDifferentialVariationVector source point
      (toContinuumPointField configuration point) direction derivativeDirection
  have vectorCoordinateSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (vector point) :=
    matterDifferentialVariationVector_coordinate_contDiff source configuration
      smooth nondegenerate direction derivativeDirection
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
    have vectorCoordinateEntrySmooth : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv (vector point) index :=
      coordinateLinear.contDiff.comp vectorCoordinateSmooth
    have dualCoordinateSmooth : ContDiff ℝ ∞ fun point =>
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) :=
      smooth.2.2.2.2.2.2.2.2 index
    exact vectorCoordinateEntrySmooth.mul dualCoordinateSmooth
  have dualPairingSmooth : ContDiff ℝ ∞ fun point =>
      configuration.conjugateMatter point (vector point) :=
    by
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
  have volumeSmooth := holonomicGeneratedVolumeDensity_contDiff configuration
    smooth nondegenerate
  unfold matterDifferentialMomentum
  simpa only [generatedVolumeDensity, toContinuumPointField, vector] using
    volumeSmooth.mul realPairingSmooth

/-! ## Algebraic coefficient and Euler--Lagrange residual -/

set_option maxHeartbeats 1200000 in
theorem holonomicMatterVariationAlgebraicDirection_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : MatterCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (holonomicMatterVariationAlgebraicDirection configuration direction
          point formDirection) := by
  have directionCoordinateContinuous : Continuous fun _ : BasePoint =>
      matterCoordinateEquiv (matterCoordinateEquiv.symm direction) := by
    simpa only [matterCoordinateEquiv.apply_symm_apply] using
      (continuous_const : Continuous fun _ : BasePoint => direction)
  have spinContinuous := diracMatrixMatterCoordinate_raw_apply_continuous
    (fun point =>
      diracSpinConnectionLift (configuration.gravityConnection point)
        formDirection)
    (fun _ : BasePoint => matterCoordinateEquiv.symm direction)
    (holonomicGravitySpinLift_continuous configuration smooth formDirection)
    directionCoordinateContinuous
  have gaugeCoordinateContinuous : Continuous fun point =>
      p286CoordinateEquiv (configuration.gaugeConnection point formDirection) :=
    (smooth.2.2.2.2.1 formDirection).continuous
  have gaugeContinuous := matterP286ActionCoordinate_apply_continuous
    (fun point => p286CoordinateEquiv
      (configuration.gaugeConnection point formDirection))
    (fun _ : BasePoint => direction)
    gaugeCoordinateContinuous continuous_const
  unfold holonomicMatterVariationAlgebraicDirection
  simp only [map_add]
  exact spinContinuous.add (gaugeContinuous.congr fun point => by
    change
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (p286CoordinateEquiv
                  (configuration.gaugeConnection point formDirection))))
            (matterCoordinateEquiv.symm direction)) = _
    rw [p286CoordinateEquiv.symm_apply_apply])

theorem matterAlgebraicVariationVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterAlgebraicVariationVector source configuration direction point) := by
  have kineticSumContinuous : Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterVariationAlgebraicDirection configuration direction
            point)) := by
    have sumContinuous : Continuous fun point =>
        ∑ formDirection : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := configuration.coframe point, derivative := 0 }
                formDirection)
              (holonomicMatterVariationAlgebraicDirection configuration direction
                point formDirection)) := by
      apply continuous_finsetSum
      intro formDirection _
      exact diracMatrixMatterCoordinate_raw_apply_continuous _ _
        (holonomicInverseCoframeDiracGamma_continuous configuration smooth
          nondegenerate formDirection)
        (holonomicMatterVariationAlgebraicDirection_coordinate_continuous
          configuration smooth direction formDirection)
    exact sumContinuous.congr fun point => by
      unfold matterGaugeKineticSum matterDerivativeFrameRelative
      simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]
  have kineticWithIContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterVariationAlgebraicDirection configuration direction
            point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticSumContinuous).congr fun point => rfl
  have yukawaContinuous := chiralYukawaCoordinate_apply_continuous
    configuration.scalar (fun _ : BasePoint => direction)
    smooth.2.2.2.2.2.2.1.continuous continuous_const
  have actual := kineticWithIContinuous.add yukawaContinuous
  unfold matterAlgebraicVariationVector matterFieldVariationVector
  exact actual.congr fun point => by
    simp only [toContinuumPointField, Pi.add_apply]
    rw [map_add, map_smul]
    rfl

theorem matterAlgebraicDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous
      (matterAlgebraicDirectionalCoefficient source configuration direction) := by
  let vector := matterAlgebraicVariationVector source configuration direction
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    matterAlgebraicVariationVector_coordinate_continuous source configuration
      smooth nondegenerate direction
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
  have realPairingContinuous := Complex.continuous_re.comp dualPairingContinuous
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold matterAlgebraicDirectionalCoefficient
  exact (volumeContinuous.mul realPairingContinuous).congr fun point => by
    simp only [Pi.mul_apply, Function.comp_apply, toContinuumPointField, vector]

def matterDifferentialMomentumDivergence
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) (point : BasePoint) : ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (matterDifferentialMomentum source configuration direction
        derivativeDirection) point derivativeDirection

def matterEulerLagrangeDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier) (point : BasePoint) : ℝ :=
  matterAlgebraicDirectionalCoefficient source configuration direction point -
    matterDifferentialMomentumDivergence source configuration direction point

theorem matterDifferentialMomentumDivergence_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous
      (matterDifferentialMomentumDivergence source configuration direction) := by
  unfold matterDifferentialMomentumDivergence
  apply continuous_finsetSum
  intro derivativeDirection _
  have momentumSmooth := matterDifferentialMomentum_contDiff source configuration
    smooth nondegenerate direction derivativeDirection
  unfold fieldDirectionalDerivative
  exact (momentumSmooth.continuous_fderiv (by simp)).clm_apply continuous_const

theorem matterEulerLagrangeDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous
      (matterEulerLagrangeDirectionalCoefficient source configuration direction) :=
  (matterAlgebraicDirectionalCoefficient_continuous source configuration smooth
    nondegenerate direction).sub
      (matterDifferentialMomentumDivergence_continuous source configuration
        smooth nondegenerate direction)

/-! ## Genuine compact-support integration by parts -/

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

theorem matterDifferentialMomentum_integrationByParts
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (derivativeDirection : LorentzianIndex) :
    (∫ point : BasePoint,
      fieldDirectionalDerivative variation point derivativeDirection *
        matterDifferentialMomentum source configuration direction
          derivativeDirection point) =
      -(∫ point : BasePoint,
        variation point *
          fieldDirectionalDerivative
            (matterDifferentialMomentum source configuration direction
              derivativeDirection) point derivativeDirection) := by
  have actual := compactSupport_integrationByParts
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (matterDifferentialMomentum source configuration direction
      derivativeDirection)
    variation
    (matterDifferentialMomentum_contDiff source configuration smooth
      nondegenerate direction derivativeDirection)
    derivativeDirection
  simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    fieldDirectionalDerivative, mul_comm] using actual

theorem canonicalMatterWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalMatterWeakEquation source configuration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        matterEulerLagrangeDirectionalCoefficient source configuration direction
          point) = 0 := by
  let momentum := fun derivativeDirection : LorentzianIndex =>
    matterDifferentialMomentum source configuration direction
      derivativeDirection
  let momentumDerivative := fun derivativeDirection : LorentzianIndex =>
    fun point => fieldDirectionalDerivative (momentum derivativeDirection)
      point derivativeDirection
  let algebraic :=
    matterAlgebraicDirectionalCoefficient source configuration direction
  have momentumContinuous : ∀ derivativeDirection,
      Continuous (momentum derivativeDirection) := fun derivativeDirection =>
    (matterDifferentialMomentum_contDiff source configuration smooth
      nondegenerate direction derivativeDirection).continuous
  have momentumDerivativeContinuous : ∀ derivativeDirection,
      Continuous (momentumDerivative derivativeDirection) := by
    intro derivativeDirection
    have momentumSmooth := matterDifferentialMomentum_contDiff source
      configuration smooth nondegenerate direction derivativeDirection
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
    matterAlgebraicDirectionalCoefficient_continuous source configuration smooth
      nondegenerate direction
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
    (scalarTimesMatterVariation direction variation)
  rw [show (fun point : BasePoint =>
      holonomicMatterFirstVariationDensity source configuration
        (scalarTimesMatterVariation direction variation) point) =
    fun point =>
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point) +
        variation point * algebraic point by
    funext point
    exact holonomicMatterFirstVariationDensity_scalarTimes source configuration
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
    exact matterDifferentialMomentum_integrationByParts source configuration
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
          matterEulerLagrangeDirectionalCoefficient source configuration
            direction point) =
      fun point =>
        variation point * algebraic point -
          ∑ derivativeDirection : LorentzianIndex,
            variation point * momentumDerivative derivativeDirection point := by
    funext point
    unfold matterEulerLagrangeDirectionalCoefficient
      matterDifferentialMomentumDivergence algebraic momentumDerivative momentum
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

def CanonicalMatterPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ direction : MatterCoordinateCarrier,
    matterEulerLagrangeDirectionalCoefficient source configuration direction = 0

theorem canonicalMatterWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : CanonicalMatterWeakEquation source configuration) :
    CanonicalMatterPointwiseEquation source configuration := by
  intro direction
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (matterEulerLagrangeDirectionalCoefficient source configuration direction)
    (matterEulerLagrangeDirectionalCoefficient_continuous source configuration
      smooth nondegenerate direction)
  intro variation
  exact canonicalMatterWeakEquation_direction_integral source configuration
    smooth nondegenerate weakEquation direction variation

theorem canonicalMatterActionStationary_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalMatterActionStationary source configuration) :
    CanonicalMatterPointwiseEquation source configuration := by
  apply canonicalMatterWeakEquation_implies_pointwiseEquation source
    configuration smooth nondegenerate
  exact canonicalMatterActionStationary_implies_weakEquation source
    configuration smooth nondegenerate densityIntegrable stationary

end

end SaturationMonoid.PhysicsCore.StageNineMatterPointwiseEquation
