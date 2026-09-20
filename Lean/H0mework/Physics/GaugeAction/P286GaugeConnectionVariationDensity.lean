import H0mework.Physics.GaugeAction.P286GaugeConnectionActionVariation

/-!
# S9-C3a3: analytic control of the P286 connection variation density

The exact local polynomial from C3a2 is promoted here to honest analytic
data.  All curvature, scalar-current, and Dirac-current terms are proved
continuous from the primitive smooth configuration and one compactly
supported connection variation.  Compact support of the variation and its
actual first derivatives then generates integrability; no current,
integrability, or equation certificate is supplied at the theorem mouth.

The canonical generated chart `0` is used for the scalar and matter frame
readout.  Extension to arbitrary generated charts is a later gauge-covariance
transport step, not an extra premise hidden here.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariationDensity

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNinePlebanskiMultiplierVariation
open StageNineGravityAuxiliaryVariation
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

set_option maxHeartbeats 600000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

theorem scalarMotherLieAction_add_right
    (matrix : SU7MotherLieMatrix)
    (first second : ScalarCoordinateCarrier) :
    scalarMotherLieAction matrix (first + second) =
      scalarMotherLieAction matrix first +
        scalarMotherLieAction matrix second := by
  unfold scalarMotherLieAction
  simp only [map_add]

theorem scalarMotherLieAction_real_smul_right
    (matrix : SU7MotherLieMatrix) (parameter : ℝ)
    (scalar : ScalarCoordinateCarrier) :
    scalarMotherLieAction matrix (parameter • scalar) =
      parameter • scalarMotherLieAction matrix scalar := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  unfold scalarMotherLieAction
  simp only [map_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

theorem matterP286ActionCoordinate_add_right
    (matrix : P286CoordinateCarrier)
    (first second : MatterCoordinateCarrier) :
    matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
          (matterCoordinateEquiv.symm (first + second))) =
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
            (matterCoordinateEquiv.symm first)) +
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
            (matterCoordinateEquiv.symm second)) := by
  simp only [map_add]

theorem matterP286ActionCoordinate_real_smul_right
    (matrix : P286CoordinateCarrier) (parameter : ℝ)
    (matter : MatterCoordinateCarrier) :
    matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
          (matterCoordinateEquiv.symm (parameter • matter))) =
      parameter •
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
            (matterCoordinateEquiv.symm matter)) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [map_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

def scalarP286ActionBilinear :
    P286CoordinateCarrier →ₗ[ℝ]
      ScalarCoordinateCarrier →ₗ[ℝ] ScalarCoordinateCarrier where
  toFun matrix :=
    { toFun := fun scalar =>
        scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix)) scalar
      map_add' := by
        intro first second
        exact scalarMotherLieAction_add_right _ _ _
      map_smul' := by
        intro parameter scalar
        exact scalarMotherLieAction_real_smul_right _ _ _ }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro scalar
    change
      scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm (first + second)))
          scalar =
        scalarMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm first)) scalar +
          scalarMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm second)) scalar
    rw [p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
      scalarMotherLieAction_add]
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro scalar
    change
      scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm (parameter • matrix)))
          scalar =
        parameter • scalarMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix)) scalar
    rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
      scalarMotherLieAction_real_smul]

def matterP286ActionCoordinateBilinear :
    P286CoordinateCarrier →ₗ[ℝ]
      MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun matrix :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        exact matterP286ActionCoordinate_add_right _ _ _
      map_smul' := by
        intro parameter matter
        exact matterP286ActionCoordinate_real_smul_right _ _ _ }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm (first + second)))
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed (p286CoordinateEquiv.symm first))
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed (p286CoordinateEquiv.symm second))
              (matterCoordinateEquiv.symm matter))
    rw [p286CoordinateEquiv.symm.map_add, p286LieBlockEmbed_add,
      diracExteriorMotherLieAction_add]
    simp only [LinearMap.add_apply, map_add]
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm (parameter • matrix)))
            (matterCoordinateEquiv.symm matter)) =
        parameter •
          matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
              (matterCoordinateEquiv.symm matter))
    rw [p286CoordinateEquiv.symm.map_smul, p286LieBlockEmbed_real_smul,
      diracExteriorMotherLieAction_real_smul]
    simp only [LinearMap.smul_apply, map_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

theorem matterP286ActionCoordinateBilinear_apply
    (matrix : P286CoordinateCarrier)
    (matter : MatterCoordinateCarrier) :
    matterP286ActionCoordinateBilinear matrix matter =
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))
          (matterCoordinateEquiv.symm matter)) := by
  rfl

def scalarCoordinatePairingReBilinear :
    ScalarCoordinateCarrier →ₗ[ℝ]
      ScalarCoordinateCarrier →ₗ[ℝ] ℝ where
  toFun first :=
    { toFun := fun second => scalarCoordinatePairingRe first second
      map_add' := by
        intro second third
        exact scalarCoordinatePairingRe_add_right second third first
      map_smul' := by
        intro parameter second
        simpa [smul_eq_mul] using
          scalarCoordinatePairingRe_real_smul_right parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact scalarCoordinatePairingRe_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    simpa [smul_eq_mul] using
      scalarCoordinatePairingRe_real_smul_left parameter first residual

theorem scalarP286Action_apply_continuous
    (matrix : BasePoint → P286CoordinateCarrier)
    (scalar : BasePoint → ScalarCoordinateCarrier)
    (matrixContinuous : Continuous matrix)
    (scalarContinuous : Continuous scalar) :
    Continuous fun point =>
      scalarP286ActionBilinear (matrix point) (scalar point) := by
  have bilinearContinuous : Continuous fun pair :
      P286CoordinateCarrier × ScalarCoordinateCarrier =>
      scalarP286ActionBilinear pair.1 pair.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((scalarP286ActionBilinear.toContinuousBilinearMap.continuous.comp
        continuous_fst).prodMk continuous_snd)
  have actual :=
    bilinearContinuous.comp (matrixContinuous.prodMk scalarContinuous)
  exact actual.congr fun point => rfl

theorem scalarP286RawAction_apply_continuous
    (matrix : BasePoint → P286CoordinateCarrier)
    (scalar : BasePoint → ScalarCoordinateCarrier)
    (matrixContinuous : Continuous matrix)
    (scalarContinuous : Continuous scalar) :
    Continuous fun point =>
      scalarMotherLieAction
        (p286LieBlockEmbed (p286CoordinateEquiv.symm (matrix point)))
        (scalar point) := by
  have actual := scalarP286Action_apply_continuous matrix scalar
    matrixContinuous scalarContinuous
  exact actual.congr fun point => rfl

theorem matterP286ActionCoordinate_apply_continuous
    (matrix : BasePoint → P286CoordinateCarrier)
    (matter : BasePoint → MatterCoordinateCarrier)
    (matrixContinuous : Continuous matrix)
    (matterContinuous : Continuous matter) :
    Continuous fun point =>
      matterP286ActionCoordinateBilinear (matrix point) (matter point) := by
  have bilinearContinuous : Continuous fun pair :
      P286CoordinateCarrier × MatterCoordinateCarrier =>
      matterP286ActionCoordinateBilinear pair.1 pair.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((matterP286ActionCoordinateBilinear.toContinuousBilinearMap.continuous.comp
        continuous_fst).prodMk continuous_snd)
  have actual :=
    bilinearContinuous.comp (matrixContinuous.prodMk matterContinuous)
  exact actual.congr fun point => rfl

theorem scalarCoordinatePairingRe_apply_continuous
    (first second : BasePoint → ScalarCoordinateCarrier)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      scalarCoordinatePairingRe (first point) (second point) := by
  have bilinearContinuous : Continuous fun pair :
      ScalarCoordinateCarrier × ScalarCoordinateCarrier =>
      scalarCoordinatePairingReBilinear pair.1 pair.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((scalarCoordinatePairingReBilinear.toContinuousBilinearMap.continuous.comp
        continuous_fst).prodMk continuous_snd)
  exact bilinearContinuous.comp (firstContinuous.prodMk secondContinuous)

@[simp] theorem scalarFrameRelativeCoordinates_zeroChart
    (source : SmoothUnifiedSource) (point : BasePoint)
    (coordinates : ScalarCoordinateCarrier) :
    scalarFrameRelativeCoordinates source 0 point coordinates = coordinates := by
  unfold scalarFrameRelativeCoordinates generatedScalarFrame
  rw [generatedTransition_normalized]
  simpa only [inv_one] using scalarCoordinateAction_one coordinates

@[simp] theorem matterFrameRelative_zeroChart
    (source : SmoothUnifiedSource) (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) :
    matterFrameRelative source 0 point matter = matter := by
  unfold matterFrameRelative generatedScalarFrame
  rw [generatedTransition_normalized]
  have representationOne :
      diracExteriorMatterGaugeRepresentation 1 =
        (1 : Module.End ℂ DiracExteriorMatterCarrier) :=
    map_one diracExteriorMatterGaugeRepresentation
  rw [inv_one, representationOne]
  rfl

@[simp] theorem matterDualFrameRelative_zeroChart
    (source : SmoothUnifiedSource) (point : BasePoint)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualFrameRelative source 0 point dual = dual := by
  apply LinearMap.ext
  intro matter
  unfold matterDualFrameRelative generatedScalarFrame
  rw [generatedTransition_normalized]
  have representationOne :
      diracExteriorMatterGaugeRepresentation 1 =
        (1 : Module.End ℂ DiracExteriorMatterCarrier) :=
    map_one diracExteriorMatterGaugeRepresentation
  rw [representationOne]
  rfl

theorem matterCoordinate_sum_single (matter : MatterCoordinateCarrier) :
    matter = ∑ index : MatterCoordinateIndex,
      matter index • EuclideanSpace.single index (1 : ℂ) := by
  apply PiLp.ext
  intro index
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  rw [Fintype.sum_eq_single index]
  · simp
  · intro candidate candidateNe
    simp [Pi.single_eq_of_ne candidateNe.symm]

theorem matterDual_coordinate_expansion
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : MatterCoordinateCarrier) :
    dual (matterCoordinateEquiv.symm matter) =
      ∑ index : MatterCoordinateIndex,
        matter index *
          dual (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) := by
  conv_lhs => rw [matterCoordinate_sum_single matter]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem holonomicLorentzianMetric_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous fun point =>
      lorentzianMetricOfCoframe (configuration.coframe point) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  unfold lorentzianMetricOfCoframe
  fun_prop

theorem holonomicLorentzianMetric_inv_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹ := by
  rw [continuous_iff_continuousAt]
  intro point
  have metricNonzero :
      Matrix.det (lorentzianMetricOfCoframe
        (configuration.coframe point)) ≠ 0 := by
    exact PointwiseLorentzianCoframeJet.metric_det_ne_zero_of_coframe
      { coframe := configuration.coframe point, derivative := 0 }
      (nondegenerate point)
  have ringInverseContinuous : ContinuousAt Ring.inverse
      (Matrix.det (lorentzianMetricOfCoframe
        (configuration.coframe point))) := by
    have actual := NormedRing.inverse_continuousAt
      (isUnit_iff_ne_zero.mpr metricNonzero).unit
    simpa only [← Ring.inverse_unit, IsUnit.unit_spec] using actual
  have matrixInvContinuous : ContinuousAt
      (fun metric : LorentzianMetric => metric⁻¹)
      (lorentzianMetricOfCoframe (configuration.coframe point)) :=
    continuousAt_matrix_inv
      (lorentzianMetricOfCoframe (configuration.coframe point))
      ringInverseContinuous
  have metricContinuous : ContinuousAt
      (fun candidate =>
        lorentzianMetricOfCoframe (configuration.coframe candidate)) point :=
    (holonomicLorentzianMetric_continuous configuration smooth).continuousAt
  exact matrixInvContinuous.tendsto.comp metricContinuous.tendsto

theorem p286GaugeVariationCoordinateDerivative_continuous
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (derivativeDirection formDirection : LorentzianIndex) :
    Continuous fun point =>
      p286GaugeVariationCoordinateDerivative variation point
        derivativeDirection formDirection := by
  have componentSmooth : ContDiff ℝ ∞ fun point =>
      variation point formDirection :=
    contDiff_pi.mp variation.smooth formDirection
  have derivativeContinuous : Continuous
      (fderiv ℝ (fun point => variation point formDirection)) :=
    componentSmooth.continuous_fderiv (by simp)
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  exact derivativeContinuous.clm_apply continuous_const

theorem holonomicP286GaugeConnectionCoordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous (holonomicP286GaugeConnectionCoordinate configuration) := by
  apply continuous_pi
  intro direction
  exact (smooth.2.2.2.2.1 direction).continuous

theorem p286GaugeConnectionLinearCurvatureVariation_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous
      (p286GaugeConnectionLinearCurvatureVariation configuration variation) := by
  have variationContinuous : Continuous
      (variation : BasePoint → P286GaugeOneForm) := variation.smooth.continuous
  have connectionContinuous :=
    holonomicP286GaugeConnectionCoordinate_continuous configuration smooth
  apply continuous_pi
  intro pair
  have firstDerivative := p286GaugeVariationCoordinateDerivative_continuous
    variation (pairFirst pair) (pairSecond pair)
  have secondDerivative := p286GaugeVariationCoordinateDerivative_continuous
    variation (pairSecond pair) (pairFirst pair)
  have variationFirst : Continuous fun point =>
      variation point (pairFirst pair) :=
    (continuous_apply (pairFirst pair)).comp variationContinuous
  have variationSecond : Continuous fun point =>
      variation point (pairSecond pair) :=
    (continuous_apply (pairSecond pair)).comp variationContinuous
  have connectionFirst : Continuous fun point =>
      holonomicP286GaugeConnectionCoordinate configuration point
        (pairFirst pair) :=
    (continuous_apply (pairFirst pair)).comp connectionContinuous
  have connectionSecond : Continuous fun point =>
      holonomicP286GaugeConnectionCoordinate configuration point
        (pairSecond pair) :=
    (continuous_apply (pairSecond pair)).comp connectionContinuous
  exact ((firstDerivative.sub secondDerivative).add
      (p286CoordinateLieBracket_apply_continuous _ _ variationFirst
        connectionSecond)).add
    (p286CoordinateLieBracket_apply_continuous _ _ connectionFirst
      variationSecond)

theorem p286GaugeConnectionQuadraticCurvatureVariation_continuous
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous (p286GaugeConnectionQuadraticCurvatureVariation variation) := by
  have variationContinuous : Continuous
      (variation : BasePoint → P286GaugeOneForm) := variation.smooth.continuous
  apply continuous_pi
  intro pair
  exact p286CoordinateLieBracket_apply_continuous _ _
    ((continuous_apply (pairFirst pair)).comp variationContinuous)
    ((continuous_apply (pairSecond pair)).comp variationContinuous)

theorem holonomicScalarGaugeConnectionVariation_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      holonomicScalarGaugeConnectionVariation configuration variation point
        direction := by
  have variationContinuous : Continuous fun point =>
      variation point direction :=
    (continuous_apply direction).comp variation.smooth.continuous
  have scalarContinuous : Continuous configuration.scalar :=
    smooth.2.2.2.2.2.2.1.continuous
  have actual := scalarP286Action_apply_continuous
    (fun point => variation point direction) configuration.scalar
      variationContinuous scalarContinuous
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  change Continuous fun point =>
    scalarP286ActionBilinear (variation point direction)
      (configuration.scalar point)
  exact actual

theorem holonomicScalarCovariantDerivative_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      holonomicScalarCovariantDerivative configuration point direction := by
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have scalarDerivativeContinuous : Continuous fun point =>
      fieldDirectionalDerivative configuration.scalar point direction := by
    unfold fieldDirectionalDerivative
    exact (scalarSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have connectionContinuous : Continuous fun point =>
      holonomicP286GaugeConnectionCoordinate configuration point direction :=
    (continuous_apply direction).comp
      (holonomicP286GaugeConnectionCoordinate_continuous configuration smooth)
  have scalarActionCoordinateContinuous := scalarP286RawAction_apply_continuous
    (fun point =>
      holonomicP286GaugeConnectionCoordinate configuration point direction)
    configuration.scalar connectionContinuous scalarSmooth.continuous
  have scalarActionContinuous : Continuous fun point =>
      scalarMotherLieAction
        (p286LieBlockEmbed (configuration.gaugeConnection point direction))
        (configuration.scalar point) :=
    scalarActionCoordinateContinuous.congr fun point => by
      simp [holonomicP286GaugeConnectionCoordinate]
  unfold holonomicScalarCovariantDerivative
  exact scalarDerivativeContinuous.add scalarActionContinuous

theorem holonomicMatterGaugeConnectionVariation_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (holonomicMatterGaugeConnectionVariation configuration variation point
          direction) := by
  have variationContinuous : Continuous fun point =>
      variation point direction :=
    (continuous_apply direction).comp variation.smooth.continuous
  have matterContinuous : Continuous fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1.continuous
  have actual := matterP286ActionCoordinate_apply_continuous
    (fun point => variation point direction)
    (fun point => matterCoordinateEquiv (configuration.matter point))
    variationContinuous matterContinuous
  unfold holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  exact actual.congr fun point => by
    change
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm
              (variation point direction)))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) =
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm
              (variation point direction)))
            (configuration.matter point))
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem holonomicP286GaugeConnectionBFFirstDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      p286GaugeBFCurvatureIncrementDensity
        (configuration.coframe point)
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (holonomicP286GaugeAuxiliaryCoordinate configuration point)
        (p286GaugeConnectionLinearCurvatureVariation configuration variation
          point) := by
  have auxiliaryContinuous :=
    holonomicP286GaugeAuxiliaryCoordinate_continuous configuration smooth
  have variationContinuous :=
    p286GaugeConnectionLinearCurvatureVariation_continuous configuration smooth
      variation
  have hodgeVariationContinuous :=
    holonomicLiftGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate _ variationContinuous
  have pairingContinuous :=
    generatedGaugeTwoFormMetricPairing_p286_apply_continuous configuration
      smooth _ _ auxiliaryContinuous hodgeVariationContinuous
  exact pairingContinuous.congr fun point => rfl

theorem holonomicP286GaugeConnectionBFSecondDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      p286GaugeBFCurvatureIncrementDensity
        (configuration.coframe point)
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (holonomicP286GaugeAuxiliaryCoordinate configuration point)
        (p286GaugeConnectionQuadraticCurvatureVariation variation point) := by
  have auxiliaryContinuous :=
    holonomicP286GaugeAuxiliaryCoordinate_continuous configuration smooth
  have variationContinuous :=
    p286GaugeConnectionQuadraticCurvatureVariation_continuous variation
  have hodgeVariationContinuous :=
    holonomicLiftGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate _ variationContinuous
  have pairingContinuous :=
    generatedGaugeTwoFormMetricPairing_p286_apply_continuous configuration
      smooth _ _ auxiliaryContinuous hodgeVariationContinuous
  exact pairingContinuous.congr fun point => rfl

theorem holonomicScalarGaugeConnectionKineticFirstDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicScalarGaugeConnectionVariation configuration variation
          point) := by
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
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹ first second :=
    (continuous_apply second).comp
      ((continuous_apply first).comp metricInverseContinuous)
  apply metricEntryContinuous.mul
  apply Continuous.add
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarGaugeConnectionVariation_continuous configuration smooth
        variation first)
      (holonomicScalarCovariantDerivative_continuous configuration smooth
        second)
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarCovariantDerivative_continuous configuration smooth
        first)
      (holonomicScalarGaugeConnectionVariation_continuous configuration smooth
        variation second)

theorem holonomicScalarGaugeConnectionKineticSecondDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      scalarGaugeConnectionKineticSecondVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicScalarGaugeConnectionVariation configuration variation
          point) := by
  have metricInverseContinuous :=
    holonomicLorentzianMetric_inv_continuous configuration smooth nondegenerate
  unfold scalarGaugeConnectionKineticSecondVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField, scalarFrameRelativeCoordinates_zeroChart]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro first _
  apply continuous_finsetSum
  intro second _
  have metricEntryContinuous : Continuous fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹ first second :=
    (continuous_apply second).comp
      ((continuous_apply first).comp metricInverseContinuous)
  exact metricEntryContinuous.mul
    (scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarGaugeConnectionVariation_continuous configuration smooth
        variation first)
      (holonomicScalarGaugeConnectionVariation_continuous configuration smooth
        variation second))

theorem diracMatrixMatterAction_add_matrix
    (first second : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (first + second) matter =
      diracMatrixMatterAction first matter +
        diracMatrixMatterAction second matter := by
  funext row
  simp [diracMatrixMatterAction, add_smul, Finset.sum_add_distrib]

theorem diracMatrixMatterAction_smul_matrix
    (parameter : ℂ) (matrix : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (parameter • matrix) matter =
      parameter • diracMatrixMatterAction matrix matter := by
  funext row
  change
    (∑ column : DiracSpinorIndex,
      (parameter * matrix row column) • matter column) =
      parameter •
        ∑ column : DiracSpinorIndex, matrix row column • matter column
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro column _
  simp [smul_smul]

def diracMatrixMatterCoordinateBilinear :
    DiracMatrix →ₗ[ℂ]
      MatterCoordinateCarrier →ₗ[ℂ] MatterCoordinateCarrier where
  toFun matrix :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (diracMatrixMatterAction matrix
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        simp only [map_add]
      map_smul' := by
        intro parameter matter
        simp only [map_smul, RingHom.id_apply] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracMatrixMatterAction (first + second)
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (diracMatrixMatterAction first
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (diracMatrixMatterAction second
              (matterCoordinateEquiv.symm matter))
    rw [diracMatrixMatterAction_add_matrix, map_add]
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracMatrixMatterAction (parameter • matrix)
            (matterCoordinateEquiv.symm matter)) =
        parameter •
          matterCoordinateEquiv
            (diracMatrixMatterAction matrix
              (matterCoordinateEquiv.symm matter))
    rw [diracMatrixMatterAction_smul_matrix, map_smul]

theorem diracMatrixMatterCoordinate_apply_continuous
    (matrix : BasePoint → DiracMatrix)
    (matter : BasePoint → MatterCoordinateCarrier)
    (matrixContinuous : Continuous matrix)
    (matterContinuous : Continuous matter) :
    Continuous fun point =>
      diracMatrixMatterCoordinateBilinear (matrix point) (matter point) := by
  have bilinearContinuous : Continuous fun pair :
      DiracMatrix × MatterCoordinateCarrier =>
      diracMatrixMatterCoordinateBilinear pair.1 pair.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((diracMatrixMatterCoordinateBilinear.toContinuousBilinearMap.continuous.comp
        continuous_fst).prodMk continuous_snd)
  have actual :=
    bilinearContinuous.comp (matrixContinuous.prodMk matterContinuous)
  exact actual.congr fun point => rfl

theorem diracMatrixMatterCoordinate_raw_apply_continuous
    (matrix : BasePoint → DiracMatrix)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (matrixContinuous : Continuous matrix)
    (matterCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (matter point)) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction (matrix point) (matter point)) := by
  have actual := diracMatrixMatterCoordinate_apply_continuous matrix
    (fun point => matterCoordinateEquiv (matter point)) matrixContinuous
      matterCoordinateContinuous
  exact actual.congr fun point => by
    change
      matterCoordinateEquiv
          (diracMatrixMatterAction (matrix point)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (matter point)))) =
        matterCoordinateEquiv
          (diracMatrixMatterAction (matrix point) (matter point))
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem holonomicInverseCoframeDiracGamma_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      inverseCoframeDiracGamma
        { coframe := configuration.coframe point, derivative := 0 } direction := by
  have inverseCoframeContinuous :=
    holonomicCoframe_inv_continuous configuration smooth nondegenerate
  unfold inverseCoframeDiracGamma
  apply continuous_finsetSum
  intro internal _
  have coefficientContinuous : Continuous fun point =>
      (configuration.coframe point)⁻¹ direction internal :=
    (continuous_apply internal).comp
      ((continuous_apply direction).comp inverseCoframeContinuous)
  have complexCoefficientContinuous : Continuous fun point =>
      ((configuration.coframe point)⁻¹ direction internal : ℂ) :=
    Complex.ofRealCLM.continuous.comp coefficientContinuous
  exact complexCoefficientContinuous.smul continuous_const

theorem holonomicMatterGaugeKineticSummand_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            direction)
          (holonomicMatterGaugeConnectionVariation configuration variation point
            direction)) :=
  diracMatrixMatterCoordinate_raw_apply_continuous _ _
    (holonomicInverseCoframeDiracGamma_continuous configuration smooth
      nondegenerate direction)
    (holonomicMatterGaugeConnectionVariation_coordinate_continuous configuration
      smooth variation direction)

theorem holonomicMatterGaugeKineticSum_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterGaugeConnectionVariation configuration variation
            point)) := by
  have sumContinuous : Continuous fun point =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              direction)
            (holonomicMatterGaugeConnectionVariation configuration variation
              point direction)) := by
    apply continuous_finsetSum
    intro direction _
    exact holonomicMatterGaugeKineticSummand_coordinate_continuous configuration
      smooth nondegenerate variation direction
  exact sumContinuous.congr fun point => by
    unfold matterGaugeKineticSum matterDerivativeFrameRelative
    simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]

theorem holonomicMatterGaugeConnectionVariationVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeConnectionVariationVector source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterGaugeConnectionVariation configuration variation
            point)) := by
  have kineticContinuous :=
    holonomicMatterGaugeKineticSum_coordinate_continuous source configuration
      smooth nondegenerate variation
  have coordinateContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterGaugeConnectionVariation configuration variation
            point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticContinuous).congr fun point => rfl
  unfold matterGaugeConnectionVariationVector
  exact coordinateContinuous.congr fun point => by
    rw [map_smul]

theorem holonomicMatterGaugeConnectionFirstDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      matterGaugeConnectionFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicMatterGaugeConnectionVariation configuration variation
          point) := by
  let vector := fun point =>
    matterGaugeConnectionVariationVector source 0 point
      (toContinuumPointField configuration point)
      (holonomicMatterGaugeConnectionVariation configuration variation point)
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    holonomicMatterGaugeConnectionVariationVector_coordinate_continuous source
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
  have realPairingContinuous :=
    Complex.continuous_re.comp pairingContinuous
  unfold matterGaugeConnectionFirstVariationDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart]
  exact realPairingContinuous.congr fun point => by
    simp only [Function.comp_apply]
    rw [← matterDual_coordinate_expansion
      (configuration.conjugateMatter point)
      (matterCoordinateEquiv (vector point))]
    simp only [matterCoordinateEquiv.symm_apply_apply]
    rfl

theorem holonomicP286GaugeConnectionFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous
      (holonomicP286GaugeConnectionFirstVariationDensity source 0
        configuration variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      abs (Matrix.det (configuration.coframe point)) :=
    coframeContinuous.matrix_det.abs
  have bfContinuous :=
    holonomicP286GaugeConnectionBFFirstDensity_continuous configuration smooth
      nondegenerate variation
  have scalarContinuous :=
    holonomicScalarGaugeConnectionKineticFirstDensity_continuous source
      configuration smooth nondegenerate variation
  have matterContinuous :=
    holonomicMatterGaugeConnectionFirstDensity_continuous source configuration
      smooth nondegenerate variation
  unfold holonomicP286GaugeConnectionFirstVariationDensity
    p286GaugeConnectionFirstVariationDensity generatedVolumeDensity
    p286AuxiliaryCoordinate
  have actual := volumeContinuous.mul
    ((bfContinuous.add scalarContinuous).add matterContinuous)
  exact actual.congr fun point => rfl

theorem holonomicP286GaugeConnectionSecondVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous
      (holonomicP286GaugeConnectionSecondVariationDensity source 0
        configuration variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      abs (Matrix.det (configuration.coframe point)) :=
    coframeContinuous.matrix_det.abs
  have bfContinuous :=
    holonomicP286GaugeConnectionBFSecondDensity_continuous configuration smooth
      nondegenerate variation
  have scalarContinuous :=
    holonomicScalarGaugeConnectionKineticSecondDensity_continuous source
      configuration smooth nondegenerate variation
  unfold holonomicP286GaugeConnectionSecondVariationDensity
    p286GaugeConnectionSecondVariationDensity generatedVolumeDensity
    p286AuxiliaryCoordinate
  have actual := volumeContinuous.mul (bfContinuous.add scalarContinuous)
  exact actual.congr fun point => rfl

theorem p286GaugeVariationCoordinateDerivative_eq_full_fderiv
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative variation point derivativeDirection
        formDirection =
      (fderiv ℝ (variation : BasePoint → P286GaugeOneForm) point
        (coordinateDirection derivativeDirection)) formDirection := by
  have differentiable : DifferentiableAt ℝ
      (variation : BasePoint → P286GaugeOneForm) point :=
    (variation.smooth.differentiable (by simp)).differentiableAt
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  rw [fderiv_apply differentiable formDirection]
  rfl

theorem compactP286GaugeConnectionVariation_eventually_jet_zero
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    ∀ᶠ point in Filter.coclosedCompact BasePoint,
      variation point = 0 ∧
        ∀ derivativeDirection formDirection : LorentzianIndex,
          p286GaugeVariationCoordinateDerivative variation point
            derivativeDirection formDirection = 0 := by
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  have derivativeEventually : ∀ direction : LorentzianIndex,
      ∀ᶠ point in Filter.coclosedCompact BasePoint,
        fderiv ℝ (variation : BasePoint → P286GaugeOneForm) point
          (coordinateDirection direction) = 0 := by
    intro direction
    have actual := compactVariation_directionalDerivative_compact variation
      direction
    rw [hasCompactSupport_iff_eventuallyEq] at actual
    exact actual
  have everyDerivativeEventually :=
    Filter.eventually_all.2 derivativeEventually
  filter_upwards [variationEventually, everyDerivativeEventually] with
    point variationZero derivativeZero
  refine ⟨variationZero, ?_⟩
  intro derivativeDirection formDirection
  rw [p286GaugeVariationCoordinateDerivative_eq_full_fderiv,
    derivativeZero derivativeDirection]
  rfl

@[simp] theorem p286CoordinateLieBracket_zero_left
    (residual : P286CoordinateCarrier) :
    p286CoordinateLieBracket 0 residual = 0 := by
  change p286CoordinateLieBracketBilinear 0 residual = 0
  simp

@[simp] theorem p286CoordinateLieBracket_zero_right
    (residual : P286CoordinateCarrier) :
    p286CoordinateLieBracket residual 0 = 0 := by
  change p286CoordinateLieBracketBilinear residual 0 = 0
  exact (p286CoordinateLieBracketBilinear residual).map_zero

@[simp] theorem scalarMotherLieAction_zero_matrix
    (scalar : ScalarCoordinateCarrier) :
    scalarMotherLieAction 0 scalar = 0 := by
  unfold scalarMotherLieAction
  rw [exteriorMotherLieAction_zero]
  simp

@[simp] theorem diracExteriorMotherLieAction_zero_matrix
    (matter : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction 0 matter = 0 := by
  unfold diracExteriorMotherLieAction exteriorSpinorMotherLieAction
    internalMatterLinearAction
  funext spinIndex
  simp [exteriorMotherLieAction_zero]

theorem p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ derivativeDirection formDirection : LorentzianIndex,
      p286GaugeVariationCoordinateDerivative variation point
        derivativeDirection formDirection = 0) :
    p286GaugeConnectionLinearCurvatureVariation configuration variation point =
      0 := by
  funext pair
  simp [p286GaugeConnectionLinearCurvatureVariation, variationZero,
    derivativeZero]

theorem p286GaugeConnectionQuadraticCurvatureVariation_eq_zero
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    p286GaugeConnectionQuadraticCurvatureVariation variation point = 0 := by
  funext pair
  simp [p286GaugeConnectionQuadraticCurvatureVariation, variationZero]

theorem holonomicScalarGaugeConnectionVariation_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    holonomicScalarGaugeConnectionVariation configuration variation point =
      0 := by
  funext direction
  simp [holonomicScalarGaugeConnectionVariation,
    p286GaugeConnectionMotherVariation, variationZero]

theorem holonomicMatterGaugeConnectionVariation_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    holonomicMatterGaugeConnectionVariation configuration variation point =
      0 := by
  funext direction
  simp [holonomicMatterGaugeConnectionVariation,
    p286GaugeConnectionMotherVariation, variationZero]

@[simp] theorem p286GaugeBFCurvatureIncrementDensity_zero
    (coframe : LorentzianCoframe)
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (auxiliary : P286GaugeTwoForm) :
    p286GaugeBFCurvatureIncrementDensity coframe spacetimeHodge auxiliary 0 =
      0 := by
  simp [p286GaugeBFCurvatureIncrementDensity,
    generatedGaugeTwoFormMetricPairing]

@[simp] theorem scalarGaugeConnectionKineticFirstVariationDensity_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    scalarGaugeConnectionKineticFirstVariationDensity source chart point field
      0 = 0 := by
  simp [scalarGaugeConnectionKineticFirstVariationDensity,
    scalarCoordinatePairingRe]

@[simp] theorem scalarGaugeConnectionKineticSecondVariationDensity_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    scalarGaugeConnectionKineticSecondVariationDensity source chart point field
      0 = 0 := by
  simp [scalarGaugeConnectionKineticSecondVariationDensity,
    scalarCoordinatePairingRe]

@[simp] theorem matterGaugeConnectionFirstVariationDensity_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    matterGaugeConnectionFirstVariationDensity source chart point field 0 =
      0 := by
  simp [matterGaugeConnectionFirstVariationDensity,
    matterGaugeConnectionVariationVector, matterGaugeKineticSum,
    matterDerivativeFrameRelative, matterFrameRelative]

theorem holonomicP286GaugeConnectionFirstVariationDensity_eq_zero_of_jet_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ derivativeDirection formDirection : LorentzianIndex,
      p286GaugeVariationCoordinateDerivative variation point
        derivativeDirection formDirection = 0) :
    holonomicP286GaugeConnectionFirstVariationDensity source chart
      configuration variation point = 0 := by
  unfold holonomicP286GaugeConnectionFirstVariationDensity
  rw [show p286GaugeConnectionLinearCurvatureVariation configuration variation
      point = 0 from
    p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
      configuration variation point variationZero derivativeZero]
  rw [show holonomicScalarGaugeConnectionVariation configuration variation
      point = 0 from
    holonomicScalarGaugeConnectionVariation_eq_zero configuration variation
      point variationZero]
  rw [show holonomicMatterGaugeConnectionVariation configuration variation
      point = 0 from
    holonomicMatterGaugeConnectionVariation_eq_zero configuration variation
      point variationZero]
  simp [p286GaugeConnectionFirstVariationDensity]

theorem holonomicP286GaugeConnectionSecondVariationDensity_eq_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    holonomicP286GaugeConnectionSecondVariationDensity source chart
      configuration variation point = 0 := by
  unfold holonomicP286GaugeConnectionSecondVariationDensity
  rw [show p286GaugeConnectionQuadraticCurvatureVariation variation point = 0
    from p286GaugeConnectionQuadraticCurvatureVariation_eq_zero variation point
      variationZero]
  rw [show holonomicScalarGaugeConnectionVariation configuration variation
      point = 0 from
    holonomicScalarGaugeConnectionVariation_eq_zero configuration variation
      point variationZero]
  simp [p286GaugeConnectionSecondVariationDensity]

theorem holonomicP286GaugeConnectionFirstVariationDensity_compact
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasCompactSupport
      (holonomicP286GaugeConnectionFirstVariationDensity source chart
        configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactP286GaugeConnectionVariation_eventually_jet_zero variation] with
    point jetZero
  exact holonomicP286GaugeConnectionFirstVariationDensity_eq_zero_of_jet_zero
    source chart configuration variation point jetZero.1 jetZero.2

theorem holonomicP286GaugeConnectionSecondVariationDensity_compact
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasCompactSupport
      (holonomicP286GaugeConnectionSecondVariationDensity source chart
        configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  filter_upwards [variationEventually] with point variationZero
  exact holonomicP286GaugeConnectionSecondVariationDensity_eq_zero source chart
    configuration variation point variationZero

theorem holonomicP286GaugeConnectionFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Integrable
      (holonomicP286GaugeConnectionFirstVariationDensity source 0
        configuration variation) :=
  (holonomicP286GaugeConnectionFirstVariationDensity_continuous source
    configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicP286GaugeConnectionFirstVariationDensity_compact source 0
        configuration variation)

theorem holonomicP286GaugeConnectionSecondVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Integrable
      (holonomicP286GaugeConnectionSecondVariationDensity source 0
        configuration variation) :=
  (holonomicP286GaugeConnectionSecondVariationDensity_continuous source
    configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicP286GaugeConnectionSecondVariationDensity_compact source 0
        configuration variation)

end

end SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariationDensity
