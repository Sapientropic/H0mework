import H0mework.Physics.Holonomic.CoframeRegularity
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity
import H0mework.Physics.GaugeStanding.ConjugateRegularity
import H0mework.Physics.GaugeStanding.FullLocalDensityPolynomial
import H0mework.Physics.GaugeStanding.VariationRegularity
import H0mework.Physics.Exterior.ScalarVariation

/-!
# S9-C: analytic control of the linked full local coefficients

The exact linked-active quartic has four pointwise coefficients.  This module
derives their continuity, compact support, and integrability from the one
actual compact-smooth P286 parameter.

The first coefficient is controlled directly by its faithful frozen-source
torque readout.  For the higher coefficients, the proof keeps the path first:
the full local-density increment is continuous and compactly supported at
each fixed parameter, and four fixed evaluations of the already proved exact
quartic recover the remaining coefficients.  Thus no coefficient is supplied
as an analytic receipt and no dominator, integrability premise, Ward zero,
stationarity law, or field equation is accepted.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveFullLocalDensityRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286FrozenSourceScalarTorque
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveConjugateRegularity
open StageNineP286LinkedActiveFullLocalDensityPolynomial
open StageNineP286LinkedActiveLocalWardCoefficient
open StageNineP286LinkedActiveMatterDensityCancellation
open StageNineP286LinkedActivePointFieldNormalForm
open StageNineP286LinkedActivePointJetExpansion
open StageNineP286LinkedActiveScalarKineticCancellation
open StageNineP286LinkedActiveVariation
open StageNineP286LinkedActiveVariationRegularity
open StageNineScalarVariation
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

open MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286InfinitesimalGaugeTransformation.p286CoordinateIndexFintype

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Smoothness and pointwise continuity of the one actual path -/

private theorem withCoframe_self_local
    (field : StageNineContinuumPointField) :
    withCoframe field field.coframe = field := by
  cases field
  rfl

/-- The linked path remains smooth because all five charged directions are
generated as compact-smooth variations from the same parameter. -/
private theorem p286LinkedActivePrimitivePath_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ) :
    (p286LinkedActivePrimitivePath configuration gaugeParameter
      parameter).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  let smooth' : configuration.Smooth :=
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  let tangent :=
    representationDerivedP286CoupledGaugeTangentSection configuration
      gaugeParameter
  have connectionTangentSmooth : ContDiff ℝ ∞ fun point =>
      (tangent point).connection := by
    change ContDiff ℝ ∞
      (p286InfinitesimalGaugeConnectionVariation configuration smooth'
        gaugeParameter).toFun
    exact
      (p286InfinitesimalGaugeConnectionVariation configuration smooth'
        gaugeParameter).smooth
  have auxiliaryTangentSmooth : ContDiff ℝ ∞ fun point =>
      (tangent point).auxiliary := by
    change ContDiff ℝ ∞
      (p286LinkedActiveAuxiliaryVariation configuration smooth'
        gaugeParameter).toFun
    exact
      (p286LinkedActiveAuxiliaryVariation configuration smooth'
        gaugeParameter).smooth
  have scalarTangentSmooth : ContDiff ℝ ∞ fun point =>
      (tangent point).scalar := by
    change ContDiff ℝ ∞
      (p286LinkedActiveScalarVariation configuration smooth'
        gaugeParameter).toFun
    exact
      (p286LinkedActiveScalarVariation configuration smooth'
        gaugeParameter).smooth
  have matterTangentSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (tangent point).matter := by
    change ContDiff ℝ ∞
      (p286LinkedActiveMatterVariation configuration smooth'
        gaugeParameter).toFun
    exact
      (p286LinkedActiveMatterVariation configuration smooth'
        gaugeParameter).smooth
  have conjugateTangentSmooth : ContDiff ℝ ∞ fun point =>
      matterDualCoordinates (tangent point).conjugateMatter := by
    rw [show
      (fun point =>
        matterDualCoordinates (tangent point).conjugateMatter) =
        (p286LinkedActiveConjugateMatterVariation configuration smooth'
          gaugeParameter).toFun by
      funext point
      exact
        (p286LinkedActiveConjugateMatterVariation_apply configuration smooth'
          gaugeParameter point).symm]
    exact
      (p286LinkedActiveConjugateMatterVariation configuration smooth'
        gaugeParameter).smooth
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [p286LinkedActivePrimitivePath_coframe] using coframeSmooth
  · simpa only [p286LinkedActivePrimitivePath_gravityConnection] using
      gravityConnectionSmooth
  · simpa only [p286LinkedActivePrimitivePath_gravityAuxiliary] using
      gravityAuxiliarySmooth
  · simpa only [p286LinkedActivePrimitivePath_gravitySimplicityMultiplier] using
      gravityMultiplierSmooth
  · intro direction
    have directionSmooth : ContDiff ℝ ∞ fun point =>
        (tangent point).connection direction :=
      contDiff_pi.mp connectionTangentSmooth direction
    have scaledSmooth : ContDiff ℝ ∞ fun point =>
        parameter • (tangent point).connection direction :=
      (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
        contDiff_const).smul directionSmooth
    rw [show
        (fun point =>
          p286CoordinateEquiv
            ((p286LinkedActivePrimitivePath configuration gaugeParameter
              parameter).gaugeConnection point direction)) =
          fun point =>
            p286CoordinateEquiv
                (configuration.gaugeConnection point direction) +
              parameter • (tangent point).connection direction by
      funext point
      exact congrFun
        (p286LinkedActivePrimitivePath_connectionCoordinate configuration
          gaugeParameter parameter point)
        direction]
    exact (gaugeConnectionSmooth direction).add scaledSmooth
  · intro pair
    have pairSmooth : ContDiff ℝ ∞ fun point =>
        (tangent point).auxiliary pair :=
      contDiff_pi.mp auxiliaryTangentSmooth pair
    have scaledSmooth : ContDiff ℝ ∞ fun point =>
        parameter • (tangent point).auxiliary pair :=
      (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
        contDiff_const).smul pairSmooth
    rw [show
        (fun point =>
          p286CoordinateEquiv
            ((p286LinkedActivePrimitivePath configuration gaugeParameter
              parameter).gaugeAuxiliary point pair)) =
          fun point =>
            p286CoordinateEquiv (configuration.gaugeAuxiliary point pair) +
              parameter • (tangent point).auxiliary pair by
      funext point
      exact congrFun
        (p286LinkedActivePrimitivePath_auxiliaryCoordinate configuration
          gaugeParameter parameter point)
        pair]
    exact (gaugeAuxiliarySmooth pair).add scaledSmooth
  · have scaledSmooth : ContDiff ℝ ∞ fun point =>
        parameter • (tangent point).scalar :=
      (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
        contDiff_const).smul scalarTangentSmooth
    rw [show
        (p286LinkedActivePrimitivePath configuration gaugeParameter
          parameter).scalar =
          fun point =>
            configuration.scalar point + parameter • (tangent point).scalar by
      funext point
      exact p286LinkedActivePrimitivePath_scalarCoordinate configuration
        gaugeParameter parameter point]
    exact scalarSmooth.add scaledSmooth
  · have scaledSmooth : ContDiff ℝ ∞ fun point =>
        parameter • matterCoordinateEquiv (tangent point).matter :=
      (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
        contDiff_const).smul matterTangentSmooth
    rw [show
        (fun point =>
          matterCoordinateEquiv
            ((p286LinkedActivePrimitivePath configuration gaugeParameter
              parameter).matter point)) =
          fun point =>
            matterCoordinateEquiv (configuration.matter point) +
              parameter • matterCoordinateEquiv (tangent point).matter by
      funext point
      exact p286LinkedActivePrimitivePath_matterCoordinate configuration
        gaugeParameter parameter point]
    exact matterSmooth.add scaledSmooth
  · intro index
    have coordinateSmooth : ContDiff ℝ ∞ fun point =>
        matterDualCoordinates (tangent point).conjugateMatter index :=
      by
        change ContDiff ℝ ∞
          (((EuclideanSpace.proj index).restrictScalars ℝ) ∘
            fun point =>
              matterDualCoordinates (tangent point).conjugateMatter)
        exact
          ((EuclideanSpace.proj index).restrictScalars ℝ).contDiff.comp
            conjugateTangentSmooth
    have scaledSmooth : ContDiff ℝ ∞ fun point =>
        parameter •
          matterDualCoordinates (tangent point).conjugateMatter index :=
      (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
        contDiff_const).smul coordinateSmooth
    rw [show
        (fun point =>
          (p286LinkedActivePrimitivePath configuration gaugeParameter
              parameter).conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index 1))) =
          fun point =>
            configuration.conjugateMatter point
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index 1)) +
              parameter •
                matterDualCoordinates (tangent point).conjugateMatter index by
      funext point
      rw [p286LinkedActivePrimitivePath_conjugateMatter]
      rfl]
    exact (conjugateMatterSmooth index).add scaledSmooth

/-- The complete root local density of any smooth nondegenerate holonomic
configuration is continuous in the base point.  This is only a private
analytic bridge to the already generated coframe regularity theorem. -/
private theorem holonomicUnifiedLocalDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField configuration point) := by
  rw [continuous_iff_continuousAt]
  intro point
  have jointContinuous :=
    (holonomicCoframeLocalDensityFamily_joint_contDiffAt source configuration
      smooth point (configuration.coframe point)
      (nondegenerate point)).continuousAt
  have sectionContinuous : ContinuousAt
      (fun candidate : BasePoint =>
        (candidate, configuration.coframe candidate)) point :=
    continuousAt_id.prodMk
      (holonomicCoframe_contDiff configuration smooth).continuous.continuousAt
  have composed : ContinuousAt
      (fun candidate =>
        Function.uncurry
          (holonomicCoframeLocalDensityFamily source configuration)
          (candidate, configuration.coframe candidate))
      point :=
    jointContinuous.comp'
      (f := fun candidate : BasePoint =>
        (candidate, configuration.coframe candidate))
      sectionContinuous
  simpa [Function.uncurry, holonomicCoframeLocalDensityFamily,
    coframeLocalDensity, toContinuumPointField, withCoframe] using composed

/-! ## The compact full-density increment -/

private def p286LinkedActiveFullLocalDensityIncrement
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ)
    (point : BasePoint) : ℝ :=
  generatedUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) 0 point
      (toContinuumPointField
        (p286LinkedActivePrimitivePath configuration gaugeParameter parameter)
        point) -
    generatedUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) 0 point
      (toContinuumPointField configuration point)

private theorem p286LinkedActiveFullLocalDensityIncrement_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ) :
    Continuous
      (p286LinkedActiveFullLocalDensityIncrement source configuration
        gaugeParameter parameter) := by
  have pathSmooth :=
    p286LinkedActivePrimitivePath_smooth configuration smooth gaugeParameter
      parameter
  have pathNondegenerate :=
    p286LinkedActivePrimitivePath_nondegenerate configuration nondegenerate
      gaugeParameter parameter
  exact
    (holonomicUnifiedLocalDensity_continuous source
      (p286LinkedActivePrimitivePath configuration gaugeParameter parameter)
      pathSmooth pathNondegenerate).sub
      (holonomicUnifiedLocalDensity_continuous source configuration smooth
        nondegenerate)

private theorem p286LinkedActivePointFieldNormalForm_eq_of_parameter_zero
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ)
    (point : BasePoint)
    (parameterZero : gaugeParameter point = 0)
    (connectionJetZero :
      (p286InfinitesimalGaugeConnectionVariation configuration smooth
          gaugeParameter) point = 0 ∧
        ∀ derivativeDirection formDirection : LorentzianIndex,
          p286GaugeVariationCoordinateDerivative
              (p286InfinitesimalGaugeConnectionVariation configuration smooth
                gaugeParameter)
              point derivativeDirection formDirection =
            0) :
    p286LinkedActivePointFieldNormalForm configuration gaugeParameter parameter
        point =
      toContinuumPointField configuration point := by
  have tangentConnectionZero :
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).connection = 0 := by
    simpa [p286InfinitesimalGaugeConnectionVariation] using
      connectionJetZero.1
  have tangentAuxiliaryZero :
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).auxiliary = 0 := by
    funext pair
    simp [representationDerivedP286CoupledGaugeTangentAt, parameterZero]
  have tangentScalarZero :
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).scalar = 0 := by
    simp [representationDerivedP286CoupledGaugeTangentAt,
      p286GaugeParameterMotherAt, parameterZero]
  have tangentMatterZero :
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).matter = 0 := by
    simp [representationDerivedP286CoupledGaugeTangentAt,
      p286GaugeParameterMotherAt, parameterZero]
  have tangentConjugateZero :
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).conjugateMatter = 0 := by
    apply LinearMap.ext
    intro matter
    simp [representationDerivedP286CoupledGaugeTangentAt,
      p286GaugeParameterMotherAt, parameterZero]
  have curvatureLinearZero :
      linkedActiveP286CurvatureLinearResponse configuration gaugeParameter
          point =
        0 := by
    change
      p286GaugeConnectionLinearCurvatureVariation configuration
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter)
          point =
        0
    exact
      p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
        configuration
        (p286InfinitesimalGaugeConnectionVariation configuration smooth
          gaugeParameter)
        point connectionJetZero.1 connectionJetZero.2
  have curvatureQuadraticZero :
      linkedActiveP286CurvatureQuadraticResponse configuration gaugeParameter
          point =
        0 := by
    change
      p286GaugeConnectionQuadraticCurvatureVariation
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter)
          point =
        0
    exact
      p286GaugeConnectionQuadraticCurvatureVariation_eq_zero
        (p286InfinitesimalGaugeConnectionVariation configuration smooth
          gaugeParameter)
        point connectionJetZero.1
  have scalarLinearZero :
      linkedActiveScalarCovariantJetResponse configuration gaugeParameter
          point =
        0 := by
    funext direction
    rw [linkedActiveScalarCovariantJetResponse_eq_action configuration smooth]
    simp [p286GaugeParameterMotherAt, parameterZero]
  have scalarQuadraticZero :
      linkedActiveScalarCovariantJetQuadraticResponse configuration
          gaugeParameter point =
        0 := by
    funext direction
    change scalarP286ActionBilinear
      ((representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).connection direction)
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).scalar = 0
    rw [show
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).connection direction = 0 by
      rw [tangentConnectionZero]
      rfl]
    simp
  have matterLinearZero :
      linkedActiveMatterCovariantJetResponse configuration gaugeParameter
          point =
        0 := by
    funext direction
    rw [linkedActiveMatterCovariantJetResponse_eq_action configuration smooth]
    simp [p286GaugeParameterMotherAt, parameterZero]
  have matterQuadraticZero :
      linkedActiveMatterCovariantJetQuadraticResponse configuration
          gaugeParameter point =
        0 := by
    funext direction
    change diracExteriorMotherLieAction
      (p286LieBlockEmbed
        (p286CoordinateEquiv.symm
          ((representationDerivedP286CoupledGaugeTangentAt configuration
            gaugeParameter point).connection direction)))
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).matter = 0
    rw [show
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).connection direction = 0 by
      rw [tangentConnectionZero]
      rfl]
    simp
  apply StageNineContinuumPointField.ext
  all_goals
    simp [p286LinkedActivePointFieldNormalForm, toContinuumPointField,
      holonomicP286GaugeCurvatureCoordinate,
      holonomicP286GaugeAuxiliaryCoordinate,
      tangentAuxiliaryZero, tangentScalarZero, tangentMatterZero,
      tangentConjugateZero, curvatureLinearZero, curvatureQuadraticZero,
      scalarLinearZero, scalarQuadraticZero, matterLinearZero,
      matterQuadraticZero]
  all_goals module

private theorem p286LinkedActiveFullLocalDensityIncrement_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ) :
    HasCompactSupport
      (p286LinkedActiveFullLocalDensityIncrement source configuration
        gaugeParameter parameter) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have parameterEventually := gaugeParameter.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at parameterEventually
  filter_upwards
    [parameterEventually,
      compactP286GaugeConnectionVariation_eventually_jet_zero
        (p286InfinitesimalGaugeConnectionVariation configuration smooth
          gaugeParameter)] with
    point parameterZero connectionJetZero
  have parameterZero' : gaugeParameter point = 0 := by
    simpa using parameterZero
  unfold p286LinkedActiveFullLocalDensityIncrement
  rw [toContinuumPointField_p286LinkedActivePrimitivePath configuration smooth]
  rw [p286LinkedActivePointFieldNormalForm_eq_of_parameter_zero configuration
    smooth gaugeParameter parameter point parameterZero' connectionJetZero]
  simp

/-! ## Four-point recovery of the higher exact coefficients -/

private theorem p286LinkedActiveFullLocalDensityIncrement_eq_polynomial
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ)
    (point : BasePoint) :
    p286LinkedActiveFullLocalDensityIncrement source configuration
        gaugeParameter parameter point =
      parameter *
          p286LinkedActiveFullLocalFirstCoefficient source configuration
            gaugeParameter point +
        parameter ^ 2 *
          p286LinkedActiveFullLocalSecondCoefficient source configuration
            gaugeParameter point +
        parameter ^ 3 *
          p286LinkedActiveFullLocalThirdCoefficient source configuration
            gaugeParameter point +
        parameter ^ 4 *
          p286LinkedActiveFullLocalFourthCoefficient source configuration
            gaugeParameter point := by
  unfold p286LinkedActiveFullLocalDensityIncrement
  rw [generatedUnifiedLocalDensity_p286LinkedActivePrimitivePath_quartic
    source configuration smooth gaugeParameter parameter point]
  ring

private theorem p286LinkedActiveFullLocalSecondCoefficient_eq_increment
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    p286LinkedActiveFullLocalSecondCoefficient source configuration
        gaugeParameter point =
      (1 / 24 : ℝ) *
        (16 *
            p286LinkedActiveFullLocalDensityIncrement source configuration
              gaugeParameter 1 point +
          16 *
            p286LinkedActiveFullLocalDensityIncrement source configuration
              gaugeParameter (-1) point -
          p286LinkedActiveFullLocalDensityIncrement source configuration
            gaugeParameter 2 point -
          p286LinkedActiveFullLocalDensityIncrement source configuration
            gaugeParameter (-2) point) := by
  rw [p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter 1 point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter (-1) point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter 2 point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter (-2) point]
  ring

private theorem p286LinkedActiveFullLocalThirdCoefficient_eq_increment
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    p286LinkedActiveFullLocalThirdCoefficient source configuration
        gaugeParameter point =
      (1 / 12 : ℝ) *
        (p286LinkedActiveFullLocalDensityIncrement source configuration
              gaugeParameter 2 point -
          p286LinkedActiveFullLocalDensityIncrement source configuration
            gaugeParameter (-2) point -
          2 *
            p286LinkedActiveFullLocalDensityIncrement source configuration
              gaugeParameter 1 point +
          2 *
            p286LinkedActiveFullLocalDensityIncrement source configuration
              gaugeParameter (-1) point) := by
  rw [p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter 1 point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter (-1) point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter 2 point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter (-2) point]
  ring

private theorem p286LinkedActiveFullLocalFourthCoefficient_eq_increment
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    p286LinkedActiveFullLocalFourthCoefficient source configuration
        gaugeParameter point =
      (1 / 24 : ℝ) *
        (p286LinkedActiveFullLocalDensityIncrement source configuration
              gaugeParameter 2 point +
          p286LinkedActiveFullLocalDensityIncrement source configuration
            gaugeParameter (-2) point -
          4 *
            p286LinkedActiveFullLocalDensityIncrement source configuration
              gaugeParameter 1 point -
          4 *
            p286LinkedActiveFullLocalDensityIncrement source configuration
              gaugeParameter (-1) point) := by
  rw [p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter 1 point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter (-1) point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter 2 point,
    p286LinkedActiveFullLocalDensityIncrement_eq_polynomial source
      configuration smooth gaugeParameter (-2) point]
  ring

/-! ## Public continuity results -/

/-- Continuity of the faithful first coefficient needs no nondegeneracy:
after the active cancellations it is exactly the scalar-potential torque. -/
theorem p286LinkedActiveFullLocalFirstCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    Continuous fun point =>
      p286LinkedActiveFullLocalFirstCoefficient source configuration
        gaugeParameter point := by
  let scalarVariation :=
    p286LinkedActiveScalarVariation configuration smooth gaugeParameter
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    (holonomicCoframe_contDiff configuration smooth).continuous.matrix_det.abs
  have potentialContinuous :=
    holonomicScalarPotentialFirstVariation_continuous source configuration
      smooth scalarVariation
  have torqueContinuous : Continuous fun point =>
      -(generatedVolumeDensity (toContinuumPointField configuration point) *
        scalarPotentialFirstVariation source
          (toContinuumPointField configuration point)
          (scalarVariation point)) :=
    (volumeContinuous.mul potentialContinuous).neg
  rw [show
      (fun point =>
        p286LinkedActiveFullLocalFirstCoefficient source configuration
          gaugeParameter point) =
        fun point =>
          p286FrozenSourceScalarTorqueDensity source configuration
            gaugeParameter point by
    funext point
    rw [p286LinkedActiveFullLocalFirstCoefficient_eq_existing,
      linkedActiveFullLocalFirstVariationDensity_eq_torque source
        configuration smooth]]
  simpa [p286FrozenSourceScalarTorqueDensity, scalarVariation] using
    torqueContinuous

/-- Continuity of the quadratic coefficient.  Nondegeneracy is the actual
configuration condition needed by the coframe inverse/Hodge terms. -/
theorem p286LinkedActiveFullLocalSecondCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    Continuous fun point =>
      p286LinkedActiveFullLocalSecondCoefficient source configuration
        gaugeParameter point := by
  have one :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter 1
  have negOne :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter (-1)
  have two :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter 2
  have negTwo :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter (-2)
  rw [show
      (fun point =>
        p286LinkedActiveFullLocalSecondCoefficient source configuration
          gaugeParameter point) =
        fun point =>
          (1 / 24 : ℝ) *
            (16 *
                p286LinkedActiveFullLocalDensityIncrement source configuration
                  gaugeParameter 1 point +
              16 *
                p286LinkedActiveFullLocalDensityIncrement source configuration
                  gaugeParameter (-1) point -
              p286LinkedActiveFullLocalDensityIncrement source configuration
                gaugeParameter 2 point -
              p286LinkedActiveFullLocalDensityIncrement source configuration
                gaugeParameter (-2) point) by
    funext point
    exact p286LinkedActiveFullLocalSecondCoefficient_eq_increment source
      configuration smooth gaugeParameter point]
  exact continuous_const.mul
    ((((continuous_const.mul one).add
      (continuous_const.mul negOne)).sub two).sub negTwo)

/-- Continuity of the cubic coefficient on the same nondegenerate actual. -/
theorem p286LinkedActiveFullLocalThirdCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    Continuous fun point =>
      p286LinkedActiveFullLocalThirdCoefficient source configuration
        gaugeParameter point := by
  have one :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter 1
  have negOne :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter (-1)
  have two :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter 2
  have negTwo :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter (-2)
  rw [show
      (fun point =>
        p286LinkedActiveFullLocalThirdCoefficient source configuration
          gaugeParameter point) =
        fun point =>
          (1 / 12 : ℝ) *
            (p286LinkedActiveFullLocalDensityIncrement source configuration
                  gaugeParameter 2 point -
              p286LinkedActiveFullLocalDensityIncrement source configuration
                gaugeParameter (-2) point -
              2 *
                p286LinkedActiveFullLocalDensityIncrement source configuration
                  gaugeParameter 1 point +
              2 *
                p286LinkedActiveFullLocalDensityIncrement source configuration
                  gaugeParameter (-1) point) by
    funext point
    exact p286LinkedActiveFullLocalThirdCoefficient_eq_increment source
      configuration smooth gaugeParameter point]
  exact continuous_const.mul
    (((two.sub negTwo).sub (continuous_const.mul one)).add
      (continuous_const.mul negOne))

/-- Continuity of the quartic coefficient on the same nondegenerate actual. -/
theorem p286LinkedActiveFullLocalFourthCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    Continuous fun point =>
      p286LinkedActiveFullLocalFourthCoefficient source configuration
        gaugeParameter point := by
  have one :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter 1
  have negOne :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter (-1)
  have two :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter 2
  have negTwo :=
    p286LinkedActiveFullLocalDensityIncrement_continuous source configuration
      smooth nondegenerate gaugeParameter (-2)
  rw [show
      (fun point =>
        p286LinkedActiveFullLocalFourthCoefficient source configuration
          gaugeParameter point) =
        fun point =>
          (1 / 24 : ℝ) *
            (p286LinkedActiveFullLocalDensityIncrement source configuration
                  gaugeParameter 2 point +
              p286LinkedActiveFullLocalDensityIncrement source configuration
                gaugeParameter (-2) point -
              4 *
                p286LinkedActiveFullLocalDensityIncrement source configuration
                  gaugeParameter 1 point -
              4 *
                p286LinkedActiveFullLocalDensityIncrement source configuration
                  gaugeParameter (-1) point) by
    funext point
    exact p286LinkedActiveFullLocalFourthCoefficient_eq_increment source
      configuration smooth gaugeParameter point]
  exact continuous_const.mul
    (((two.add negTwo).sub (continuous_const.mul one)).sub
      (continuous_const.mul negOne))

/-! ## Public compact-support results -/

/-- The first coefficient is supported where the generated scalar tangent
is supported. -/
theorem p286LinkedActiveFullLocalFirstCoefficient_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    HasCompactSupport fun point =>
      p286LinkedActiveFullLocalFirstCoefficient source configuration
        gaugeParameter point := by
  let scalarVariation :=
    p286LinkedActiveScalarVariation configuration smooth gaugeParameter
  rw [hasCompactSupport_iff_eventuallyEq]
  have variationEventually := scalarVariation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  filter_upwards [variationEventually] with point variationZero
  have variationZero' : scalarVariation point = 0 := by
    simpa using variationZero
  have tangentScalarZero :
      (representationDerivedP286CoupledGaugeTangentAt configuration
        gaugeParameter point).scalar = 0 := by
    simpa [scalarVariation,
      representationDerivedP286CoupledGaugeTangentSection] using variationZero'
  rw [p286LinkedActiveFullLocalFirstCoefficient_eq_existing,
    linkedActiveFullLocalFirstVariationDensity_eq_torque source configuration
      smooth]
  unfold p286FrozenSourceScalarTorqueDensity
  rw [tangentScalarZero]
  simp

/-- The quadratic coefficient has compact support generated internally by the
same compact-smooth gauge parameter. -/
theorem p286LinkedActiveFullLocalSecondCoefficient_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    HasCompactSupport fun point =>
      p286LinkedActiveFullLocalSecondCoefficient source configuration
        gaugeParameter point := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have one :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter 1
  have negOne :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter (-1)
  have two :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter 2
  have negTwo :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter (-2)
  rw [hasCompactSupport_iff_eventuallyEq] at one negOne two negTwo
  filter_upwards [one, negOne, two, negTwo] with
    point oneZero negOneZero twoZero negTwoZero
  rw [p286LinkedActiveFullLocalSecondCoefficient_eq_increment source
    configuration smooth gaugeParameter point]
  simp [oneZero, negOneZero, twoZero, negTwoZero]

/-- The cubic coefficient has compact support generated internally by the
same compact-smooth gauge parameter. -/
theorem p286LinkedActiveFullLocalThirdCoefficient_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    HasCompactSupport fun point =>
      p286LinkedActiveFullLocalThirdCoefficient source configuration
        gaugeParameter point := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have one :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter 1
  have negOne :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter (-1)
  have two :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter 2
  have negTwo :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter (-2)
  rw [hasCompactSupport_iff_eventuallyEq] at one negOne two negTwo
  filter_upwards [one, negOne, two, negTwo] with
    point oneZero negOneZero twoZero negTwoZero
  rw [p286LinkedActiveFullLocalThirdCoefficient_eq_increment source
    configuration smooth gaugeParameter point]
  simp [oneZero, negOneZero, twoZero, negTwoZero]

/-- The quartic coefficient has compact support generated internally by the
same compact-smooth gauge parameter. -/
theorem p286LinkedActiveFullLocalFourthCoefficient_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    HasCompactSupport fun point =>
      p286LinkedActiveFullLocalFourthCoefficient source configuration
        gaugeParameter point := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have one :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter 1
  have negOne :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter (-1)
  have two :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter 2
  have negTwo :=
    p286LinkedActiveFullLocalDensityIncrement_compact source configuration
      smooth gaugeParameter (-2)
  rw [hasCompactSupport_iff_eventuallyEq] at one negOne two negTwo
  filter_upwards [one, negOne, two, negTwo] with
    point oneZero negOneZero twoZero negTwoZero
  rw [p286LinkedActiveFullLocalFourthCoefficient_eq_increment source
    configuration smooth gaugeParameter point]
  simp [oneZero, negOneZero, twoZero, negTwoZero]

/-! ## Public integrability results -/

/-- Integrability of the first coefficient follows from its generated
continuity and compact support. -/
theorem p286LinkedActiveFullLocalFirstCoefficient_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    Integrable fun point =>
      p286LinkedActiveFullLocalFirstCoefficient source configuration
        gaugeParameter point :=
  (p286LinkedActiveFullLocalFirstCoefficient_continuous source configuration
    smooth gaugeParameter).integrable_of_hasCompactSupport
      (p286LinkedActiveFullLocalFirstCoefficient_compact source configuration
        smooth gaugeParameter)

/-- Integrability of the quadratic coefficient on the nondegenerate actual. -/
theorem p286LinkedActiveFullLocalSecondCoefficient_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    Integrable fun point =>
      p286LinkedActiveFullLocalSecondCoefficient source configuration
        gaugeParameter point :=
  (p286LinkedActiveFullLocalSecondCoefficient_continuous source configuration
    smooth nondegenerate gaugeParameter).integrable_of_hasCompactSupport
      (p286LinkedActiveFullLocalSecondCoefficient_compact source configuration
        smooth gaugeParameter)

/-- Integrability of the cubic coefficient on the nondegenerate actual. -/
theorem p286LinkedActiveFullLocalThirdCoefficient_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    Integrable fun point =>
      p286LinkedActiveFullLocalThirdCoefficient source configuration
        gaugeParameter point :=
  (p286LinkedActiveFullLocalThirdCoefficient_continuous source configuration
    smooth nondegenerate gaugeParameter).integrable_of_hasCompactSupport
      (p286LinkedActiveFullLocalThirdCoefficient_compact source configuration
        smooth gaugeParameter)

/-- Integrability of the quartic coefficient on the nondegenerate actual. -/
theorem p286LinkedActiveFullLocalFourthCoefficient_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    Integrable fun point =>
      p286LinkedActiveFullLocalFourthCoefficient source configuration
        gaugeParameter point :=
  (p286LinkedActiveFullLocalFourthCoefficient_continuous source configuration
    smooth nondegenerate gaugeParameter).integrable_of_hasCompactSupport
      (p286LinkedActiveFullLocalFourthCoefficient_compact source configuration
        smooth gaugeParameter)

end

end
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveFullLocalDensityRegularity
