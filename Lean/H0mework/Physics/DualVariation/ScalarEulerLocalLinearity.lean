import H0mework.Physics.ScalarJets.FixedJointScalarSegmentRegularity

/-!
# Local real linearity of the Dirac-dual scalar Euler covector

The scalar Euler coefficient is real-linear in its scalar variation whenever
the already supplied current has the local regularity needed to differentiate
its momentum.  The result exposes the action covector at one actual point; it
does not generate a field, choose a response, or consume a residual value.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeScalarEulerLocalLinearity

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

local instance scalarEulerLinearityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance scalarEulerLinearityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance scalarEulerLinearityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance scalarEulerLinearityP286CoordinateNormedAddCommGroup :
    NormedAddCommGroup P286CoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : P286CoordinateIndex => ℝ)

local instance scalarEulerLinearityP286CoordinateNormedSpace :
    NormedSpace ℝ P286CoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : P286CoordinateIndex => ℝ)

local instance scalarEulerLinearityBasePointNormedAddCommGroup :
    NormedAddCommGroup BasePoint :=
  PiLp.normedAddCommGroup 2 (fun _ : LorentzianIndex => ℝ)

local instance scalarEulerLinearityBasePointNormedSpace :
    NormedSpace ℝ BasePoint :=
  PiLp.normedSpace 2 ℝ (fun _ : LorentzianIndex => ℝ)

local instance scalarEulerLinearityCoframeNormedAddCommGroup :
    NormedAddCommGroup LorentzianCoframe :=
  inferInstanceAs (NormedAddCommGroup (Fin 4 → Fin 4 → ℝ))

local instance scalarEulerLinearityCoframeNormedSpace :
    NormedSpace ℝ LorentzianCoframe :=
  inferInstanceAs (NormedSpace ℝ (Fin 4 → Fin 4 → ℝ))

local instance scalarEulerLinearityCoordinateNormedAddCommGroup :
    NormedAddCommGroup ScalarCoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : ScalarBasisIndex => ℂ)

local instance scalarEulerLinearityCoordinateNormedSpace :
    NormedSpace ℝ ScalarCoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : ScalarBasisIndex => ℂ)

private theorem scalarVariationDifferentialDirection_add
    (first second : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarVariationDifferentialDirection (first + second)
        derivativeDirection =
      scalarVariationDifferentialDirection first derivativeDirection +
        scalarVariationDifferentialDirection second derivativeDirection := by
  funext formDirection
  by_cases same : formDirection = derivativeDirection <;>
    simp [scalarVariationDifferentialDirection, same]

private theorem scalarVariationDifferentialDirection_real_smul
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarVariationDifferentialDirection (parameter • direction)
        derivativeDirection =
      parameter •
        scalarVariationDifferentialDirection direction derivativeDirection := by
  funext formDirection
  simp [scalarVariationDifferentialDirection]

private theorem holonomicScalarVariationAlgebraicDirection_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : ScalarCoordinateCarrier)
    (point : BasePoint) :
    holonomicScalarVariationAlgebraicDirection configuration (first + second)
        point =
      holonomicScalarVariationAlgebraicDirection configuration first point +
        holonomicScalarVariationAlgebraicDirection configuration second point := by
  funext formDirection
  unfold holonomicScalarVariationAlgebraicDirection
  exact scalarMotherLieAction_add_right _ _ _

private theorem holonomicScalarVariationAlgebraicDirection_real_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    holonomicScalarVariationAlgebraicDirection configuration
        (parameter • direction) point =
      parameter •
        holonomicScalarVariationAlgebraicDirection configuration direction
          point := by
  funext formDirection
  unfold holonomicScalarVariationAlgebraicDirection
  exact scalarMotherLieAction_real_smul_right _ _ _

private theorem scalarPotentialFirstVariation_add
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (first second : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation source field (first + second) =
      scalarPotentialFirstVariation source field first +
        scalarPotentialFirstVariation source field second := by
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
  change
    2 * scalarCoordinatePairingRe
        (field.scalar - sourceGeneratedVacuumCoordinates source)
        (first + second) =
      2 * scalarCoordinatePairingRe
          (field.scalar - sourceGeneratedVacuumCoordinates source) first +
        2 * scalarCoordinatePairingRe
          (field.scalar - sourceGeneratedVacuumCoordinates source) second
  rw [scalarCoordinatePairingRe_add_right]
  ring

private theorem diracDualScalarYukawaFirstVariationDensity_add
    (field : StageNineContinuumPointField)
    (first second : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity field (first + second) =
      diracDualScalarYukawaFirstVariationDensity field first +
        diracDualScalarYukawaFirstVariationDensity field second := by
  unfold diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  rw [scalarCoordinateEquiv.symm.map_add,
    diracDualRightChiralYukawaAction_add, LinearMap.add_apply, map_add]
  exact Complex.add_re _ _

theorem scalarDifferentialMomentum_add
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (first second : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source configuration (first + second)
        derivativeDirection =
      scalarDifferentialMomentum source configuration first
          derivativeDirection +
        scalarDifferentialMomentum source configuration second
          derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
  rw [scalarVariationDifferentialDirection_add,
    scalarKineticFirstVariationDensity_add]
  simp only [Pi.add_apply]
  ring

theorem scalarDifferentialMomentum_real_smul
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source configuration
        (parameter • direction) derivativeDirection =
      parameter •
        scalarDifferentialMomentum source configuration direction
          derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
  rw [scalarVariationDifferentialDirection_real_smul,
    scalarKineticFirstVariationDensity_real_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem diracDualScalarAlgebraicDirectionalCoefficient_add
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (first second : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarAlgebraicDirectionalCoefficient source configuration
        (first + second) point =
      diracDualScalarAlgebraicDirectionalCoefficient source configuration
          first point +
        diracDualScalarAlgebraicDirectionalCoefficient source configuration
          second point := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [holonomicScalarVariationAlgebraicDirection_add,
    scalarKineticFirstVariationDensity_add,
    scalarPotentialFirstVariation_add,
    diracDualScalarYukawaFirstVariationDensity_add]
  ring

theorem diracDualScalarAlgebraicDirectionalCoefficient_real_smul
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarAlgebraicDirectionalCoefficient source configuration
        (parameter • direction) point =
      parameter *
        diracDualScalarAlgebraicDirectionalCoefficient source configuration
          direction point := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [holonomicScalarVariationAlgebraicDirection_real_smul,
    scalarKineticFirstVariationDensity_real_smul,
    scalarPotentialFirstVariation_real_smul,
    diracDualScalarYukawaFirstVariationDensity_real_smul]
  ring

private theorem scalarMomentumDirectionalDerivative_add_of_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ configuration.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ configuration.scalar point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (configuration.gaugeConnection candidate direction)) point)
    (first second : ScalarCoordinateCarrier)
    (momentumDirection derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum source configuration (first + second)
          momentumDirection)
        point derivativeDirection =
      fieldDirectionalDerivative
          (scalarDifferentialMomentum source configuration first
            momentumDirection)
          point derivativeDirection +
        fieldDirectionalDerivative
          (scalarDifferentialMomentum source configuration second
            momentumDirection)
          point derivativeDirection := by
  have firstDifferentiable : DifferentiableAt ℝ
      (scalarDifferentialMomentum source configuration first
        momentumDirection) point :=
    (scalarMomentum_contDiffAt_of_local source configuration point
      coframeNondegenerate coframeRegular scalarRegular
      gaugeConnectionRegular first momentumDirection).differentiableAt
      (by simp)
  have secondDifferentiable : DifferentiableAt ℝ
      (scalarDifferentialMomentum source configuration second
        momentumDirection) point :=
    (scalarMomentum_contDiffAt_of_local source configuration point
      coframeNondegenerate coframeRegular scalarRegular
      gaugeConnectionRegular second momentumDirection).differentiableAt
      (by simp)
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_add,
    fderiv_add firstDifferentiable secondDifferentiable, add_apply]

private theorem scalarMomentumDirectionalDerivative_real_smul_of_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ configuration.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ configuration.scalar point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (configuration.gaugeConnection candidate direction)) point)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (momentumDirection derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum source configuration
          (parameter • direction) momentumDirection)
        point derivativeDirection =
      parameter *
        fieldDirectionalDerivative
          (scalarDifferentialMomentum source configuration direction
            momentumDirection)
          point derivativeDirection := by
  have differentiable : DifferentiableAt ℝ
      (scalarDifferentialMomentum source configuration direction
        momentumDirection) point :=
    (scalarMomentum_contDiffAt_of_local source configuration point
      coframeNondegenerate coframeRegular scalarRegular
      gaugeConnectionRegular direction momentumDirection).differentiableAt
      (by simp)
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_real_smul]
  change
    (fderiv ℝ
      (fun candidate => parameter *
        scalarDifferentialMomentum source configuration direction
          momentumDirection candidate)
      point) (coordinateDirection derivativeDirection) = _
  rw [fderiv_const_mul differentiable parameter]
  rfl

theorem diracDualScalarEulerLagrangeDirectionalCoefficient_add_of_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ configuration.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ configuration.scalar point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (configuration.gaugeConnection candidate direction)) point)
    (first second : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
        (first + second) point =
      diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
          first point +
        diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
          second point := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  rw [diracDualScalarAlgebraicDirectionalCoefficient_add]
  simp_rw [scalarMomentumDirectionalDerivative_add_of_local source
    configuration point coframeNondegenerate coframeRegular scalarRegular
    gaugeConnectionRegular]
  rw [Finset.sum_add_distrib]
  ring

theorem diracDualScalarEulerLagrangeDirectionalCoefficient_real_smul_of_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ configuration.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ configuration.scalar point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (configuration.gaugeConnection candidate direction)) point)
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
        (parameter • direction) point =
      parameter *
        diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
          direction point := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  rw [diracDualScalarAlgebraicDirectionalCoefficient_real_smul]
  simp_rw [scalarMomentumDirectionalDerivative_real_smul_of_local source
    configuration point coframeNondegenerate coframeRegular scalarRegular
    gaugeConnectionRegular]
  rw [← Finset.mul_sum]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeScalarEulerLocalLinearity
