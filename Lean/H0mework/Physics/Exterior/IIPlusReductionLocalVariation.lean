import H0mework.Physics.Coframe.CoframeLocalVariation
import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryVariation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Local nonlinear `II+` reduction of the form-native action

This module varies the primitive coframe by `e + t h` and recomputes the
gravity auxiliary from that same coframe:

`B(t) = II+(e + t h)`.

The resulting derivative is generated from the current form-native action.
It is the sum of the frozen-`B` coframe response and the gravity-auxiliary
response in `D II+(e)[h]`.  The direct multiplier reaction then cancels
between these two partials, leaving the reduced gravity-BF plus gauge and
matter response.

No historical residual-linear action derivative, stationarity theorem,
fixed actual, shell certificate, derivative receipt, or target response is
consumed.  This checkpoint is local and canonical-chart only; it does not
claim an integrated variation, Euler equation, four-leg critical locus,
Einstein--Cartan reduction, or root-action authority.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeIIPlusReductionLocalVariation

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeVariation
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineTopologicalFourFormPairing
open StageNineTopologicalGravityCurvatureVariancePairing
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! ## The actual nonlinear local path -/

/-- Replace the coframe and recompute `B := II+(e)` from that same coframe.
The input field's old gravity-auxiliary coordinate is not reused. -/
def formNativeIIPlusJointLocalPathField
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) :
    StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus
    (withCoframe field (field.coframe + parameter • variation))

/-- The current form-native density evaluated on the actual nonlinear
`II+` path. -/
def formNativeIIPlusJointLocalDensityPath
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) : ℝ :=
  sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
    (formNativeIIPlusJointLocalPathField field variation parameter)

/-- The constraint-free readout of the same actual nonlinear path. -/
def formNativeIIPlusReducedLocalDensityPath
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) : ℝ :=
  generatedFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary source
    (sourceGeneratedUnifiedCouplings source) 0 point
    (formNativeIIPlusJointLocalPathField field variation parameter)

@[simp] theorem formNativeIIPlusJointLocalPathField_zero
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    formNativeIIPlusJointLocalPathField field variation 0 =
      restrictContinuumPointFieldToIIPlus field := by
  apply StageNineContinuumPointField.ext <;>
    simp [formNativeIIPlusJointLocalPathField, withCoframe,
      restrictContinuumPointFieldToIIPlus]

/-- On the actual path the direct constraint vanishes pointwise. -/
theorem formNativeIIPlusJointLocalDensityPath_eq_reduced
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) :
    formNativeIIPlusJointLocalDensityPath source point field variation
        parameter =
      generatedFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (formNativeIIPlusJointLocalPathField field variation parameter) := by
  unfold formNativeIIPlusJointLocalDensityPath
    sourceGeneratedFormNativeUnifiedLocalDensity
  let variedField := withCoframe field
    (field.coframe + parameter • variation)
  have restriction := generatedFormNativeUnifiedLocalDensity_restrictToIIPlus
    source (sourceGeneratedUnifiedCouplings source) 0 point variedField
  simpa [variedField, formNativeIIPlusJointLocalPathField] using restriction

theorem formNativeIIPlusJointLocalDensityPath_eq_reducedPath
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    formNativeIIPlusJointLocalDensityPath source point field variation =
      formNativeIIPlusReducedLocalDensityPath source point field variation := by
  funext parameter
  exact formNativeIIPlusJointLocalDensityPath_eq_reduced
    source point field variation parameter

/-- Full-density and constraint-free derivative predicates are identical on
the same computed `II+` path.  This is an action-value seam, not a second
derivative producer. -/
theorem formNativeIIPlusJointLocalDensityPath_hasDerivAt_iff_reduced
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (derivative : ℝ) :
    HasDerivAt
        (formNativeIIPlusJointLocalDensityPath source point field variation)
        derivative 0 ↔
      HasDerivAt
        (formNativeIIPlusReducedLocalDensityPath source point field variation)
        derivative 0 := by
  rw [formNativeIIPlusJointLocalDensityPath_eq_reducedPath]

/-! ## Exact decomposition through the two primitive partials -/

private theorem withCoframe_self
    (field : StageNineContinuumPointField) :
    withCoframe field field.coframe = field := by
  apply StageNineContinuumPointField.ext <;> rfl

/-- Neutral one-variable calculus used by any action epoch whose path is
`t * coefficient t`.  The statement carries no action receipt. -/
theorem hasDerivAt_id_mul_of_continuousAt
    (coefficient : ℝ → ℝ)
    (continuous : ContinuousAt coefficient 0) :
    HasDerivAt (fun parameter : ℝ => parameter * coefficient parameter)
      (coefficient 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have limit :
      Filter.Tendsto coefficient
        (nhdsWithin 0 {0}ᶜ) (nhds (coefficient 0)) :=
    continuous.tendsto.mono_left inf_le_left
  apply limit.congr'
  filter_upwards [self_mem_nhdsWithin] with parameter parameterMem
  have nonzero : parameter ≠ 0 := by simpa using parameterMem
  simp [nonzero]

private theorem gravityTopologicalWedgeCoefficient_path_contDiffAt
    (first second : ℝ → PhysicalBivector)
    (firstSmooth : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ ∞
        (fun parameter => first parameter internalPair spacetimePair) 0)
    (secondSmooth : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ ∞
        (fun parameter => second parameter internalPair spacetimePair) 0) :
    ContDiffAt ℝ ∞ (fun parameter =>
      gravityTopologicalWedgeCoefficient
        (first parameter) (second parameter)) 0 := by
  unfold gravityTopologicalWedgeCoefficient
    orientedTwoFormWedgeCoefficient generatedTwoFormWedgeCoefficient
  apply ContDiffAt.sum
  intro internalPair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro spacetimePair _
  exact (firstSmooth internalPair spacetimePair).mul
    (secondSmooth internalPair (twoFormComplement spacetimePair))

private theorem gravityInternalDualEquiv_path_component_contDiffAt
    (bivectorPath : ℝ → PhysicalBivector)
    (bivectorSmooth : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ ∞ (fun parameter =>
        bivectorPath parameter internalPair spacetimePair) 0)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ ∞ (fun parameter =>
      gravityInternalDualEquiv (bivectorPath parameter)
        internalPair spacetimePair) 0 := by
  fin_cases internalPair
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      bivectorSmooth 3 spacetimePair
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      bivectorSmooth 4 spacetimePair
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      bivectorSmooth 5 spacetimePair
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      (bivectorSmooth 0 spacetimePair).neg
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      (bivectorSmooth 1 spacetimePair).neg
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      (bivectorSmooth 2 spacetimePair).neg

/-- Formulation-neutral continuity of the gravity-auxiliary first coefficient
along a coframe-generated `II+` direction. -/
theorem formNativeAuxiliaryFirstCoefficient_contDiffAt
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    ContDiffAt ℝ ∞ (fun parameter : ℝ =>
      formNativeGravityAuxiliaryFirstVariationDensity
        (withCoframe (restrictContinuumPointFieldToIIPlus field)
          (field.coframe + parameter • variation))
        (physicalIIPlusCoframeTangent field.coframe variation +
          parameter • physicalIIPlusBivector variation)) 0 := by
  let shellField := restrictContinuumPointFieldToIIPlus field
  let direction := fun parameter : ℝ =>
    physicalIIPlusCoframeTangent field.coframe variation +
      parameter • physicalIIPlusBivector variation
  have directionSmooth : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ ∞ (fun parameter =>
        direction parameter internalPair spacetimePair) 0 := by
    intro internalPair spacetimePair
    unfold direction
    fun_prop
  have dualDirectionSmooth : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ ∞ (fun parameter =>
        gravityInternalDualEquiv (direction parameter)
          internalPair spacetimePair) 0 :=
    gravityInternalDualEquiv_path_component_contDiffAt
      direction directionSmooth
  have bfSmooth : ContDiffAt ℝ ∞ (fun parameter =>
      gravityTopologicalBFCoefficient (direction parameter)
        shellField.gravityCurvature) 0 := by
    unfold gravityTopologicalBFCoefficient
    exact gravityTopologicalWedgeCoefficient_path_contDiffAt direction
      (fun _ => gravityInternalPairVarianceNormalization
        shellField.gravityCurvature) directionSmooth
      (fun _ _ => contDiffAt_const)
  have firstCrossSmooth : ContDiffAt ℝ ∞ (fun parameter =>
      gravityTopologicalWedgeCoefficient (direction parameter)
        (gravityInternalDualEquiv shellField.gravityAuxiliary)) 0 :=
    gravityTopologicalWedgeCoefficient_path_contDiffAt direction
      (fun _ => gravityInternalDualEquiv shellField.gravityAuxiliary)
      directionSmooth (fun _ _ => contDiffAt_const)
  have secondCrossSmooth : ContDiffAt ℝ ∞ (fun parameter =>
      gravityTopologicalWedgeCoefficient shellField.gravityAuxiliary
        (gravityInternalDualEquiv (direction parameter))) 0 :=
    gravityTopologicalWedgeCoefficient_path_contDiffAt
      (fun _ => shellField.gravityAuxiliary)
      (fun parameter => gravityInternalDualEquiv (direction parameter))
      (fun _ _ => contDiffAt_const) dualDirectionSmooth
  have constraintSmooth : ContDiffAt ℝ ∞ (fun parameter =>
      gravityTopologicalWedgeCoefficient
        shellField.gravitySimplicityMultiplier (direction parameter)) 0 :=
    gravityTopologicalWedgeCoefficient_path_contDiffAt
      (fun _ => shellField.gravitySimplicityMultiplier) direction
      (fun _ _ => contDiffAt_const) directionSmooth
  have scaledCrossSmooth : ContDiffAt ℝ ∞ (fun parameter =>
      (1 / 2 : ℝ) *
        (gravityTopologicalWedgeCoefficient (direction parameter)
            (gravityInternalDualEquiv shellField.gravityAuxiliary) +
          gravityTopologicalWedgeCoefficient shellField.gravityAuxiliary
            (gravityInternalDualEquiv (direction parameter)))) 0 :=
    (contDiffAt_const.mul
      (firstCrossSmooth.add secondCrossSmooth) :
        ContDiffAt ℝ ∞ (fun parameter =>
          (1 / 2 : ℝ) *
            (gravityTopologicalWedgeCoefficient (direction parameter)
                (gravityInternalDualEquiv shellField.gravityAuxiliary) +
              gravityTopologicalWedgeCoefficient shellField.gravityAuxiliary
                (gravityInternalDualEquiv (direction parameter)))) 0)
  have totalSmooth :=
    (bfSmooth.sub scaledCrossSmooth).add constraintSmooth
  change ContDiffAt ℝ ∞ (fun parameter =>
    gravityTopologicalBFCoefficient (direction parameter)
        shellField.gravityCurvature -
      (1 / 2 : ℝ) *
        (gravityTopologicalWedgeCoefficient (direction parameter)
            (gravityInternalDualEquiv shellField.gravityAuxiliary) +
          gravityTopologicalWedgeCoefficient shellField.gravityAuxiliary
            (gravityInternalDualEquiv (direction parameter))) +
      gravityTopologicalWedgeCoefficient
        shellField.gravitySimplicityMultiplier (direction parameter)) 0
  exact totalSmooth

/-- Formulation-neutral continuity of the gravity-auxiliary quadratic
coefficient along the same `II+` direction. -/
theorem formNativeAuxiliaryQuadraticCoefficient_contDiffAt
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    ContDiffAt ℝ ∞ (fun parameter : ℝ =>
      formNativeGravityAuxiliaryBFQuadraticCoefficientDensity
        (physicalIIPlusCoframeTangent field.coframe variation +
          parameter • physicalIIPlusBivector variation)) 0 := by
  let direction := fun parameter : ℝ =>
    physicalIIPlusCoframeTangent field.coframe variation +
      parameter • physicalIIPlusBivector variation
  have directionSmooth : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ ∞ (fun parameter =>
        direction parameter internalPair spacetimePair) 0 := by
    intro internalPair spacetimePair
    unfold direction
    fun_prop
  have dualDirectionSmooth : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ ∞ (fun parameter =>
        gravityInternalDualEquiv (direction parameter)
          internalPair spacetimePair) 0 :=
    gravityInternalDualEquiv_path_component_contDiffAt
      direction directionSmooth
  have pairingSmooth : ContDiffAt ℝ ∞ (fun parameter =>
      gravityTopologicalWedgeCoefficient (direction parameter)
        (gravityInternalDualEquiv (direction parameter))) 0 :=
    gravityTopologicalWedgeCoefficient_path_contDiffAt direction
      (fun parameter => gravityInternalDualEquiv (direction parameter))
      directionSmooth dualDirectionSmooth
  change ContDiffAt ℝ ∞ (fun parameter =>
    -(1 / 2 : ℝ) *
      gravityTopologicalWedgeCoefficient (direction parameter)
        (gravityInternalDualEquiv (direction parameter))) 0
  exact (contDiffAt_const.mul pairingSmooth :
    ContDiffAt ℝ ∞ (fun parameter =>
      -(1 / 2 : ℝ) *
        gravityTopologicalWedgeCoefficient (direction parameter)
          (gravityInternalDualEquiv (direction parameter))) 0)

/-- The actual nonlinear path is the frozen-`B` coframe path plus the exact
gravity-auxiliary polynomial of the same action. -/
theorem formNativeIIPlusJointLocalDensityPath_eq_frozen_add_auxiliary
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) :
    formNativeIIPlusJointLocalDensityPath source point field variation
        parameter =
      formNativeCoframeLocalDensity source point
          (restrictContinuumPointFieldToIIPlus field)
          (field.coframe + parameter • variation) +
        parameter *
          formNativeGravityAuxiliaryFirstVariationDensity
            (withCoframe (restrictContinuumPointFieldToIIPlus field)
              (field.coframe + parameter • variation))
            (physicalIIPlusCoframeTangent field.coframe variation +
              parameter • physicalIIPlusBivector variation) +
        parameter ^ 2 *
          formNativeGravityAuxiliaryBFQuadraticCoefficientDensity
            (physicalIIPlusCoframeTangent field.coframe variation +
              parameter • physicalIIPlusBivector variation) := by
  let shellField := restrictContinuumPointFieldToIIPlus field
  let variedCoframe := field.coframe + parameter • variation
  let auxiliaryDirection :=
    physicalIIPlusCoframeTangent field.coframe variation +
      parameter • physicalIIPlusBivector variation
  have expansion :=
    generatedFormNativeUnifiedLocalDensityAtBoundary_auxiliary_quadratic
      source (sourceGeneratedUnifiedCouplings source) 0 point
      (withCoframe shellField variedCoframe) auxiliaryDirection parameter
  have auxiliaryEquality :
      (withCoframe shellField variedCoframe).gravityAuxiliary +
          parameter • auxiliaryDirection =
        physicalIIPlusBivector variedCoframe := by
    change physicalIIPlusBivector field.coframe +
          parameter •
            (physicalIIPlusCoframeTangent field.coframe variation +
              parameter • physicalIIPlusBivector variation) =
        physicalIIPlusBivector
          (field.coframe + parameter • variation)
    rw [physicalIIPlusBivector_affine_expansion]
    funext internalPair spacetimePair
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [auxiliaryEquality] at expansion
  have pathFieldEquality :
      formNativeIIPlusJointLocalPathField field variation parameter =
        withFormNativeGravityAuxiliary
          (withCoframe shellField variedCoframe)
          (physicalIIPlusBivector variedCoframe) := by
    apply StageNineContinuumPointField.ext <;> rfl
  unfold formNativeIIPlusJointLocalDensityPath
  rw [pathFieldEquality]
  simpa [sourceGeneratedFormNativeUnifiedLocalDensity,
    formNativeCoframeLocalDensity, shellField, variedCoframe,
    auxiliaryDirection] using expansion

/-! ## The action-generated reduced response -/

/-- The local reduced response generated by the actual nonlinear path. -/
def formNativeIIPlusReducedCoframeFirstVariationDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) : ℝ :=
  let shellField := restrictContinuumPointFieldToIIPlus field
  formNativeCoframeEulerCovector source point shellField variation +
    formNativeGravityAuxiliaryFirstVariationDensity shellField
      (physicalIIPlusCoframeTangent field.coframe variation)

/-- The current action has the actual local nonlinear reduced derivative.
No Euler equation or stationarity premise is used. -/
theorem formNativeIIPlusJointLocalDensityPath_hasDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    HasDerivAt
      (formNativeIIPlusJointLocalDensityPath source point field variation)
      (formNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation) 0 := by
  let shellField := restrictContinuumPointFieldToIIPlus field
  let firstCoefficient := fun parameter : ℝ =>
    formNativeGravityAuxiliaryFirstVariationDensity
      (withCoframe shellField
        (field.coframe + parameter • variation))
      (physicalIIPlusCoframeTangent field.coframe variation +
        parameter • physicalIIPlusBivector variation)
  let quadraticCoefficient := fun parameter : ℝ =>
    formNativeGravityAuxiliaryBFQuadraticCoefficientDensity
      (physicalIIPlusCoframeTangent field.coframe variation +
        parameter • physicalIIPlusBivector variation)
  have frozenDerivative := formNativeCoframeLocalDensity_path_hasDerivAt
    source point shellField (by simpa [shellField] using nondegenerate)
      variation
  have firstContinuous : ContinuousAt firstCoefficient 0 :=
    (formNativeAuxiliaryFirstCoefficient_contDiffAt
      field variation).continuousAt
  have quadraticContinuous : ContinuousAt quadraticCoefficient 0 :=
    (formNativeAuxiliaryQuadraticCoefficient_contDiffAt
      field variation).continuousAt
  have firstDerivative :=
    hasDerivAt_id_mul_of_continuousAt firstCoefficient firstContinuous
  have quadraticTimesContinuous : ContinuousAt
      (fun parameter : ℝ => parameter * quadraticCoefficient parameter) 0 :=
    continuousAt_id.mul quadraticContinuous
  have quadraticDerivative :=
    hasDerivAt_id_mul_of_continuousAt
      (fun parameter : ℝ => parameter * quadraticCoefficient parameter)
      quadraticTimesContinuous
  have sumDerivative := (frozenDerivative.add firstDerivative).add
    quadraticDerivative
  have pathEquality :
      formNativeIIPlusJointLocalDensityPath source point field variation =
        fun parameter =>
          formNativeCoframeLocalDensity source point shellField
              (field.coframe + parameter • variation) +
            parameter * firstCoefficient parameter +
            parameter * (parameter * quadraticCoefficient parameter) := by
    funext parameter
    rw [formNativeIIPlusJointLocalDensityPath_eq_frozen_add_auxiliary]
    simp only [shellField, firstCoefficient, quadraticCoefficient]
    ring
  rw [pathEquality]
  have baseFieldEquality :
      withCoframe shellField field.coframe = shellField := by
    have coframeEquality : field.coframe = shellField.coframe := by rfl
    rw [coframeEquality]
    exact withCoframe_self shellField
  have combinedDerivative :
      HasDerivAt
        (fun parameter =>
          formNativeCoframeLocalDensity source point shellField
              (field.coframe + parameter • variation) +
            parameter * firstCoefficient parameter +
            parameter * (parameter * quadraticCoefficient parameter))
        (formNativeCoframeEulerCovector source point shellField variation +
          firstCoefficient 0 + 0 * quadraticCoefficient 0) 0 := by
    apply sumDerivative.congr_of_eventuallyEq
    filter_upwards [] with parameter
    rfl
  have coefficientEquality :
      formNativeCoframeEulerCovector source point shellField variation +
          firstCoefficient 0 + 0 * quadraticCoefficient 0 =
        formNativeIIPlusReducedCoframeFirstVariationDensity
          source point field variation := by
    dsimp [firstCoefficient, quadraticCoefficient]
    simp only [zero_smul, add_zero, zero_mul]
    rw [baseFieldEquality]
    rfl
  exact combinedDerivative.congr_deriv coefficientEquality

/-- The constraint-free readout has the same action-generated derivative on
the same computed `II+` path.  This is the direct consumer seam for later
reduced-action work; it does not introduce another derivative producer. -/
theorem formNativeIIPlusReducedLocalDensityPath_hasDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    HasDerivAt
      (formNativeIIPlusReducedLocalDensityPath source point field variation)
      (formNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation) 0 := by
  exact
    (formNativeIIPlusJointLocalDensityPath_hasDerivAt_iff_reduced
      source point field variation
        (formNativeIIPlusReducedCoframeFirstVariationDensity
          source point field variation)).mp
      (formNativeIIPlusJointLocalDensityPath_hasDerivAt
        source point field nondegenerate variation)

/-! ## Constraint-reaction cancellation and the B-equation seam -/

theorem formNativeCoframeConstraintReaction_eq_auxiliaryConstraintVariation
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    formNativeCoframeConstraintReaction field variation =
      formNativeGravityAuxiliaryConstraintFirstVariationDensity field
        (physicalIIPlusCoframeTangent field.coframe variation) :=
  rfl

/-- The multiplier reaction cancels between the two actual partials.  The
reduced response is exactly gauge plus matter plus the gravity-BF pullback. -/
theorem formNativeIIPlusReducedCoframeFirstVariationDensity_eq_common_add_bf
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    formNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation =
      formNativeCoframeCommonCoreEulerCovector source point
          (restrictContinuumPointFieldToIIPlus field) variation +
        formNativeGravityAuxiliaryBFFirstVariationDensity
          (restrictContinuumPointFieldToIIPlus field)
          (physicalIIPlusCoframeTangent field.coframe variation) := by
  let shellField := restrictContinuumPointFieldToIIPlus field
  change
    formNativeCoframeEulerCovector source point shellField variation +
        formNativeGravityAuxiliaryFirstVariationDensity shellField
          (physicalIIPlusCoframeTangent field.coframe variation) =
      formNativeCoframeCommonCoreEulerCovector source point shellField
          variation +
        formNativeGravityAuxiliaryBFFirstVariationDensity shellField
          (physicalIIPlusCoframeTangent field.coframe variation)
  rw [formNativeCoframeEulerCovector_apply source point shellField
    (by simpa [shellField] using nondegenerate) variation]
  unfold formNativeGravityAuxiliaryFirstVariationDensity
  rw [formNativeCoframeConstraintReaction_eq_auxiliaryConstraintVariation]
  simp only [shellField, restrictContinuumPointFieldToIIPlus_coframe]
  ring

/-- Exact chain-rule identity: the reduced response is the full frozen-`B`
coframe response plus the full `B` response in `D II+(e)[h]`. -/
theorem formNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_add_auxiliary
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    formNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation =
      formNativeCoframeEulerCovector source point
          (restrictContinuumPointFieldToIIPlus field) variation +
        formNativeGravityAuxiliaryFirstVariationDensity
          (restrictContinuumPointFieldToIIPlus field)
          (physicalIIPlusCoframeTangent field.coframe variation) :=
  rfl

/-- Once the independent `B` Euler residual vanishes on the same shell, the
reduced and frozen-`B` coframe responses coincide. -/
theorem formNativeIIPlusReducedCoframeFirstVariationDensity_eq_frozenCoframe_of_auxiliaryEulerZero
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe)
    (auxiliaryZero :
      formNativeGravityAuxiliaryEulerResidual
        (restrictContinuumPointFieldToIIPlus field) = 0) :
    formNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation =
      formNativeCoframeEulerCovector source point
        (restrictContinuumPointFieldToIIPlus field) variation := by
  have auxiliaryVariationZero :
      formNativeGravityAuxiliaryFirstVariationDensity
          (restrictContinuumPointFieldToIIPlus field)
          (physicalIIPlusCoframeTangent field.coframe variation) = 0 := by
    rw [formNativeGravityAuxiliaryFirstVariationDensity_eq_eulerPairing,
      auxiliaryZero]
    simp
  rw [formNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_add_auxiliary,
    auxiliaryVariationZero]
  ring

theorem formNativeIIPlusReducedCoframeFirstVariationDensity_eq_zero_iff_frozenCoframe
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe)
    (auxiliaryZero :
      formNativeGravityAuxiliaryEulerResidual
        (restrictContinuumPointFieldToIIPlus field) = 0) :
    formNativeIIPlusReducedCoframeFirstVariationDensity
          source point field variation = 0 ↔
      formNativeCoframeEulerCovector source point
          (restrictContinuumPointFieldToIIPlus field) variation = 0 := by
  rw [formNativeIIPlusReducedCoframeFirstVariationDensity_eq_frozenCoframe_of_auxiliaryEulerZero
    source point field variation auxiliaryZero]

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeIIPlusReductionLocalVariation
