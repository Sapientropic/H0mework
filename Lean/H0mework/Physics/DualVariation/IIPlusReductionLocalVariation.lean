import H0mework.Physics.CoframeVariation.CoframeLocalVariation
import H0mework.Physics.Exterior.IIPlusReductionLocalVariation

/-!
# Local nonlinear `II+` reduction of the Dirac-dual form-native root

The primitive coframe follows `e + t h` while the gravity auxiliary is
recomputed from that same coframe as `B(t) = II+(e+t h)`.  Both the full path
and its constraint-free readout are evaluated in the repaired action hash.

The new reduced coefficient is defined directly as the repaired frozen-`B`
coframe Euler covector plus the unchanged gravity-auxiliary response in
`D II+(e)[h]`.  The direct multiplier reaction cancels between these two
partials.  Only neutral one-variable continuity lemmas are reused from the
previous nonlinear calculus; no old total derivative, stationarity receipt,
equation, fixed actual, or target response is consumed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusReductionLocalVariation

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeIIPlusReductionLocalVariation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineIIPlusRestriction

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! ## The repaired nonlinear local path -/

def diracDualFormNativeIIPlusJointLocalPathField
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) :
    StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus
    (withCoframe field (field.coframe + parameter • variation))

def diracDualFormNativeIIPlusJointLocalDensityPath
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
    (diracDualFormNativeIIPlusJointLocalPathField field variation parameter)

def diracDualFormNativeIIPlusReducedLocalDensityPath
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) : ℝ :=
  generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
    source (sourceGeneratedUnifiedCouplings source) 0 point
    (diracDualFormNativeIIPlusJointLocalPathField field variation parameter)

@[simp] theorem diracDualFormNativeIIPlusJointLocalPathField_zero
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusJointLocalPathField field variation 0 =
      restrictContinuumPointFieldToIIPlus field := by
  apply StageNineContinuumPointField.ext <;>
    simp [diracDualFormNativeIIPlusJointLocalPathField, withCoframe,
      restrictContinuumPointFieldToIIPlus]

theorem diracDualFormNativeIIPlusJointLocalDensityPath_eq_reduced
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) :
    diracDualFormNativeIIPlusJointLocalDensityPath source point field
        variation parameter =
      generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
        source (sourceGeneratedUnifiedCouplings source) 0 point
        (diracDualFormNativeIIPlusJointLocalPathField field variation
          parameter) := by
  unfold diracDualFormNativeIIPlusJointLocalDensityPath
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
  let variedField := withCoframe field
    (field.coframe + parameter • variation)
  have restriction :=
    generatedDiracDualFormNativeUnifiedLocalDensity_restrictToIIPlus source
      (sourceGeneratedUnifiedCouplings source) 0 point variedField
  simpa [variedField, diracDualFormNativeIIPlusJointLocalPathField] using
    restriction

theorem diracDualFormNativeIIPlusJointLocalDensityPath_eq_reducedPath
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusJointLocalDensityPath source point field
        variation =
      diracDualFormNativeIIPlusReducedLocalDensityPath source point field
        variation := by
  funext parameter
  exact diracDualFormNativeIIPlusJointLocalDensityPath_eq_reduced
    source point field variation parameter

theorem diracDualFormNativeIIPlusJointLocalDensityPath_hasDerivAt_iff_reduced
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (derivative : ℝ) :
    HasDerivAt
        (diracDualFormNativeIIPlusJointLocalDensityPath source point field
          variation) derivative 0 ↔
      HasDerivAt
        (diracDualFormNativeIIPlusReducedLocalDensityPath source point field
          variation) derivative 0 := by
  rw [diracDualFormNativeIIPlusJointLocalDensityPath_eq_reducedPath]

/-! ## Direct repaired-root auxiliary polynomial -/

@[simp] theorem generatedDiracDualFormNativeMatterDensity_withAuxiliary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (auxiliary : PhysicalBivector) :
    generatedDiracDualFormNativeMatterDensity source chart point
        (withFormNativeGravityAuxiliary field auxiliary) =
      generatedDiracDualFormNativeMatterDensity source chart point field :=
  rfl

/-- The repaired root directly reissues the unchanged gravity-auxiliary
quadratic law under its own action hash. -/
theorem generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_auxiliary_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        chart point
        (withFormNativeGravityAuxiliary field
          (field.gravityAuxiliary + parameter • variation)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
          chart point field +
        parameter *
          formNativeGravityAuxiliaryFirstVariationDensity field variation +
        parameter ^ 2 *
          formNativeGravityAuxiliaryBFQuadraticCoefficientDensity variation := by
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    formNativeGravityAuxiliaryFirstVariationDensity
  rw [generatedFormNativeGravityBFDensity_auxiliary_quadratic,
    generatedFormNativeGravityConstraintDensity_auxiliary_affine]
  simp only [generatedFormNativeGaugeDensityAtBoundary_withAuxiliary,
    generatedDiracDualFormNativeMatterDensity_withAuxiliary]
  ring

private theorem withCoframe_self
    (field : StageNineContinuumPointField) :
    withCoframe field field.coframe = field := by
  apply StageNineContinuumPointField.ext <;> rfl

/-- The nonlinear repaired path is its repaired frozen-`B` coframe path plus
the gravity-auxiliary polynomial of the same root. -/
theorem diracDualFormNativeIIPlusJointLocalDensityPath_eq_frozen_add_auxiliary
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) (parameter : ℝ) :
    diracDualFormNativeIIPlusJointLocalDensityPath source point field variation
        parameter =
      diracDualFormNativeCoframeLocalDensity source point
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
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_auxiliary_quadratic
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
      diracDualFormNativeIIPlusJointLocalPathField field variation parameter =
        withFormNativeGravityAuxiliary
          (withCoframe shellField variedCoframe)
          (physicalIIPlusBivector variedCoframe) := by
    apply StageNineContinuumPointField.ext <;> rfl
  unfold diracDualFormNativeIIPlusJointLocalDensityPath
  rw [pathFieldEquality]
  simpa [sourceGeneratedDiracDualFormNativeUnifiedLocalDensity,
    diracDualFormNativeCoframeLocalDensity, shellField, variedCoframe,
    auxiliaryDirection] using expansion

/-! ## Action-generated reduced response -/

def diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) : ℝ :=
  let shellField := restrictContinuumPointFieldToIIPlus field
  diracDualFormNativeCoframeEulerCovector source point shellField variation +
    formNativeGravityAuxiliaryFirstVariationDensity shellField
      (physicalIIPlusCoframeTangent field.coframe variation)

theorem diracDualFormNativeIIPlusJointLocalDensityPath_hasDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    HasDerivAt
      (diracDualFormNativeIIPlusJointLocalDensityPath source point field
        variation)
      (diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
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
  have frozenDerivative :=
    diracDualFormNativeCoframeLocalDensity_path_hasDerivAt source point
      shellField (by simpa [shellField] using nondegenerate) variation
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
      diracDualFormNativeIIPlusJointLocalDensityPath source point field
          variation =
        fun parameter =>
          diracDualFormNativeCoframeLocalDensity source point shellField
              (field.coframe + parameter • variation) +
            parameter * firstCoefficient parameter +
            parameter * (parameter * quadraticCoefficient parameter) := by
    funext parameter
    rw [diracDualFormNativeIIPlusJointLocalDensityPath_eq_frozen_add_auxiliary]
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
          diracDualFormNativeCoframeLocalDensity source point shellField
              (field.coframe + parameter • variation) +
            parameter * firstCoefficient parameter +
            parameter * (parameter * quadraticCoefficient parameter))
        (diracDualFormNativeCoframeEulerCovector source point shellField
            variation +
          firstCoefficient 0 + 0 * quadraticCoefficient 0) 0 := by
    apply sumDerivative.congr_of_eventuallyEq
    filter_upwards [] with parameter
    rfl
  have coefficientEquality :
      diracDualFormNativeCoframeEulerCovector source point shellField
            variation +
          firstCoefficient 0 + 0 * quadraticCoefficient 0 =
        diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
          source point field variation := by
    dsimp [firstCoefficient, quadraticCoefficient]
    simp only [zero_smul, add_zero, zero_mul]
    rw [baseFieldEquality]
    rfl
  exact combinedDerivative.congr_deriv coefficientEquality

theorem diracDualFormNativeIIPlusReducedLocalDensityPath_hasDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    HasDerivAt
      (diracDualFormNativeIIPlusReducedLocalDensityPath source point field
        variation)
      (diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation) 0 := by
  exact
    (diracDualFormNativeIIPlusJointLocalDensityPath_hasDerivAt_iff_reduced
      source point field variation
        (diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
          source point field variation)).mp
      (diracDualFormNativeIIPlusJointLocalDensityPath_hasDerivAt
        source point field nondegenerate variation)

/-! ## Constraint-reaction cancellation and the B-equation seam -/

theorem diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_common_add_bf
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation =
      diracDualFormNativeCoframeCommonCoreEulerCovector source point
          (restrictContinuumPointFieldToIIPlus field) variation +
        formNativeGravityAuxiliaryBFFirstVariationDensity
          (restrictContinuumPointFieldToIIPlus field)
          (physicalIIPlusCoframeTangent field.coframe variation) := by
  let shellField := restrictContinuumPointFieldToIIPlus field
  change
    diracDualFormNativeCoframeEulerCovector source point shellField variation +
        formNativeGravityAuxiliaryFirstVariationDensity shellField
          (physicalIIPlusCoframeTangent field.coframe variation) =
      diracDualFormNativeCoframeCommonCoreEulerCovector source point shellField
          variation +
        formNativeGravityAuxiliaryBFFirstVariationDensity shellField
          (physicalIIPlusCoframeTangent field.coframe variation)
  rw [diracDualFormNativeCoframeEulerCovector_apply source point shellField
    (by simpa [shellField] using nondegenerate) variation]
  unfold formNativeGravityAuxiliaryFirstVariationDensity
  rw [formNativeCoframeConstraintReaction_eq_auxiliaryConstraintVariation]
  simp only [shellField, restrictContinuumPointFieldToIIPlus_coframe]
  ring

theorem diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_add_auxiliary
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation =
      diracDualFormNativeCoframeEulerCovector source point
          (restrictContinuumPointFieldToIIPlus field) variation +
        formNativeGravityAuxiliaryFirstVariationDensity
          (restrictContinuumPointFieldToIIPlus field)
          (physicalIIPlusCoframeTangent field.coframe variation) :=
  rfl

theorem diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_frozenCoframe_of_auxiliaryEulerZero
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe)
    (auxiliaryZero :
      formNativeGravityAuxiliaryEulerResidual
        (restrictContinuumPointFieldToIIPlus field) = 0) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
        source point field variation =
      diracDualFormNativeCoframeEulerCovector source point
        (restrictContinuumPointFieldToIIPlus field) variation := by
  have auxiliaryVariationZero :
      formNativeGravityAuxiliaryFirstVariationDensity
          (restrictContinuumPointFieldToIIPlus field)
          (physicalIIPlusCoframeTangent field.coframe variation) = 0 := by
    rw [formNativeGravityAuxiliaryFirstVariationDensity_eq_eulerPairing,
      auxiliaryZero]
    simp
  rw [diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_add_auxiliary,
    auxiliaryVariationZero]
  ring

theorem diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_zero_iff_frozenCoframe
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : LorentzianCoframe)
    (auxiliaryZero :
      formNativeGravityAuxiliaryEulerResidual
        (restrictContinuumPointFieldToIIPlus field) = 0) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
          source point field variation = 0 ↔
      diracDualFormNativeCoframeEulerCovector source point
          (restrictContinuumPointFieldToIIPlus field) variation = 0 := by
  rw [diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_frozenCoframe_of_auxiliaryEulerZero
    source point field variation auxiliaryZero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIIPlusReductionLocalVariation
