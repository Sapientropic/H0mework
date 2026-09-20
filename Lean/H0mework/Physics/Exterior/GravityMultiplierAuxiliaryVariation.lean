import H0mework.Physics.Exterior.MotherAction

/-!
# Form-native gravity multiplier and auxiliary variations

This module derives the two algebraic gravity legs of the form-native mother
action from actual affine paths in the primitive holonomic configuration.
The multiplier path produces the selected-branch simplicity residual.  The
gravity-auxiliary path produces

`N(F_raw) - star_internal(B) + lambda`,

where the historical curvature passes through the fixed variance
normalization exactly once.  Consequently the action-generated reaction is
uniquely

`lambda = star_internal(B) - N(F_raw)`.

Every derivative below is recomputed from the form-native density.  No
historical action derivative, stationarity theorem, fixed actual,
nondegeneracy premise, shell receipt, or supplied reaction is used.  This
checkpoint is pointwise and holonomic-local; compact-support integration and
the global weak equations remain a later analytic seam.
-/

namespace SaturationMonoid.PhysicsCore.StageNineFormNativeGravityMultiplierAuxiliaryVariation

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineTopologicalFourFormPairing
open StageNineTopologicalGravityCurvatureVariancePairing

noncomputable section

set_option autoImplicit false

private theorem gravityTopologicalWedgeCoefficient_sub_right
    (first second residual : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient residual (first - second) =
      gravityTopologicalWedgeCoefficient residual first -
        gravityTopologicalWedgeCoefficient residual second := by
  rw [sub_eq_add_neg, gravityTopologicalWedgeCoefficient_add_right]
  rw [show -second = (-1 : ℝ) • second by simp,
    gravityTopologicalWedgeCoefficient_smul_right]
  ring

/-! ## Multiplier path and local derivative -/

/-- Replace only the primitive form-native gravity reaction multiplier. -/
def withFormNativeGravityMultiplier
    (field : StageNineContinuumPointField)
    (multiplier : PhysicalBivector) : StageNineContinuumPointField :=
  { field with gravitySimplicityMultiplier := multiplier }

@[simp] theorem generatedFormNativeGravityBFDensity_withMultiplier
    (field : StageNineContinuumPointField)
    (multiplier : PhysicalBivector) :
    generatedFormNativeGravityBFDensity
        (withFormNativeGravityMultiplier field multiplier) =
      generatedFormNativeGravityBFDensity field :=
  rfl

@[simp] theorem generatedFormNativeGaugeDensityAtBoundary_withMultiplier
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (multiplier : PhysicalBivector) :
    generatedFormNativeGaugeDensityAtBoundary boundary
        (withFormNativeGravityMultiplier field multiplier) =
      generatedFormNativeGaugeDensityAtBoundary boundary field :=
  rfl

@[simp] theorem generatedFormNativeMatterDensity_withMultiplier
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (multiplier : PhysicalBivector) :
    generatedFormNativeMatterDensity source chart point
        (withFormNativeGravityMultiplier field multiplier) =
      generatedFormNativeMatterDensity source chart point field :=
  rfl

/-- The multiplier Euler residual is the actual selected-branch simplicity
residual, not a Boolean simplicity receipt. -/
def formNativeGravityMultiplierEulerResidual
    (field : StageNineContinuumPointField) : PhysicalBivector :=
  generatedGravitySimplicityResidual field

/-- Faithful `W22` dual of the multiplier Euler residual. -/
def formNativeGravityMultiplierEulerDual
    (field : StageNineContinuumPointField) :
    Module.Dual ℝ PhysicalBivector :=
  gravityTopologicalWedgeDual
    (formNativeGravityMultiplierEulerResidual field)

def formNativeGravityMultiplierFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  gravityTopologicalWedgeCoefficient variation
    (formNativeGravityMultiplierEulerResidual field)

theorem generatedFormNativeGravityConstraintDensity_multiplier_affine
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedFormNativeGravityConstraintDensity
        (withFormNativeGravityMultiplier field
          (field.gravitySimplicityMultiplier + parameter • variation)) =
      generatedFormNativeGravityConstraintDensity field +
        parameter *
          formNativeGravityMultiplierFirstVariationDensity field variation := by
  have residualEquality :
      generatedGravitySimplicityResidual
          (withFormNativeGravityMultiplier field
            (field.gravitySimplicityMultiplier + parameter • variation)) =
        generatedGravitySimplicityResidual field :=
    rfl
  unfold generatedFormNativeGravityConstraintDensity
    formNativeGravityMultiplierFirstVariationDensity
    formNativeGravityMultiplierEulerResidual
  rw [residualEquality]
  change gravityTopologicalWedgeCoefficient
      (field.gravitySimplicityMultiplier + parameter • variation)
      (generatedGravitySimplicityResidual field) = _
  rw [gravityTopologicalWedgeCoefficient_add_left,
    gravityTopologicalWedgeCoefficient_smul_left]

theorem generatedFormNativeUnifiedLocalDensityAtBoundary_multiplier_affine
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
        (withFormNativeGravityMultiplier field
          (field.gravitySimplicityMultiplier + parameter • variation)) =
      generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
          field +
        parameter *
          formNativeGravityMultiplierFirstVariationDensity field variation := by
  unfold generatedFormNativeUnifiedLocalDensityAtBoundary
  rw [generatedFormNativeGravityConstraintDensity_multiplier_affine]
  simp only [generatedFormNativeGravityBFDensity_withMultiplier,
    generatedFormNativeGaugeDensityAtBoundary_withMultiplier,
    generatedFormNativeMatterDensity_withMultiplier]
  ring

theorem generatedFormNativeUnifiedLocalDensityAtBoundary_multiplier_hasDerivAt
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point
          (withFormNativeGravityMultiplier field
            (field.gravitySimplicityMultiplier + parameter • variation)))
      (formNativeGravityMultiplierFirstVariationDensity field variation) 0 := by
  let coefficient :=
    formNativeGravityMultiplierFirstVariationDensity field variation
  have formula :
      (fun parameter : ℝ =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point
          (withFormNativeGravityMultiplier field
            (field.gravitySimplicityMultiplier + parameter • variation))) =
        fun parameter =>
          generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
              point field +
            parameter * coefficient := by
    funext parameter
    exact
      generatedFormNativeUnifiedLocalDensityAtBoundary_multiplier_affine
        source boundary chart point field variation parameter
  rw [formula]
  simpa [coefficient] using
    ((hasDerivAt_id (x := (0 : ℝ))).mul_const coefficient).const_add
      (generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
        point field)

theorem formNativeGravityMultiplierFirstVariationDensity_eq_eulerDual
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) :
    formNativeGravityMultiplierFirstVariationDensity field variation =
      formNativeGravityMultiplierEulerDual field variation := by
  unfold formNativeGravityMultiplierFirstVariationDensity
    formNativeGravityMultiplierEulerDual gravityTopologicalWedgeDual
  rw [gravityTopologicalWedgeCoefficient_symmetric]
  rfl

theorem formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
    (field : StageNineContinuumPointField) :
    formNativeGravityMultiplierEulerResidual field = 0 ↔
      field.gravityAuxiliary = physicalIIPlusBivector field.coframe := by
  simp [formNativeGravityMultiplierEulerResidual,
    generatedGravitySimplicityResidual, sub_eq_zero]

theorem formNativeGravityMultiplierEulerDual_eq_zero_iff
    (field : StageNineContinuumPointField) :
    formNativeGravityMultiplierEulerDual field = 0 ↔
      formNativeGravityMultiplierEulerResidual field = 0 :=
  gravityTopologicalWedgeDual_eq_zero_iff
    (formNativeGravityMultiplierEulerResidual field)

theorem formNativeGravityMultiplierEulerDual_eq_zero_iff_simplicity
    (field : StageNineContinuumPointField) :
    formNativeGravityMultiplierEulerDual field = 0 ↔
      field.gravityAuxiliary = physicalIIPlusBivector field.coframe := by
  rw [formNativeGravityMultiplierEulerDual_eq_zero_iff,
    formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity]

/-! ## Actual holonomic multiplier path -/

def varyFormNativeGravityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravitySimplicityMultiplier := fun point =>
      configuration.gravitySimplicityMultiplier point +
        parameter • variation point }

theorem toContinuumPointField_varyFormNativeGravityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ)
    (point : BasePoint) :
    toContinuumPointField
        (varyFormNativeGravityMultiplier configuration variation parameter)
        point =
      withFormNativeGravityMultiplier
        (toContinuumPointField configuration point)
        (configuration.gravitySimplicityMultiplier point +
          parameter • variation point) :=
  rfl

def holonomicFormNativeGravityMultiplierFirstVariationDensity
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector)
    (point : BasePoint) : ℝ :=
  formNativeGravityMultiplierFirstVariationDensity
    (toContinuumPointField configuration point) (variation point)

theorem holonomicFormNativeLocalDensity_multiplier_affine
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
        (toContinuumPointField
          (varyFormNativeGravityMultiplier configuration variation parameter)
          point) =
      generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeGravityMultiplierFirstVariationDensity
            configuration variation point := by
  rw [toContinuumPointField_varyFormNativeGravityMultiplier]
  exact
    generatedFormNativeUnifiedLocalDensityAtBoundary_multiplier_affine source
      boundary chart point (toContinuumPointField configuration point)
      (variation point) parameter

theorem holonomicFormNativeLocalDensity_multiplier_hasDerivAt
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point
          (toContinuumPointField
            (varyFormNativeGravityMultiplier configuration variation parameter)
            point))
      (holonomicFormNativeGravityMultiplierFirstVariationDensity configuration
        variation point) 0 := by
  have formula :
      (fun parameter : ℝ =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point
          (toContinuumPointField
            (varyFormNativeGravityMultiplier configuration variation parameter)
            point)) =
        fun parameter =>
          generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
              point (toContinuumPointField configuration point) +
            parameter *
              holonomicFormNativeGravityMultiplierFirstVariationDensity
                configuration variation point := by
    funext parameter
    exact holonomicFormNativeLocalDensity_multiplier_affine source boundary
      chart point configuration variation parameter
  rw [formula]
  simpa using
    ((hasDerivAt_id (x := (0 : ℝ))).mul_const
      (holonomicFormNativeGravityMultiplierFirstVariationDensity configuration
        variation point)).const_add
      (generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
        point (toContinuumPointField configuration point))

/-! ## Gravity-auxiliary path and exact quadratic law -/

/-- Replace only the primitive form-native gravity auxiliary two-form. -/
def withFormNativeGravityAuxiliary
    (field : StageNineContinuumPointField)
    (auxiliary : PhysicalBivector) : StageNineContinuumPointField :=
  { field with gravityAuxiliary := auxiliary }

@[simp] theorem generatedFormNativeGaugeDensityAtBoundary_withAuxiliary
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (auxiliary : PhysicalBivector) :
    generatedFormNativeGaugeDensityAtBoundary boundary
        (withFormNativeGravityAuxiliary field auxiliary) =
      generatedFormNativeGaugeDensityAtBoundary boundary field :=
  rfl

@[simp] theorem generatedFormNativeMatterDensity_withAuxiliary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (auxiliary : PhysicalBivector) :
    generatedFormNativeMatterDensity source chart point
        (withFormNativeGravityAuxiliary field auxiliary) =
      generatedFormNativeMatterDensity source chart point field :=
  rfl

/-- Pointwise `B` Euler residual.  The historical lowered curvature is raised
by the unique variance authority exactly once. -/
def formNativeGravityAuxiliaryEulerResidual
    (field : StageNineContinuumPointField) : PhysicalBivector :=
  gravityInternalPairVarianceNormalization field.gravityCurvature -
    gravityInternalDualEquiv field.gravityAuxiliary +
    field.gravitySimplicityMultiplier

/-- The unique form-native reaction read from fixed primitive `F_raw` and
`B`; it contains no inverse witness or branch choice. -/
def formNativeGravityReactionOfBF
    (field : StageNineContinuumPointField) : PhysicalBivector :=
  gravityInternalDualEquiv field.gravityAuxiliary -
    gravityInternalPairVarianceNormalization field.gravityCurvature

def formNativeGravityAuxiliaryBFFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  gravityTopologicalBFCoefficient variation field.gravityCurvature -
    (1 / 2 : ℝ) *
      (gravityTopologicalWedgeCoefficient variation
          (gravityInternalDualEquiv field.gravityAuxiliary) +
        gravityTopologicalWedgeCoefficient field.gravityAuxiliary
          (gravityInternalDualEquiv variation))

def formNativeGravityAuxiliaryBFQuadraticCoefficientDensity
    (variation : PhysicalBivector) : ℝ :=
  -(1 / 2 : ℝ) *
    gravityTopologicalWedgeCoefficient variation
      (gravityInternalDualEquiv variation)

def formNativeGravityAuxiliaryConstraintFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  gravityTopologicalWedgeCoefficient field.gravitySimplicityMultiplier
    variation

def formNativeGravityAuxiliaryFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  formNativeGravityAuxiliaryBFFirstVariationDensity field variation +
    formNativeGravityAuxiliaryConstraintFirstVariationDensity field variation

theorem generatedFormNativeGravityBFDensity_auxiliary_quadratic
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedFormNativeGravityBFDensity
        (withFormNativeGravityAuxiliary field
          (field.gravityAuxiliary + parameter • variation)) =
      generatedFormNativeGravityBFDensity field +
        parameter *
          formNativeGravityAuxiliaryBFFirstVariationDensity field variation +
        parameter ^ 2 *
          formNativeGravityAuxiliaryBFQuadraticCoefficientDensity variation := by
  unfold generatedFormNativeGravityBFDensity
    formNativeGravityAuxiliaryBFFirstVariationDensity
    formNativeGravityAuxiliaryBFQuadraticCoefficientDensity
    gravityTopologicalBFCoefficient withFormNativeGravityAuxiliary
  simp only [gravityTopologicalWedgeCoefficient_add_left,
    gravityTopologicalWedgeCoefficient_smul_left,
    gravityTopologicalWedgeCoefficient_add_right,
    gravityTopologicalWedgeCoefficient_smul_right, map_add, map_smul]
  ring

theorem generatedFormNativeGravityConstraintDensity_auxiliary_affine
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedFormNativeGravityConstraintDensity
        (withFormNativeGravityAuxiliary field
          (field.gravityAuxiliary + parameter • variation)) =
      generatedFormNativeGravityConstraintDensity field +
        parameter *
          formNativeGravityAuxiliaryConstraintFirstVariationDensity
            field variation := by
  have residualEquality :
      generatedGravitySimplicityResidual
          (withFormNativeGravityAuxiliary field
            (field.gravityAuxiliary + parameter • variation)) =
        generatedGravitySimplicityResidual field + parameter • variation := by
    funext internalPair spacetimePair
    simp [generatedGravitySimplicityResidual,
      withFormNativeGravityAuxiliary]
    ring
  unfold generatedFormNativeGravityConstraintDensity
    formNativeGravityAuxiliaryConstraintFirstVariationDensity
  rw [residualEquality, gravityTopologicalWedgeCoefficient_add_right,
    gravityTopologicalWedgeCoefficient_smul_right]
  rfl

theorem generatedFormNativeUnifiedLocalDensityAtBoundary_auxiliary_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
        (withFormNativeGravityAuxiliary field
          (field.gravityAuxiliary + parameter • variation)) =
      generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
          field +
        parameter *
          formNativeGravityAuxiliaryFirstVariationDensity field variation +
        parameter ^ 2 *
          formNativeGravityAuxiliaryBFQuadraticCoefficientDensity variation := by
  unfold generatedFormNativeUnifiedLocalDensityAtBoundary
    formNativeGravityAuxiliaryFirstVariationDensity
  rw [generatedFormNativeGravityBFDensity_auxiliary_quadratic,
    generatedFormNativeGravityConstraintDensity_auxiliary_affine]
  simp only [generatedFormNativeGaugeDensityAtBoundary_withAuxiliary,
    generatedFormNativeMatterDensity_withAuxiliary]
  ring

theorem generatedFormNativeUnifiedLocalDensityAtBoundary_auxiliary_hasDerivAt
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point
          (withFormNativeGravityAuxiliary field
            (field.gravityAuxiliary + parameter • variation)))
      (formNativeGravityAuxiliaryFirstVariationDensity field variation) 0 := by
  let firstCoefficient :=
    formNativeGravityAuxiliaryFirstVariationDensity field variation
  let quadraticCoefficient :=
    formNativeGravityAuxiliaryBFQuadraticCoefficientDensity variation
  have formula :
      (fun parameter : ℝ =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point
          (withFormNativeGravityAuxiliary field
            (field.gravityAuxiliary + parameter • variation))) =
        fun parameter =>
          generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
              point field +
            parameter * firstCoefficient +
            parameter ^ 2 * quadraticCoefficient := by
    funext parameter
    exact generatedFormNativeUnifiedLocalDensityAtBoundary_auxiliary_quadratic
      source boundary chart point field variation parameter
  rw [formula]
  change HasDerivAt
    ((fun parameter =>
      generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point field +
        parameter * firstCoefficient) +
      fun parameter => parameter ^ 2 * quadraticCoefficient)
    firstCoefficient 0
  simpa using
    ((((hasDerivAt_id (x := (0 : ℝ))).mul_const firstCoefficient).const_add
      (generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
        point field)).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const
        quadraticCoefficient))

theorem formNativeGravityAuxiliaryFirstVariationDensity_eq_eulerPairing
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) :
    formNativeGravityAuxiliaryFirstVariationDensity field variation =
      gravityTopologicalWedgeCoefficient variation
        (formNativeGravityAuxiliaryEulerResidual field) := by
  unfold formNativeGravityAuxiliaryFirstVariationDensity
    formNativeGravityAuxiliaryBFFirstVariationDensity
    formNativeGravityAuxiliaryConstraintFirstVariationDensity
    formNativeGravityAuxiliaryEulerResidual
    gravityTopologicalBFCoefficient
  rw [gravityTopologicalWedgeCoefficient_internalDual_symmetric
    field.gravityAuxiliary variation]
  rw [gravityTopologicalWedgeCoefficient_symmetric
    field.gravitySimplicityMultiplier variation]
  rw [gravityTopologicalWedgeCoefficient_add_right,
    gravityTopologicalWedgeCoefficient_sub_right]
  ring

/-- Faithful `W22` dual of the form-native `B` Euler residual. -/
def formNativeGravityAuxiliaryEulerDual
    (field : StageNineContinuumPointField) :
    Module.Dual ℝ PhysicalBivector :=
  gravityTopologicalWedgeDual
    (formNativeGravityAuxiliaryEulerResidual field)

theorem formNativeGravityAuxiliaryFirstVariationDensity_eq_eulerDual
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) :
    formNativeGravityAuxiliaryFirstVariationDensity field variation =
      formNativeGravityAuxiliaryEulerDual field variation := by
  rw [formNativeGravityAuxiliaryFirstVariationDensity_eq_eulerPairing,
    gravityTopologicalWedgeCoefficient_symmetric]
  rfl

theorem formNativeGravityAuxiliaryEulerDual_eq_zero_iff
    (field : StageNineContinuumPointField) :
    formNativeGravityAuxiliaryEulerDual field = 0 ↔
      formNativeGravityAuxiliaryEulerResidual field = 0 :=
  gravityTopologicalWedgeDual_eq_zero_iff
    (formNativeGravityAuxiliaryEulerResidual field)

theorem formNativeGravityAuxiliaryEulerResidual_eq_zero_iff_reaction
    (field : StageNineContinuumPointField) :
    formNativeGravityAuxiliaryEulerResidual field = 0 ↔
      field.gravitySimplicityMultiplier =
        formNativeGravityReactionOfBF field := by
  constructor
  · intro residualZero
    funext internalPair spacetimePair
    have componentZero := congrFun
      (congrFun residualZero internalPair) spacetimePair
    simp [formNativeGravityAuxiliaryEulerResidual,
      formNativeGravityReactionOfBF] at componentZero ⊢
    linarith
  · intro reaction
    funext internalPair spacetimePair
    have componentReaction := congrFun
      (congrFun reaction internalPair) spacetimePair
    simp [formNativeGravityAuxiliaryEulerResidual,
      formNativeGravityReactionOfBF] at componentReaction ⊢
    linarith

/-- No-free-parameter gate: fixed primitive raw curvature and `B` determine
exactly one form-native reaction multiplier. -/
theorem formNativeGravityReaction_existsUnique
    (rawCurvature auxiliary : PhysicalBivector) :
    ∃! multiplier : PhysicalBivector,
      gravityInternalPairVarianceNormalization rawCurvature -
          gravityInternalDualEquiv auxiliary + multiplier = 0 := by
  refine ⟨gravityInternalDualEquiv auxiliary -
      gravityInternalPairVarianceNormalization rawCurvature, ?_, ?_⟩
  · funext internalPair spacetimePair
    simp
  · intro multiplier equation
    funext internalPair spacetimePair
    have componentEquation := congrFun
      (congrFun equation internalPair) spacetimePair
    simp at componentEquation ⊢
    linarith

/-! ## Actual holonomic gravity-auxiliary path -/

def varyFormNativeGravityAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravityAuxiliary := fun point =>
      configuration.gravityAuxiliary point + parameter • variation point }

theorem toContinuumPointField_varyFormNativeGravityAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ)
    (point : BasePoint) :
    toContinuumPointField
        (varyFormNativeGravityAuxiliary configuration variation parameter)
        point =
      withFormNativeGravityAuxiliary
        (toContinuumPointField configuration point)
        (configuration.gravityAuxiliary point + parameter • variation point) :=
  rfl

def holonomicFormNativeGravityAuxiliaryEulerResidual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : PhysicalBivector :=
  formNativeGravityAuxiliaryEulerResidual
    (toContinuumPointField configuration point)

theorem holonomicFormNativeGravityAuxiliaryEulerResidual_eq
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicFormNativeGravityAuxiliaryEulerResidual configuration point =
      holonomicContravariantGravityCurvature configuration point -
        gravityInternalDualEquiv (configuration.gravityAuxiliary point) +
        configuration.gravitySimplicityMultiplier point :=
  rfl

def holonomicFormNativeGravityAuxiliaryFirstVariationDensity
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector)
    (point : BasePoint) : ℝ :=
  formNativeGravityAuxiliaryFirstVariationDensity
    (toContinuumPointField configuration point) (variation point)

def holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
    (variation : BasePoint → PhysicalBivector)
    (point : BasePoint) : ℝ :=
  formNativeGravityAuxiliaryBFQuadraticCoefficientDensity (variation point)

theorem holonomicFormNativeLocalDensity_auxiliary_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
        (toContinuumPointField
          (varyFormNativeGravityAuxiliary configuration variation parameter)
          point) =
      generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeGravityAuxiliaryFirstVariationDensity
            configuration variation point +
        parameter ^ 2 *
          holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
            variation point := by
  rw [toContinuumPointField_varyFormNativeGravityAuxiliary]
  exact generatedFormNativeUnifiedLocalDensityAtBoundary_auxiliary_quadratic
    source boundary chart point (toContinuumPointField configuration point)
      (variation point) parameter

theorem holonomicFormNativeLocalDensity_auxiliary_hasDerivAt
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point
          (toContinuumPointField
            (varyFormNativeGravityAuxiliary configuration variation parameter)
            point))
      (holonomicFormNativeGravityAuxiliaryFirstVariationDensity configuration
        variation point) 0 := by
  let firstCoefficient :=
    holonomicFormNativeGravityAuxiliaryFirstVariationDensity configuration
      variation point
  let quadraticCoefficient :=
    holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity variation
      point
  have formula :
      (fun parameter : ℝ =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point
          (toContinuumPointField
            (varyFormNativeGravityAuxiliary configuration variation parameter)
            point)) =
        fun parameter =>
          generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
              point (toContinuumPointField configuration point) +
            parameter * firstCoefficient +
            parameter ^ 2 * quadraticCoefficient := by
    funext parameter
    exact holonomicFormNativeLocalDensity_auxiliary_quadratic source boundary
      chart point configuration variation parameter
  rw [formula]
  change HasDerivAt
    ((fun parameter =>
      generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
          point (toContinuumPointField configuration point) +
        parameter * firstCoefficient) +
      fun parameter => parameter ^ 2 * quadraticCoefficient)
    firstCoefficient 0
  simpa [firstCoefficient, quadraticCoefficient] using
    ((((hasDerivAt_id (x := (0 : ℝ))).mul_const firstCoefficient).const_add
      (generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
        point (toContinuumPointField configuration point))).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const
        quadraticCoefficient))

end

end SaturationMonoid.PhysicsCore.StageNineFormNativeGravityMultiplierAuxiliaryVariation
