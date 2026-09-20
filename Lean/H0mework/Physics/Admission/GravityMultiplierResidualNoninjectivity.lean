import H0mework.Physics.Source.GeneratedPartialPrimitiveCarrier
import H0mework.Physics.Admission.JointShellResidualCarrier
import H0mework.Physics.Exterior.GravityAuxiliaryVariation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# S9-C3h12: gravity-multiplier residual noninjectivity

This module audits one explicit response-null class of the current Stage-9
joint residual.  Fix a holonomic configuration and vary only its smooth
gravity simplicity-multiplier field.  On the nondegenerate simplicity shell,
the zero multiplier and one explicit nonzero constant multiplier give the
same complete nine-channel joint residual section.

Consequently the current residual readout is not injective on this class and
cannot canonically recover a multiplier from residual data.  This is a
no-free-parameter / response-null-class no-go.  It is not a zero-fiber
producer, does not select a transport update from stationarity, and does not
authorize a new field, coupling, source slot, branch receipt, or change to the
action grammar.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityMultiplierResidualNoninjectivity

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineBlockwiseConstitutive
open StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open StageNineHolonomicField
open StageNinePlebanskiMultiplierVariation
open StageNineGravityAuxiliaryVariation
open StageNineJointShellResidualCarrier
open StageNineSourceGeneratedPartialPrimitiveCarrier
open EmpiricalReferenceScaleCouplingBoundary
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! ## Explicit smooth response-null class -/

/-- The carrier under audit consists only of smooth multiplier fields.  It
stores no equation, stationarity, source, branch, or transport receipt. -/
@[ext] structure SmoothGravityMultiplierField where
  toFun : BasePoint → PhysicalBivector
  smooth : ∀ internalPair spacetimePair,
    ContDiff ℝ ∞ fun point => toFun point internalPair spacetimePair

instance : CoeFun SmoothGravityMultiplierField
    (fun _ => BasePoint → PhysicalBivector) :=
  ⟨SmoothGravityMultiplierField.toFun⟩

/-- Replace only the multiplier field, fixing the other eight configuration
fields definitionally. -/
def installGravityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (multiplier : SmoothGravityMultiplierField) :
    StageNineHolonomicConfiguration :=
  { configuration with gravitySimplicityMultiplier := multiplier }

/-- Smoothness of the installed configuration uses only the candidate
multiplier's declared smoothness; this is not a source-generation theorem. -/
theorem installGravityMultiplier_smooth
    (configuration : StageNineHolonomicConfiguration)
    (configurationSmooth : configuration.Smooth)
    (multiplier : SmoothGravityMultiplierField) :
    (installGravityMultiplier configuration multiplier).Smooth := by
  rcases configurationSmooth with
    ⟨coframe, connection, auxiliary, _, gaugeConnection, gaugeAuxiliary,
      scalar, matter, conjugateMatter⟩
  exact ⟨coframe, connection, auxiliary, multiplier.smooth,
    gaugeConnection, gaugeAuxiliary, scalar, matter, conjugateMatter⟩

/-- The explicit zero member of the audited class.  It is used only as one
side of the noninjectivity witness and is not a source completion. -/
def zeroSmoothGravityMultiplierField : SmoothGravityMultiplierField where
  toFun := 0
  smooth := by
    intro internalPair spacetimePair
    exact contDiff_const

/-- An explicit nonzero constant member of the audited class.  It is not a
physical branch choice or a target solution. -/
def coordinateSmoothGravityMultiplierField :
    SmoothGravityMultiplierField where
  toFun := fun _ => physicalBivectorCoordinateDirection 0 0
  smooth := by
    intro internalPair spacetimePair
    exact contDiff_const

theorem zeroSmoothGravityMultiplierField_ne_coordinate :
    zeroSmoothGravityMultiplierField ≠
      coordinateSmoothGravityMultiplierField := by
  intro equality
  have valueEquality := congrArg
    (fun multiplier : SmoothGravityMultiplierField => multiplier 0 0 0)
    equality
  simpa [zeroSmoothGravityMultiplierField,
    coordinateSmoothGravityMultiplierField,
    physicalBivectorCoordinateDirection] using valueEquality

/-! The preceding pair is invisible only to the current first residual.
Its existing second auxiliary response still distinguishes the multiplier,
so this module does not quotient or discard the pending primitive field. -/

@[simp] theorem coordinateMultiplier_auxiliarySecondResponse_eq_one
    (field : StageNineContinuumPointField) :
    gravityAuxiliarySimplicitySecondVariationDensity
        (withGravitySimplicityMultiplier field
          (physicalBivectorCoordinateDirection 0 0))
        (physicalBivectorCoordinateDirection 0 0) = 1 := by
  simp [gravityAuxiliarySimplicitySecondVariationDensity,
    withGravitySimplicityMultiplier,
    physicalBivectorCoordinateDirection]

@[simp] theorem zeroMultiplier_auxiliarySecondResponse_eq_zero
    (field : StageNineContinuumPointField) :
    gravityAuxiliarySimplicitySecondVariationDensity
        (withGravitySimplicityMultiplier field 0)
        (physicalBivectorCoordinateDirection 0 0) = 0 := by
  simp [gravityAuxiliarySimplicitySecondVariationDensity,
    withGravitySimplicityMultiplier]

/-! ## The squared simplicity response is null along the explicit pair -/

theorem zeroMultiplier_withCoframe_fderiv_eq_zero
    (field : StageNineContinuumPointField) :
    fderiv ℝ
        (fun candidate : LorentzianCoframe =>
          generatedGravitySimplicityDensity
            (withCoframe
              (withGravitySimplicityMultiplier field 0) candidate))
        field.coframe = 0 := by
  have functionZero :
      (fun candidate : LorentzianCoframe =>
        generatedGravitySimplicityDensity
          (withCoframe
            (withGravitySimplicityMultiplier field 0) candidate)) =
        fun _ => (0 : ℝ) := by
    funext candidate
    simp [generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero,
      withCoframe, withGravitySimplicityMultiplier]
  rw [functionZero]
  have minimum : IsLocalMin (fun _ : LorentzianCoframe => (0 : ℝ))
      field.coframe := by
    exact Filter.Eventually.of_forall (fun _ => le_rfl)
  exact minimum.fderiv_eq_zero

theorem coordinateMultiplier_withCoframe_fderiv_eq_zero_of_simplicity
    (field : StageNineContinuumPointField)
    (simplicity : field.gravityAuxiliary =
      physicalIIPlusBivector field.coframe) :
    fderiv ℝ
        (fun candidate : LorentzianCoframe =>
          generatedGravitySimplicityDensity
            (withCoframe
              (withGravitySimplicityMultiplier field
                (physicalBivectorCoordinateDirection 0 0)) candidate))
        field.coframe = 0 := by
  have functionEquality :
      (fun candidate : LorentzianCoframe =>
        generatedGravitySimplicityDensity
          (withCoframe
            (withGravitySimplicityMultiplier field
              (physicalBivectorCoordinateDirection 0 0)) candidate)) =
        fun candidate =>
          (field.gravityAuxiliary 0 0 -
            physicalIIPlusBivector candidate 0 0) ^ 2 := by
    funext candidate
    simp [generatedGravitySimplicityDensity,
      gravitySimplicityMultiplierPairing,
      generatedGravitySimplicityResidual,
      withCoframe, withGravitySimplicityMultiplier,
      physicalBivectorCoordinateDirection]
  rw [functionEquality]
  have residualZero :
      field.gravityAuxiliary 0 0 -
        physicalIIPlusBivector field.coframe 0 0 = 0 := by
    rw [show field.gravityAuxiliary 0 0 =
      physicalIIPlusBivector field.coframe 0 0 by
        exact congrFun (congrFun simplicity 0) 0]
    exact sub_self _
  have localMinimum : IsLocalMin
      (fun candidate : LorentzianCoframe =>
        (field.gravityAuxiliary 0 0 -
          physicalIIPlusBivector candidate 0 0) ^ 2)
      field.coframe := by
    apply Filter.Eventually.of_forall
    intro candidate
    change
      (field.gravityAuxiliary 0 0 -
        physicalIIPlusBivector field.coframe 0 0) ^ 2 ≤ _
    rw [residualZero]
    simpa using (sq_nonneg
      (field.gravityAuxiliary 0 0 -
        physicalIIPlusBivector candidate 0 0 : ℝ))
  exact localMinimum.fderiv_eq_zero

theorem generatedGravitySimplicityDensity_eq_zero_of_simplicity
    (field : StageNineContinuumPointField)
    (simplicity : field.gravityAuxiliary =
      physicalIIPlusBivector field.coframe) :
    generatedGravitySimplicityDensity field = 0 := by
  unfold generatedGravitySimplicityDensity
    gravitySimplicityMultiplierPairing
    generatedGravitySimplicityResidual
  rw [simplicity]
  simp

/-! ## Coframe response is equal for the explicit multiplier pair -/

theorem coframeLocalInnerStressCovector_eq_coreFDeriv_of_zeroSimplicityResponse
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (simplicityResponseZero :
      fderiv ℝ
          (fun candidate : LorentzianCoframe =>
            generatedGravitySimplicityDensity (withCoframe field candidate))
          field.coframe = 0) :
    coframeLocalInnerStressCovector source point field =
      fderiv ℝ
        (fun candidate : LorentzianCoframe =>
          generatedUnifiedLocalDensityCoreAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (withCoframe field candidate))
        field.coframe := by
  have simplicityDifferentiableAt : DifferentiableAt ℝ
      (fun candidate : LorentzianCoframe =>
        generatedGravitySimplicityDensity (withCoframe field candidate))
      field.coframe :=
    (generatedGravitySimplicityDensity_withCoframe_contDiff field).contDiffAt
      |>.differentiableAt (by simp)
  have simplicityDerivative := simplicityDifferentiableAt.hasFDerivAt
  rw [simplicityResponseZero] at simplicityDerivative
  have coreDerivative : HasFDerivAt (𝕜 := ℝ)
      (fun candidate : LorentzianCoframe =>
        generatedUnifiedLocalDensityCoreAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (withCoframe field candidate))
      (fderiv ℝ
        (fun candidate : LorentzianCoframe =>
          generatedUnifiedLocalDensityCoreAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (withCoframe field candidate)) field.coframe)
      field.coframe :=
    ((generatedUnifiedLocalDensityCore_withCoframe_contDiffAt
      source point field nondegenerate).differentiableAt (by simp)).hasFDerivAt
  have combinedDerivative := simplicityDerivative.add coreDerivative
  have derivativeEquality :=
    (coframeLocalInnerDensity_hasFDerivAt source point field
      nondegenerate).unique combinedDerivative
  exact derivativeEquality.trans (zero_add _)

theorem coframeLocalInnerStressCovector_coordinate_eq_zero_of_simplicity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (simplicity : field.gravityAuxiliary =
      physicalIIPlusBivector field.coframe) :
    coframeLocalInnerStressCovector source point
        (withGravitySimplicityMultiplier field
          (physicalBivectorCoordinateDirection 0 0)) =
      coframeLocalInnerStressCovector source point
        (withGravitySimplicityMultiplier field 0) := by
  rw [coframeLocalInnerStressCovector_eq_coreFDeriv_of_zeroSimplicityResponse
      source point
        (withGravitySimplicityMultiplier field
          (physicalBivectorCoordinateDirection 0 0))
        nondegenerate
        (coordinateMultiplier_withCoframe_fderiv_eq_zero_of_simplicity
          field simplicity),
    coframeLocalInnerStressCovector_eq_coreFDeriv_of_zeroSimplicityResponse
      source point (withGravitySimplicityMultiplier field 0)
        nondegenerate (zeroMultiplier_withCoframe_fderiv_eq_zero field)]
  rfl

theorem coframeLocalInnerDensity_withMultiplier_eq_of_simplicity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (simplicity : field.gravityAuxiliary =
      physicalIIPlusBivector field.coframe)
    (multiplier : PhysicalBivector) :
    coframeLocalInnerDensity source point
        (withGravitySimplicityMultiplier field multiplier)
        (withGravitySimplicityMultiplier field multiplier).coframe =
      coframeLocalInnerDensity source point field field.coframe := by
  unfold coframeLocalInnerDensity
  rw [generatedGravitySimplicityDensity_eq_zero_of_simplicity
      (withCoframe
        (withGravitySimplicityMultiplier field multiplier)
        (withGravitySimplicityMultiplier field multiplier).coframe)
      (by exact simplicity),
    generatedGravitySimplicityDensity_eq_zero_of_simplicity
      (withCoframe field field.coframe) (by exact simplicity)]
  rfl

/-- The actual coframe Euler--Lagrange covector cannot distinguish the two
explicit multiplier fields on the nondegenerate simplicity shell. -/
theorem coframeLocalStressCovector_coordinate_eq_zero_of_simplicity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (simplicity : field.gravityAuxiliary =
      physicalIIPlusBivector field.coframe) :
    coframeLocalStressCovector source point
        (withGravitySimplicityMultiplier field
          (physicalBivectorCoordinateDirection 0 0)) =
      coframeLocalStressCovector source point
        (withGravitySimplicityMultiplier field 0) := by
  let coordinate := withGravitySimplicityMultiplier field
    (physicalBivectorCoordinateDirection 0 0)
  let zero := withGravitySimplicityMultiplier field 0
  rw [coframeLocalStressCovector_product_rule source point coordinate
      nondegenerate,
    coframeLocalStressCovector_product_rule source point zero nondegenerate]
  have innerStressEquality :=
    coframeLocalInnerStressCovector_coordinate_eq_zero_of_simplicity
      source point field nondegenerate simplicity
  have coordinateDensity :=
    coframeLocalInnerDensity_withMultiplier_eq_of_simplicity
      source point field simplicity
        (physicalBivectorCoordinateDirection 0 0)
  have zeroDensity :=
    coframeLocalInnerDensity_withMultiplier_eq_of_simplicity
      source point field simplicity 0
  change generatedVolumeDensity coordinate •
        coframeLocalInnerStressCovector source point coordinate +
      coframeLocalInnerDensity source point coordinate coordinate.coframe •
        coframeVolumeStressCovector coordinate =
    generatedVolumeDensity zero •
        coframeLocalInnerStressCovector source point zero +
      coframeLocalInnerDensity source point zero zero.coframe •
        coframeVolumeStressCovector zero
  rw [innerStressEquality, coordinateDensity, zeroDensity]
  rfl

/-! ## Complete joint-residual noninjectivity -/

@[simp] theorem toContinuumPointField_installGravityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (multiplier : SmoothGravityMultiplierField)
    (point : BasePoint) :
    toContinuumPointField
        (installGravityMultiplier configuration multiplier) point =
      withGravitySimplicityMultiplier
        (toContinuumPointField configuration point) (multiplier point) :=
  rfl

/-- The complete nine-channel pointwise readout identifies the two distinct
explicit multiplier completions. -/
theorem currentPointwiseJointShellResidual_coordinate_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (simplicity : GravitySimplicityEquation configuration)
    (point : BasePoint) :
    currentPointwiseJointShellResidual source
        (installGravityMultiplier configuration
          coordinateSmoothGravityMultiplierField) point =
      currentPointwiseJointShellResidual source
        (installGravityMultiplier configuration
          zeroSmoothGravityMultiplierField) point := by
  apply CurrentPointwiseJointShellResidualCarrier.ext
  · apply CurrentPointwiseAlgebraicResidualCarrier.ext <;> rfl
  · apply CurrentPointwiseEulerLagrangeResidualCarrier.ext
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact coframeLocalStressCovector_coordinate_eq_zero_of_simplicity
        source point (toContinuumPointField configuration point)
          (nondegenerate point) (simplicity point)

theorem currentJointShellResidualSection_coordinate_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (simplicity : GravitySimplicityEquation configuration) :
    currentJointShellResidualSection source
        (installGravityMultiplier configuration
          coordinateSmoothGravityMultiplierField) =
      currentJointShellResidualSection source
        (installGravityMultiplier configuration
          zeroSmoothGravityMultiplierField) := by
  funext point
  exact currentPointwiseJointShellResidual_coordinate_eq_zero
    source configuration nondegenerate simplicity point

/-- The explicit pair is null only for the current first-residual readout.
The already defined quadratic auxiliary response separates the same two
backgrounds, so first-residual noninjectivity is not a license to quotient
the multiplier before the fluctuation/observable jurisdiction is proved. -/
theorem jointResidual_eq_but_auxiliarySecondResponse_ne
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (simplicity : GravitySimplicityEquation configuration) :
    currentJointShellResidualSection source
        (installGravityMultiplier configuration
          coordinateSmoothGravityMultiplierField) =
        currentJointShellResidualSection source
          (installGravityMultiplier configuration
            zeroSmoothGravityMultiplierField) ∧
      gravityAuxiliarySimplicitySecondVariationDensity
          (withGravitySimplicityMultiplier
            (toContinuumPointField configuration 0)
            (physicalBivectorCoordinateDirection 0 0))
          (physicalBivectorCoordinateDirection 0 0) ≠
        gravityAuxiliarySimplicitySecondVariationDensity
          (withGravitySimplicityMultiplier
            (toContinuumPointField configuration 0) 0)
          (physicalBivectorCoordinateDirection 0 0) := by
  refine ⟨currentJointShellResidualSection_coordinate_eq_zero source
    configuration nondegenerate simplicity, ?_⟩
  simp

/-- Typed no-free-parameter gate: the full joint residual readout is not
injective on the explicit smooth multiplier class. -/
theorem jointResidual_multiplierCompletion_not_injective
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (simplicity : GravitySimplicityEquation configuration) :
    ¬ Function.Injective (fun multiplier : SmoothGravityMultiplierField =>
      currentJointShellResidualSection source
        (installGravityMultiplier configuration multiplier)) := by
  intro injective
  apply zeroSmoothGravityMultiplierField_ne_coordinate
  apply injective
  exact (currentJointShellResidualSection_coordinate_eq_zero source
    configuration nondegenerate simplicity).symm

/-! ## Source-partial carrier specialization -/

/-- A full configuration extends exactly the six primitive fields generated
by the given proof-free source.  The multiplier, matter, and conjugate-matter
fields remain visible and unconstrained. -/
structure ExtendsSourcePartialPrimitiveCarrier
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop where
  coframe : configuration.coframe =
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).coframe
  gravityConnection : configuration.gravityConnection =
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).gravityConnection
  gravityAuxiliary : configuration.gravityAuxiliary =
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).gravityAuxiliary
  gaugeConnection : configuration.gaugeConnection =
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).gaugeConnection
  gaugeAuxiliary : configuration.gaugeAuxiliary =
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).gaugeAuxiliary
  scalar : configuration.scalar =
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).scalar

theorem extendsSourcePartialPrimitiveCarrier_implies_simplicity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (extension : ExtendsSourcePartialPrimitiveCarrier source configuration) :
    GravitySimplicityEquation configuration := by
  intro point
  rw [extension.gravityAuxiliary, extension.coframe]
  rfl

/-- Source-facing response-null no-go: even after fixing all six fields the
current proof-free source genuinely produces, the complete residual readout
cannot select a unique smooth multiplier completion. -/
theorem sourcePartial_jointResidual_multiplierCompletion_not_injective
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (extension : ExtendsSourcePartialPrimitiveCarrier source configuration)
    (nondegenerate : configuration.Nondegenerate) :
    ¬ Function.Injective (fun multiplier : SmoothGravityMultiplierField =>
      currentJointShellResidualSection source
        (installGravityMultiplier configuration multiplier)) :=
  jointResidual_multiplierCompletion_not_injective source configuration
    nondegenerate
    (extendsSourcePartialPrimitiveCarrier_implies_simplicity
      source configuration extension)

end

end SaturationMonoid.PhysicsCore.StageNineGravityMultiplierResidualNoninjectivity
