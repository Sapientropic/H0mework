import H0mework.Physics.Coframe.CoframeMatrixExponentialRetraction
import H0mework.Physics.ConstrainedCauchy.FixedJointDirectPrimitivePathRadialFirstJet
import H0mework.Physics.ConstrainedCauchy.FixedExponentialJointDirectPrimitivePath

/-!
# GL-valued coframe actualization of the direct primitive path

The direct complete-joint path already generates coframe and Lorentz radial
increments from one source and section input.  This module actualizes the
coframe increment by the canonical matrix-exponential retraction, retains the
existing Lorentz path, and recomputes `II+` from the resulting coframe.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePathGLCoframe

open ProofFreeRicherAnholonomicSource
open StageNineCoframeMatrixExponentialRetraction
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePath
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePathRadialFirstJet
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialCompleteJointDirectPrimitivePath
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineIIPlusRestriction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Generic source/section-input producer -/

/-- Canonical GL-valued actualization of the coframe radial increment emitted
by the direct primitive path. -/
def directPrimitivePathGLCoframeField
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    BasePoint → LorentzianCoframe :=
  fun point =>
    coframeMatrixExponentialRetraction
      (sectionInput.coframe 0)
      (directPrimitivePathCoframeRadialIncrement source sectionInput point)

@[simp] theorem directPrimitivePathGLCoframeField_zero
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    directPrimitivePathGLCoframeField source sectionInput 0 =
      sectionInput.coframe 0 := by
  simp [directPrimitivePathGLCoframeField]

/-- A nondegenerate origin coframe generates a globally nondegenerate
GL-valued radial field. -/
theorem directPrimitivePathGLCoframeField_nondegenerate
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (baseNondegenerate : Matrix.det (sectionInput.coframe 0) ≠ 0) :
    ∀ point, Matrix.det
      (directPrimitivePathGLCoframeField source sectionInput point) ≠ 0 := by
  intro point
  exact coframeMatrixExponentialRetraction_det_ne_zero
    (sectionInput.coframe 0)
    (directPrimitivePathCoframeRadialIncrement source sectionInput point)
    baseNondegenerate

/-- At the origin the GL actualization retains the complete first germ of the
source-generated radial increment. -/
theorem directPrimitivePathGLCoframeField_hasFDerivAt_zero_of_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (baseNondegenerate : Matrix.det (sectionInput.coframe 0) ≠ 0)
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ 1 (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate)) :
    HasFDerivAt
      (directPrimitivePathGLCoframeField source sectionInput)
      (directPrimitivePathCoframeRadialFirstJet source sectionInput 0)
      0 := by
  exact coframeMatrixExponentialRetraction_comp_hasFDerivAt
    (sectionInput.coframe 0) baseNondegenerate
    (directPrimitivePathCoframeRadialIncrement source sectionInput)
    0
    (directPrimitivePathCoframeRadialFirstJet source sectionInput 0)
    (directPrimitivePathCoframeRadialIncrement_hasFDerivAt_of_contDiff
      source sectionInput regular 0)
    (directPrimitivePathCoframeRadialIncrement_zero source sectionInput)

/-- Parallel primitive-path write with GL-valued coframe actualization. -/
def sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  let coframe := directPrimitivePathGLCoframeField source sectionInput
  { sectionInput with
    coframe := coframe
    gravityConnection := directPrimitivePathConnectionField source sectionInput
    gravityAuxiliary := fun point => physicalIIPlusBivector (coframe point) }

@[simp] theorem sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_coframe
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
      source sectionInput).coframe =
      directPrimitivePathGLCoframeField source sectionInput :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_gravityConnection
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
      source sectionInput).gravityConnection =
      directPrimitivePathConnectionField source sectionInput :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
      source sectionInput).gravityAuxiliary =
      fun point => physicalIIPlusBivector
        (directPrimitivePathGLCoframeField source sectionInput point) :=
  rfl

@[simp] theorem sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_matter
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
      source sectionInput).matter = sectionInput.matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_conjugateMatter
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
      source sectionInput).conjugateMatter = sectionInput.conjugateMatter :=
  rfl

theorem sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_nondegenerate
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (baseNondegenerate : Matrix.det (sectionInput.coframe 0) ≠ 0) :
    (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
      source sectionInput).Nondegenerate := by
  exact directPrimitivePathGLCoframeField_nondegenerate
    source sectionInput baseNondegenerate

theorem
    sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_coframe_hasFDerivAt_zero_of_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (baseNondegenerate : Matrix.det (sectionInput.coframe 0) ≠ 0)
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ 1 (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate)) :
    HasFDerivAt
      (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
        source sectionInput).coframe
      (directPrimitivePathCoframeRadialFirstJet source sectionInput 0)
      0 := by
  exact directPrimitivePathGLCoframeField_hasFDerivAt_zero_of_contDiff
    source sectionInput baseNondegenerate regular

/-! ## Fixed P506/L0 exponential-prefix specialization -/

private abbrev FixedSource : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedSectionInput : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialCauchyDirectPrimitivePathPrefix

/-- Fixed P506/L0 GL-valued direct primitive-path output. -/
def fixedP506L0CartanECConstraintExponentialCauchyGLDirectPrimitivePathGlobalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
    FixedSource FixedSectionInput

private theorem fixedP506L0ExponentialPrefix_origin_nondegenerate :
    Matrix.det (FixedSectionInput.coframe 0) ≠ 0 :=
  fixedP506L0CartanECConstraintExponentialCauchyDirectPrimitivePathPrefix_nondegenerate
    0

/-- The fixed output is globally nondegenerate. -/
theorem
    fixedP506L0CartanECConstraintExponentialCauchyGLDirectPrimitivePathGlobalActual_nondegenerate :
    fixedP506L0CartanECConstraintExponentialCauchyGLDirectPrimitivePathGlobalActual.Nondegenerate := by
  exact sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_nondegenerate
    FixedSource FixedSectionInput
    fixedP506L0ExponentialPrefix_origin_nondegenerate

/-- Fixed-source origin first-germ readback of the GL-valued writer. -/
theorem
    fixedP506L0CartanECConstraintExponentialCauchyGLDirectPrimitivePathGlobalActual_coframe_hasFDerivAt_zero_of_contDiff
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ 1 (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          FixedSource FixedSectionInput contact internal coordinate)) :
    HasFDerivAt
      fixedP506L0CartanECConstraintExponentialCauchyGLDirectPrimitivePathGlobalActual.coframe
      (directPrimitivePathCoframeRadialFirstJet
        FixedSource FixedSectionInput 0)
      0 := by
  exact
    sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_coframe_hasFDerivAt_zero_of_contDiff
      FixedSource FixedSectionInput
      fixedP506L0ExponentialPrefix_origin_nondegenerate regular

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePathGLCoframe
