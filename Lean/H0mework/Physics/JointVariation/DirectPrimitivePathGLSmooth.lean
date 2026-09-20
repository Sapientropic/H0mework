import H0mework.Physics.ConstrainedCauchy.FixedJointDirectPrimitivePathGLCoframe
import H0mework.Physics.Source.RadialCurveIntegralSmoothRegularity

/-!
# Smoothness of the GL direct primitive-path writer

This module isolates the structural regularity of the existing
source/current-only GL writer.  Smooth material-stage jet families generate
smooth radial primitives, the matrix-exponential retraction generates the GL
coframe, and the output's remaining fields are retained from the exact input
stage.  No target, endpoint, equation, or completed output certificate enters
the writer.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeCompleteJointDirectPrimitivePathGLSmooth

open ProofFreeRicherAnholonomicSource
open StageNineCoframeHolonomicMatrixExponentialRealization
open StageNineCoframeMatrixExponentialRetraction
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePath
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePathGLCoframe
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineRadialCurveIntegralFirstJet
open StageNineRadialCurveIntegralSmoothRegularity
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

local instance glSmoothP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance glSmoothP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

private theorem const_matrix_mul_contDiff
    (base : LorentzianCoframe)
    (field : BasePoint → LorentzianCoframe)
    (regular : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (fun point => base * field point) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  rw [show (fun point => (base * field point) row column) =
    fun point => ∑ middle : LorentzianIndex,
      base row middle * field point middle column by
    funext point
    rw [Matrix.mul_apply]]
  exact ContDiff.sum fun middle _ =>
    contDiff_const.mul
      (contDiff_pi.mp (contDiff_pi.mp regular middle) column)

private theorem coframeMatrixExponentialRetraction_comp_contDiff
    (base : LorentzianCoframe)
    (increment : BasePoint → LorentzianCoframe)
    (regular : ContDiff ℝ ∞ increment) :
    ContDiff ℝ ∞ (fun point =>
      coframeMatrixExponentialRetraction base (increment point)) := by
  unfold coframeMatrixExponentialRetraction
  have inverseIncrementSmooth : ContDiff ℝ ∞
      (fun point => base⁻¹ * increment point) :=
    const_matrix_mul_contDiff base⁻¹ increment regular
  have exponentialSmooth : ContDiff ℝ ∞
      (fun point => coframeMatrixExponential (base⁻¹ * increment point)) :=
    coframeMatrixExponential_contDiff.comp inverseIncrementSmooth
  exact const_matrix_mul_contDiff base
    (fun point => coframeMatrixExponential (base⁻¹ * increment point))
    exponentialSmooth

private theorem directPrimitivePathCoframeRadialIncrement_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ ∞ (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate)) :
    ContDiff ℝ ∞
      (directPrimitivePathCoframeRadialIncrement source sectionInput) := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  simpa only [directPrimitivePathCoframeRadialIncrement] using
    radialCurveIntegral_contDiff_infty_of_contDiff
      (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate)
      (regular internal coordinate)

private theorem directPrimitivePathGLCoframeField_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ ∞ (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate)) :
    ContDiff ℝ ∞
      (directPrimitivePathGLCoframeField source sectionInput) :=
  coframeMatrixExponentialRetraction_comp_contDiff
    (sectionInput.coframe 0)
    (directPrimitivePathCoframeRadialIncrement source sectionInput)
    (directPrimitivePathCoframeRadialIncrement_contDiff
      source sectionInput regular)

private theorem directPrimitivePathLorentzRadialIncrement_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular : ContDiff ℝ ∞
      (directPrimitivePathLorentzJetCLM source sectionInput)) :
    ContDiff ℝ ∞
      (directPrimitivePathLorentzRadialIncrement source sectionInput) := by
  rw [show directPrimitivePathLorentzRadialIncrement source sectionInput =
    fun endpoint => ∫ᶜ contact in Path.segment (0 : BasePoint) endpoint,
      directPrimitivePathLorentzJetCLM source sectionInput contact by
    funext endpoint
    rfl]
  exact radialCurveIntegral_contDiff_infty_of_contDiff
    (directPrimitivePathLorentzJetCLM source sectionInput) regular

private theorem directPrimitivePathConnectionField_component_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular : ContDiff ℝ ∞
      (directPrimitivePathLorentzJetCLM source sectionInput))
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      directPrimitivePathConnectionField source sectionInput point
        formDirection internalOut internalIn) := by
  have incrementSmooth := directPrimitivePathLorentzRadialIncrement_contDiff
    source sectionInput regular
  have liftedSmooth : ContDiff ℝ ∞ (fun point =>
      radialLorentzConnectionLiftCLM
        (directPrimitivePathLorentzRadialIncrement
          source sectionInput point)) :=
    radialLorentzConnectionLiftCLM.contDiff.comp incrementSmooth
  have coordinateSmooth : ContDiff ℝ ∞ (fun point =>
      radialLorentzConnectionCoordinateCLM
        formDirection internalOut internalIn
        (radialLorentzConnectionLiftCLM
          (directPrimitivePathLorentzRadialIncrement
            source sectionInput point))) :=
    (radialLorentzConnectionCoordinateCLM
      formDirection internalOut internalIn).contDiff.comp liftedSmooth
  change ContDiff ℝ ∞ (fun point =>
    sectionInput.gravityConnection 0 formDirection internalOut internalIn +
      radialLorentzConnectionCoordinateCLM
        formDirection internalOut internalIn
        (radialLorentzConnectionLiftCLM
          (directPrimitivePathLorentzRadialIncrement
            source sectionInput point)))
  exact contDiff_const.add coordinateSmooth

/-- The exact source/input writer is smooth once its two generated jet
families and precisely the retained source fields are smooth. -/
theorem
    sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_smooth_of_materialRegularity
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (multiplierSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ (fun point =>
        sectionInput.gravitySimplicityMultiplier point
          internalPair spacetimePair))
    (gaugeConnectionSmooth : ∀ direction,
      ContDiff ℝ ∞ (fun point =>
        p286CoordinateEquiv (sectionInput.gaugeConnection point direction)))
    (gaugeAuxiliarySmooth : ∀ pair,
      ContDiff ℝ ∞ (fun point =>
        p286CoordinateEquiv (sectionInput.gaugeAuxiliary point pair)))
    (scalarSmooth : ContDiff ℝ ∞ sectionInput.scalar)
    (matterSmooth : ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv (sectionInput.matter point)))
    (conjugateMatterSmooth : ∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞ (fun point =>
        sectionInput.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index 1))))
    (coframeJetRegular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ ∞ (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate))
    (lorentzJetRegular : ContDiff ℝ ∞
      (directPrimitivePathLorentzJetCLM source sectionInput)) :
    (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
      source sectionInput).Smooth := by
  have coframeSmooth := directPrimitivePathGLCoframeField_contDiff
    source sectionInput coframeJetRegular
  have auxiliarySmooth : ContDiff ℝ ∞ (fun point =>
      physicalIIPlusBivector
        (directPrimitivePathGLCoframeField source sectionInput point)) :=
    physicalIIPlusBivector_contDiff.comp coframeSmooth
  refine ⟨?_, ?_, ?_, multiplierSmooth, gaugeConnectionSmooth,
    gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
    conjugateMatterSmooth⟩
  · intro row column
    exact contDiff_pi.mp (contDiff_pi.mp coframeSmooth row) column
  · exact directPrimitivePathConnectionField_component_contDiff
      source sectionInput lorentzJetRegular
  · intro internalPair spacetimePair
    exact contDiff_pi.mp (contDiff_pi.mp auxiliarySmooth internalPair)
      spacetimePair

/-- Aggregate source-stage mouth for consumers that already carry whole
input smoothness.  The writer still stores none of this evidence. -/
theorem sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_smooth
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (sectionInputSmooth : sectionInput.Smooth)
    (coframeJetRegular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ ∞ (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate))
    (lorentzJetRegular : ContDiff ℝ ∞
      (directPrimitivePathLorentzJetCLM source sectionInput)) :
    (sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite
      source sectionInput).Smooth :=
  sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_smooth_of_materialRegularity
    source sectionInput sectionInputSmooth.2.2.2.1
    sectionInputSmooth.2.2.2.2.1 sectionInputSmooth.2.2.2.2.2.1
    sectionInputSmooth.2.2.2.2.2.2.1
    sectionInputSmooth.2.2.2.2.2.2.2.1
    sectionInputSmooth.2.2.2.2.2.2.2.2 coframeJetRegular
    lorentzJetRegular

#print axioms
  sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_smooth_of_materialRegularity
#print axioms sourceActionGeneratedDiracDualGLDirectPrimitivePathWrite_smooth

end
end StageNineDiracDualFormNativeCompleteJointDirectPrimitivePathGLSmooth
end PhysicsCore
end SaturationMonoid
