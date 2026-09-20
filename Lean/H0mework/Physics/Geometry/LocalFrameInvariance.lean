import H0mework.Physics.Exterior.GlobalIntegratedAction
import H0mework.Physics.Dirac.SpinMatterBundle

namespace SaturationMonoid.PhysicsCore.StageNineLocalFrameInvariance

open StageNineGlobalIntegratedAction
open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle
open StageNineSpinMatterBundle
open StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation
open DiracExteriorMatterAction
open SU7MotherLieAlgebra
open SU7ExteriorMatterGaugeCovariantJet
open EmpiricalReferenceScaleCouplingBoundary

noncomputable section

abbrev LocalTotalFrame := TotalStructureGroup
abbrev LocalTotalFrameSection := BasePoint → LocalTotalFrame

/-- Tensorial P286 coordinates are carried relative to the moving mother
frame.  This is their actual raw SU(7)-mother representative. -/
def rawMotherTwoForm
    (frame : SU7MotherGroup)
    (relative : Fin 6 → P286LieBlockData) :
    Fin 6 → SU7MotherLieMatrix :=
  fun pair => motherGaugeConjugate frame (p286LieBlockEmbed (relative pair))

theorem motherGaugeConjugate_mul
    (first second : SU7MotherGroup) (matrix : SU7MotherLieMatrix) :
    motherGaugeConjugate (first * second) matrix =
      motherGaugeConjugate first (motherGaugeConjugate second matrix) := by
  apply Subtype.ext
  change
    ((first : Matrix SU7MotherIndex SU7MotherIndex ℂ) * second) * matrix *
        star ((first : Matrix SU7MotherIndex SU7MotherIndex ℂ) * second) =
      (first : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        ((second : Matrix SU7MotherIndex SU7MotherIndex ℂ) * matrix *
          star (second : Matrix SU7MotherIndex SU7MotherIndex ℂ)) *
        star (first : Matrix SU7MotherIndex SU7MotherIndex ℂ)
  rw [star_mul]
  noncomm_ring

theorem rawMotherTwoForm_localGauge_covariant
    (gauge frame : SU7MotherGroup)
    (relative : Fin 6 → P286LieBlockData) :
    rawMotherTwoForm (gauge * frame) relative =
      fun pair => motherGaugeConjugate gauge
        (rawMotherTwoForm frame relative pair) := by
  funext pair
  exact motherGaugeConjugate_mul gauge frame
    (p286LieBlockEmbed (relative pair))

/-- Raw scalar/matter representatives transform; the gravity and P286
two-form coordinates remain moving-frame-relative fiber coordinates. -/
def transformContinuumPointField
    (change : LocalTotalFrame)
    (field : StageNineContinuumPointField) :
    StageNineContinuumPointField where
  coframe := field.coframe
  gravityCurvature := field.gravityCurvature
  gravityAuxiliary := field.gravityAuxiliary
  gravitySimplicityMultiplier := field.gravitySimplicityMultiplier
  gaugeCurvature := field.gaugeCurvature
  gaugeAuxiliary := field.gaugeAuxiliary
  scalar := scalarCoordinateAction change.2 field.scalar
  scalarCovariantDerivative := fun direction =>
    scalarCoordinateAction change.2
      (field.scalarCovariantDerivative direction)
  matter := totalDiracExteriorMatterRepresentation change field.matter
  matterCovariantDerivative := fun direction =>
    totalDiracExteriorMatterRepresentation change
      (field.matterCovariantDerivative direction)
  conjugateMatter := field.conjugateMatter.comp
    (totalDiracExteriorMatterRepresentation change⁻¹)

/-- Remove an arbitrary local Spin×SU(7) choice of frame before feeding the
source-generated chart density. -/
def reduceContinuumPointField
    (frame : LocalTotalFrame)
    (field : StageNineContinuumPointField) :
    StageNineContinuumPointField where
  coframe := field.coframe
  gravityCurvature := field.gravityCurvature
  gravityAuxiliary := field.gravityAuxiliary
  gravitySimplicityMultiplier := field.gravitySimplicityMultiplier
  gaugeCurvature := field.gaugeCurvature
  gaugeAuxiliary := field.gaugeAuxiliary
  scalar := scalarCoordinateAction frame.2⁻¹ field.scalar
  scalarCovariantDerivative := fun direction =>
    scalarCoordinateAction frame.2⁻¹
      (field.scalarCovariantDerivative direction)
  matter := totalDiracExteriorMatterRepresentation frame⁻¹ field.matter
  matterCovariantDerivative := fun direction =>
    totalDiracExteriorMatterRepresentation frame⁻¹
      (field.matterCovariantDerivative direction)
  conjugateMatter := field.conjugateMatter.comp
    (totalDiracExteriorMatterRepresentation frame)

theorem scalarFrameReduction_mul
    (change frame : LocalTotalFrame)
    (scalar : ScalarCoordinateCarrier) :
    scalarCoordinateAction (change * frame).2⁻¹
        (scalarCoordinateAction change.2 scalar) =
      scalarCoordinateAction frame.2⁻¹ scalar := by
  change scalarCoordinateAction (change.2 * frame.2)⁻¹
      (scalarCoordinateAction change.2 scalar) =
    scalarCoordinateAction frame.2⁻¹ scalar
  rw [mul_inv_rev, ← scalarCoordinateAction_mul]
  simp

theorem matterFrameReduction_mul
    (change frame : LocalTotalFrame)
    (matter : DiracExteriorMatterCarrier) :
    totalDiracExteriorMatterRepresentation (change * frame)⁻¹
        (totalDiracExteriorMatterRepresentation change matter) =
      totalDiracExteriorMatterRepresentation frame⁻¹ matter := by
  rw [mul_inv_rev, ← Module.End.mul_apply, ← map_mul]
  simp

theorem dualFrameReduction_mul
    (change frame : LocalTotalFrame)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (dual.comp (totalDiracExteriorMatterRepresentation change⁻¹)).comp
        (totalDiracExteriorMatterRepresentation (change * frame)) =
      dual.comp (totalDiracExteriorMatterRepresentation frame) := by
  apply LinearMap.ext
  intro matter
  simp only [LinearMap.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul]
  simp

theorem reduce_transform_mul
    (change frame : LocalTotalFrame)
    (field : StageNineContinuumPointField) :
    reduceContinuumPointField (change * frame)
        (transformContinuumPointField change field) =
      reduceContinuumPointField frame field := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact scalarFrameReduction_mul change frame field.scalar
  · funext direction
    exact scalarFrameReduction_mul change frame
      (field.scalarCovariantDerivative direction)
  · exact matterFrameReduction_mul change frame field.matter
  · funext direction
    exact matterFrameReduction_mul change frame
      (field.matterCovariantDerivative direction)
  · exact dualFrameReduction_mul change frame field.conjugateMatter

@[simp] theorem reduceContinuumPointField_one
    (field : StageNineContinuumPointField) :
    reduceContinuumPointField 1 field = field := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [reduceContinuumPointField]
  · funext direction
    simp [reduceContinuumPointField]
  · simp [reduceContinuumPointField]
  · funext direction
    simp [reduceContinuumPointField]
  · apply LinearMap.ext
    intro matter
    simp [reduceContinuumPointField]

def generatedUnifiedLocalDensityInFrameAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (frame : LocalTotalFrame)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedUnifiedLocalDensityAtBoundary source boundary chart point
    (reduceContinuumPointField frame field)

theorem generatedUnifiedLocalDensityInFrame_localInvariant
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (change frame : LocalTotalFrame)
    (field : StageNineContinuumPointField) :
    generatedUnifiedLocalDensityInFrameAtBoundary source boundary chart point
        (change * frame) (transformContinuumPointField change field) =
      generatedUnifiedLocalDensityInFrameAtBoundary source boundary chart point
        frame field := by
  rw [generatedUnifiedLocalDensityInFrameAtBoundary,
    generatedUnifiedLocalDensityInFrameAtBoundary,
    reduce_transform_mul]

def transformContinuumFieldSection
    (change : LocalTotalFrameSection)
    (field : StageNineContinuumFieldSection) :
    StageNineContinuumFieldSection :=
  fun point => transformContinuumPointField (change point) (field point)

def multiplyLocalFrameSections
    (change frame : LocalTotalFrameSection) : LocalTotalFrameSection :=
  fun point => change point * frame point

def integratedUnifiedActionInFrameAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (frame : LocalTotalFrameSection)
    (field : StageNineContinuumFieldSection) : ℝ :=
  ∫ point : BasePoint,
    generatedUnifiedLocalDensityInFrameAtBoundary source boundary chart point
      (frame point) (field point)

theorem integratedUnifiedActionInFrame_localInvariant
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (change frame : LocalTotalFrameSection)
    (field : StageNineContinuumFieldSection) :
    integratedUnifiedActionInFrameAtBoundary source boundary chart
        (multiplyLocalFrameSections change frame)
        (transformContinuumFieldSection change field) =
      integratedUnifiedActionInFrameAtBoundary source boundary chart
        frame field := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  exact generatedUnifiedLocalDensityInFrame_localInvariant
    source boundary chart point (change point) (frame point) (field point)

def sourceGeneratedIntegratedUnifiedActionInFrame
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (frame : LocalTotalFrameSection)
    (field : StageNineContinuumFieldSection) : ℝ :=
  integratedUnifiedActionInFrameAtBoundary source
    (sourceGeneratedUnifiedCouplings source) chart frame field

theorem sourceGeneratedIntegratedUnifiedActionInFrame_localInvariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (change frame : LocalTotalFrameSection)
    (field : StageNineContinuumFieldSection) :
    sourceGeneratedIntegratedUnifiedActionInFrame source chart
        (multiplyLocalFrameSections change frame)
        (transformContinuumFieldSection change field) =
      sourceGeneratedIntegratedUnifiedActionInFrame source chart frame field :=
  integratedUnifiedActionInFrame_localInvariant source
    (sourceGeneratedUnifiedCouplings source) chart change frame field

def identityLocalTotalFrameSection : LocalTotalFrameSection := fun _ => 1

theorem sourceGeneratedIntegratedUnifiedAction_identityFrame
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    sourceGeneratedIntegratedUnifiedActionInFrame source chart
        identityLocalTotalFrameSection field =
      sourceGeneratedIntegratedUnifiedAction source chart field := by
  unfold sourceGeneratedIntegratedUnifiedActionInFrame
  unfold integratedUnifiedActionInFrameAtBoundary
  unfold sourceGeneratedIntegratedUnifiedAction
  unfold integratedUnifiedActionAtBoundary
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  rw [generatedUnifiedLocalDensityInFrameAtBoundary]
  simp [identityLocalTotalFrameSection]

/-- Negative regression inherited from the actual Spin representation: an
identity local-spin action cannot replace the generated one. -/
theorem handFilledIdentitySpinFrameAction_rejected :
    StageNineSpinMatterBundle.trivialSpinMatrixAction ≠
      StageNineSpinMatterBundle.spinDiracMatrix :=
  StageNineSpinMatterBundle.trivialSpinMatrixAction_rejected

end

end SaturationMonoid.PhysicsCore.StageNineLocalFrameInvariance
