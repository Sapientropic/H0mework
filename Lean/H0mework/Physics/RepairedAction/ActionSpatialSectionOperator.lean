import H0mework.Physics.ConstitutiveAction.SpatialSectionOperator
import H0mework.Physics.FixedJoint.FixedRepairedConstitutiveJointActionSuccessor

/-!
# Spatial section of the repaired constitutive joint operator

The same source/current-only repaired operator is recomputed at every
canonical spatial contact and read on that contact's physical-time axis.
This produces one explicit four-dimensional configuration.  Residuals are
not accepted by the constructor and are evaluated only downstream.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506RepairedConstitutiveJointActionSuccessor
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- One global section assembled from the repaired action-owned local
operator. -/
def diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  spatialContactTimeAxisDiagonal fun space =>
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator source
      (spatiallyRecenterHolonomicConfiguration current space)

macro "repaired_section_field_slice" : tactic =>
  `(tactic|
    simp [
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator,
      spatialContactTimeAxisDiagonal])

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).coframe (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).coframe (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityConnection_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gravityConnection
        (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).gravityConnection (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gravityAuxiliary
        (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).gravityAuxiliary (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_multiplier_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gravitySimplicityMultiplier
        (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).gravitySimplicityMultiplier (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gaugeConnection
        (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).gaugeConnection (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gaugeAuxiliary
        (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).gaugeAuxiliary (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).scalar (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).scalar (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_matter_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).matter (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).matter (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

@[simp] theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).conjugateMatter
        (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        source (spatiallyRecenterHolonomicConfiguration current space)
        ).conjugateMatter (canonicalCauchySlicePoint time 0) := by
  repaired_section_field_slice

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).coframe =
      current.coframe := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe_slice,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_coframe]
  simp [spatiallyRecenterHolonomicConfiguration]

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).gaugeConnection =
      current.gaugeConnection := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection_slice,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection]
  simp [spatiallyRecenterHolonomicConfiguration]

theorem
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      source current).scalar =
      current.scalar := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar_slice,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar]
  simp [spatiallyRecenterHolonomicConfiguration]

/-- Fixed P506/L0 four-dimensional repaired successor. -/
def FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
    positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor_exactLineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506FormNativeJointActionSolvedSuccessor_exactLineage

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor_preservedPrimitives :
    FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.coframe =
        FixedP506FormNativeJointActionSolvedSuccessor.coframe ∧
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.gaugeConnection =
        FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection ∧
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.scalar =
        FixedP506FormNativeJointActionSolvedSuccessor.scalar :=
  ⟨diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
      _ _,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
      _ _,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar
      _ _⟩

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- All nine primitive values at the canonical origin come from the same
repaired contact actual.  This theorem deliberately says nothing about
spatial or mixed jets of the assembled section. -/
theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor_origin_values :
    let sectionActual :=
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor
    let contactActual :=
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor
    sectionActual.coframe 0 = contactActual.coframe 0 ∧
      sectionActual.gravityConnection 0 = contactActual.gravityConnection 0 ∧
      sectionActual.gravityAuxiliary 0 = contactActual.gravityAuxiliary 0 ∧
      sectionActual.gravitySimplicityMultiplier 0 =
        contactActual.gravitySimplicityMultiplier 0 ∧
      sectionActual.gaugeConnection 0 = contactActual.gaugeConnection 0 ∧
      sectionActual.gaugeAuxiliary 0 = contactActual.gaugeAuxiliary 0 ∧
      sectionActual.scalar 0 = contactActual.scalar 0 ∧
      sectionActual.matter 0 = contactActual.matter 0 ∧
      sectionActual.conjugateMatter 0 =
        contactActual.conjugateMatter 0 := by
  dsimp only
  have coframe :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.coframe
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.coframe
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have gravityConnection :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.gravityConnection
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.gravityConnection
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityConnection_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have gravityAuxiliary :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.gravityAuxiliary
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.gravityAuxiliary
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have multiplier :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.gravitySimplicityMultiplier
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.gravitySimplicityMultiplier
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_multiplier_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have gaugeConnection :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.gaugeConnection
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.gaugeConnection
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have gaugeAuxiliary :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.gaugeAuxiliary
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.gaugeAuxiliary
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have scalar :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.scalar
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.scalar
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have matter :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.matter
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.matter
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_matter_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have conjugateMatter :
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.conjugateMatter
          0 =
        FixedP506FormNativeRepairedConstitutiveJointActionSuccessor.conjugateMatter
          0 := by
    simpa only [
      FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor,
      FixedP506FormNativeRepairedConstitutiveJointActionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  exact
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, gaugeAuxiliary, scalar, matter, conjugateMatter⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
