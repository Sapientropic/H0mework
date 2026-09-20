import H0mework.Physics.Cauchy.CanonicalCauchyCoordinateProjection
import H0mework.Physics.ConstitutiveAction.ResponseOperator
import H0mework.Physics.FixedJoint.FixedConstitutiveSuccessor

/-!
# Spatial-section lift of the constitutive joint action operator

The canonical-contact operator is already generated from `(source,current)`,
but its normalized-affine gravity write is centered at one contact.  This
module applies that same action-owned operator to the current translated to
each canonical spatial contact, then reads every generated germ on its local
physical-time axis:

```text
source + one four-dimensional current
  -> translate the current to each canonical spatial contact
  -> run the same constitutive joint action operator at that contact
  -> evaluate the generated germ on its local time axis
  -> one explicit four-dimensional holonomic section.
```

This is one direct global formula, not an atlas or a supplied gluing
certificate.  No residual, residual coordinate, support, sign, branch,
target field, equation witness, or zero-fiber receipt enters the constructor.
Residual substitution belongs strictly downstream.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false

/-! ## Canonical spatial recentering -/

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- Translate a local base point so that its origin is the selected point of
the canonical time-zero slice.  The translation is fixed by the canonical
`3+1` split and carries no source parameter. -/
def canonicalSpatialContactTranslation
    (space : StageNineSpatialPoint)
    (point : BasePoint) : BasePoint :=
  canonicalCauchySlicePoint 0 space + point

@[simp] theorem canonicalSpatialContactTranslation_timeAxis
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    canonicalSpatialContactTranslation space
        (canonicalCauchySlicePoint time 0) =
      canonicalCauchySlicePoint time space := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalSpatialContactTranslation, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three, add_comm]

@[simp] theorem canonicalSpatialContactTranslation_zero
    (point : BasePoint) :
    canonicalSpatialContactTranslation 0 point = point := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalSpatialContactTranslation, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-- Pull one holonomic current back to the selected canonical spatial
contact.  All nine primitive fields use the same translation. -/
def spatiallyRecenterHolonomicConfiguration
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration where
  coframe := fun point =>
    current.coframe (canonicalSpatialContactTranslation space point)
  gravityConnection := fun point =>
    current.gravityConnection
      (canonicalSpatialContactTranslation space point)
  gravityAuxiliary := fun point =>
    current.gravityAuxiliary
      (canonicalSpatialContactTranslation space point)
  gravitySimplicityMultiplier := fun point =>
    current.gravitySimplicityMultiplier
      (canonicalSpatialContactTranslation space point)
  gaugeConnection := fun point =>
    current.gaugeConnection (canonicalSpatialContactTranslation space point)
  gaugeAuxiliary := fun point =>
    current.gaugeAuxiliary (canonicalSpatialContactTranslation space point)
  scalar := fun point =>
    current.scalar (canonicalSpatialContactTranslation space point)
  matter := fun point =>
    current.matter (canonicalSpatialContactTranslation space point)
  conjugateMatter := fun point =>
    current.conjugateMatter
      (canonicalSpatialContactTranslation space point)

@[simp] theorem spatiallyRecenterHolonomicConfiguration_zero
    (current : StageNineHolonomicConfiguration) :
    spatiallyRecenterHolonomicConfiguration current 0 = current := by
  apply StageNineHolonomicConfiguration.ext <;>
    simp [spatiallyRecenterHolonomicConfiguration]

/-! ## One explicit global section -/

/-- Assemble a spatial family of already generated local actuals by reading
each member only on its own canonical physical-time axis. -/
def spatialContactTimeAxisDiagonal
    (family : StageNineSpatialPoint → StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration where
  coframe := fun point =>
    (family (canonicalSpatialProjection point)).coframe
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  gravityConnection := fun point =>
    (family (canonicalSpatialProjection point)).gravityConnection
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  gravityAuxiliary := fun point =>
    (family (canonicalSpatialProjection point)).gravityAuxiliary
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  gravitySimplicityMultiplier := fun point =>
    (family (canonicalSpatialProjection point)).gravitySimplicityMultiplier
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  gaugeConnection := fun point =>
    (family (canonicalSpatialProjection point)).gaugeConnection
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  gaugeAuxiliary := fun point =>
    (family (canonicalSpatialProjection point)).gaugeAuxiliary
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  scalar := fun point =>
    (family (canonicalSpatialProjection point)).scalar
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  matter := fun point =>
    (family (canonicalSpatialProjection point)).matter
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)
  conjugateMatter := fun point =>
    (family (canonicalSpatialProjection point)).conjugateMatter
      (canonicalCauchySlicePoint (canonicalTimeProjection point) 0)

/-- Section-level constitutive joint action producer.  The operator is
recomputed from the translated live current at every spatial contact before
the single global section is assembled. -/
def diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  spatialContactTimeAxisDiagonal fun space =>
    diracDualFormNativeConstitutiveJointActionResponseOperator source
      (spatiallyRecenterHolonomicConfiguration current space)

macro "section_field_slice" : tactic =>
  `(tactic|
    simp [diracDualFormNativeConstitutiveJointActionSpatialSectionOperator,
      spatialContactTimeAxisDiagonal])

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).coframe (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)).coframe
          (canonicalCauchySlicePoint time 0) := by
  section_field_slice

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityConnection_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).gravityConnection
          (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)
        ).gravityConnection (canonicalCauchySlicePoint time 0) := by
  section_field_slice

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).gravityAuxiliary
          (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)
        ).gravityAuxiliary (canonicalCauchySlicePoint time 0) := by
  section_field_slice

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_multiplier_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).gravitySimplicityMultiplier
          (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)
        ).gravitySimplicityMultiplier
          (canonicalCauchySlicePoint time 0) := by
  section_field_slice

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeConnection_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).gaugeConnection
          (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)
        ).gaugeConnection (canonicalCauchySlicePoint time 0) := by
  section_field_slice

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).gaugeAuxiliary
          (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)
        ).gaugeAuxiliary (canonicalCauchySlicePoint time 0) := by
  section_field_slice

/-- At every canonical spatial contact the active P286 auxiliary is read
from the same live-coframe/live-curvature constitutive action inverse. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice_actionWrite
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).gaugeAuxiliary
          (canonicalCauchySlicePoint time space) =
      diracDualFormNativeConstitutiveAuxiliaryField source
        (spatiallyRecenterHolonomicConfiguration current space)
        (canonicalCauchySlicePoint time 0) := by
  rw [
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice,
    diracDualFormNativeConstitutiveJointActionResponseOperator_gaugeAuxiliary]

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_scalar_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).scalar (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)).scalar
          (canonicalCauchySlicePoint time 0) := by
  section_field_slice

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_matter_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).matter (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)).matter
          (canonicalCauchySlicePoint time 0) := by
  section_field_slice

@[simp] theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).conjugateMatter
          (canonicalCauchySlicePoint time space) =
      (diracDualFormNativeConstitutiveJointActionResponseOperator source
        (spatiallyRecenterHolonomicConfiguration current space)
        ).conjugateMatter (canonicalCauchySlicePoint time 0) := by
  section_field_slice

/-! ## Global primitive preservation -/

/-- The section lift preserves the complete four-dimensional coframe field.
Only fields written by the downstream action chain can change. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current).coframe =
      current.coframe := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe_slice,
    diracDualFormNativeConstitutiveJointActionResponseOperator_coframe]
  simp [spatiallyRecenterHolonomicConfiguration]

/-- The section lift does not infer a P286 branch from the residual; it
preserves the already action-generated P286 connection verbatim. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current).gaugeConnection =
      current.gaugeConnection := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeConnection_slice,
    diracDualFormNativeConstitutiveJointActionResponseOperator_gaugeConnection]
  simp [spatiallyRecenterHolonomicConfiguration]

/-- The constitutive/Dirac/EC section lift preserves the scalar primitive
globally; no scalar residual is converted into a write. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current).scalar =
      current.scalar := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_scalar_slice,
    diracDualFormNativeConstitutiveJointActionResponseOperator_scalar]
  simp [spatiallyRecenterHolonomicConfiguration]

/-! ## Fixed P506/L0 specialization -/

/-- The next fixed P506/L0 common actual is generated by the section operator
from the same solved current that feeds the canonical-contact successor. -/
def FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
    positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_preservedPrimitives :
    FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.coframe =
        FixedP506FormNativeJointActionSolvedSuccessor.coframe ∧
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.gaugeConnection =
        FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection ∧
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.scalar =
        FixedP506FormNativeJointActionSolvedSuccessor.scalar := by
  exact
    ⟨diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor,
      diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor,
      diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_scalar
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor⟩

/-- At the canonical origin, the section producer reads the very same
action-generated local actual as the earlier canonical-contact producer.
This is value provenance only; derivatives of the assembled section are
recomputed downstream from its explicit global formula. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_origin_values :
    let sectionActual :=
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor
    let contact :=
      FixedP506FormNativeConstitutiveJointActionSuccessor
    sectionActual.coframe 0 = contact.coframe 0 ∧
      sectionActual.gravityConnection 0 = contact.gravityConnection 0 ∧
      sectionActual.gravityAuxiliary 0 = contact.gravityAuxiliary 0 ∧
      sectionActual.gravitySimplicityMultiplier 0 =
        contact.gravitySimplicityMultiplier 0 ∧
      sectionActual.gaugeConnection 0 = contact.gaugeConnection 0 ∧
      sectionActual.gaugeAuxiliary 0 = contact.gaugeAuxiliary 0 ∧
      sectionActual.scalar 0 = contact.scalar 0 ∧
      sectionActual.matter 0 = contact.matter 0 ∧
      sectionActual.conjugateMatter 0 = contact.conjugateMatter 0 := by
  have coframeEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.coframe
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.coframe 0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have gravityConnectionEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.gravityConnection
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.gravityConnection
          0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityConnection_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have gravityAuxiliaryEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.gravityAuxiliary
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.gravityAuxiliary
          0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have multiplierEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.gravitySimplicityMultiplier
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.gravitySimplicityMultiplier
          0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_multiplier_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have gaugeConnectionEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.gaugeConnection
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection
          0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeConnection_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have gaugeAuxiliaryEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.gaugeAuxiliary
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeAuxiliary
          0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have scalarEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.scalar
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.scalar 0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_scalar_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have matterEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.matter
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.matter 0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_matter_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  have conjugateMatterEq :
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor.conjugateMatter
          0 =
        FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter 0 := by
    simpa only [
      FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor,
      canonicalCauchySlicePoint_zero_zero,
      spatiallyRecenterHolonomicConfiguration_zero,
      ←
        fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator]
      using
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0 0)
  exact
    ⟨coframeEq, gravityConnectionEq, gravityAuxiliaryEq, multiplierEq,
      gaugeConnectionEq, gaugeAuxiliaryEq, scalarEq, matterEq,
      conjugateMatterEq⟩

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_exactLineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506FormNativeConstitutiveJointActionSuccessor_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
