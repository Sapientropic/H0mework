import H0mework.Physics.JointVariation.SectionLorentzPathGlobalOperator
import H0mework.Physics.SynchronizedJoint.FixedGlobalActual

/-!
# Fixed P506/L0 Lorentz path over the smooth synchronized section

This is the fixed-lineage specialization of the four-leg section/synchronized-
gravity/path/live-reaction occurrence.  The connection profile is generated
from exact recenterings of the already emitted smooth and nondegenerate base;
no completed target or residual coordinate is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Base : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual

/-- The unique exact four-leg fixed occurrence. -/
def fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence :
    CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence
      Source Input :=
  sourceActionGeneratedCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence
    Source Input

/-- One source/current-only whole-field path actual. -/
def fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence.finalActual

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual =
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
        Source Input :=
  rfl

@[simp] theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence_before_path :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence.before
        .lorentzPath =
      Base :=
  rfl

/-- Every profile contact is the native Cartan--EC action leg on an exact
recentered occurrence of the same fixed pre-path actual. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileContact_eq_nativeActionWrite
    (contact : BasePoint) :
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileContact
        Source Input contact =
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
        Source
        (fullyRecenterHolonomicConfiguration Base contact)
        0 :=
  rfl

/-- The path starts from the primitive connection emitted by the exact
synchronized-section occurrence. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_connection_zero :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gravityConnection
        0 =
      Base.gravityConnection 0 := by
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gravityConnection,
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField_zero]
  rfl

/-- The path and reaction legs retain the globally generated identity
coframe. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.coframe =
      fun _ => (1 : LorentzianCoframe) := by
  change Base.coframe = _
  exact
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframe_eq_one

/-- The one emitted path actual is nondegenerate everywhere. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_nondegenerate :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.Nondegenerate := by
  intro point
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
  norm_num

/-- The path changes neither the generated coframe nor its computed `II+`
auxiliary. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_simplicity :
    FormNativeGravitySimplicityEquation
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual := by
  intro point
  change Base.gravityAuxiliary point =
    physicalIIPlusBivector (Base.coframe point)
  exact
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_simplicity
      point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
