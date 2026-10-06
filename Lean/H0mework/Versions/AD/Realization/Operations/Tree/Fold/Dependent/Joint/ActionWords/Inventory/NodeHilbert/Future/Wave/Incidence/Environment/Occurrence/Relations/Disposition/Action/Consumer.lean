import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Relations.Disposition.Action.Compiler
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Target
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations.Disposition.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift DebtActivationWorld
variable (frame : Frame.{u})
def sourcePresentation : RootInquiryStatePresentation where
 N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
 V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
 state := .create (state frame)
def targetState := RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathState (old frame)
 (registered frame) (packetAt frame) 0
def targetPresentation : RootInquiryStatePresentation where
 N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World (registered frame)
 V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV (registered frame) (packetAt frame)
 state := .create (targetState frame)
theorem literal_next : (generatedAction frame).target.targetAnswerAndNext.nextCurrent=
 ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV (registered frame) (packetAt frame),
 (targetState frame).root.toAuthoritativeRoot,(targetState frame).visit⟩ :=
 (generatedAction frame).target.targetAnswerAndNext_next_eq
theorem successor_valid : (targetPresentation frame).erase=
 (RootInquiryProcessNode.answered (sourcePresentation frame)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame Disposition.programme)).erase ∧
 (RootInquiryProcessNode.active (sourcePresentation frame)).PreservesGeneratedLivingLawAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame Disposition.programme)
  (.active (targetPresentation frame)) := by
 apply RootInquiryProcessNode.active_debtAdmission_successor_valid (sourcePresentation frame) (targetPresentation frame)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame Disposition.programme)
  (generatedAction frame) (compiles frame)
 · exact (congrArg (fun target => (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World (registered frame),target⟩ : AnyAuthoritativeRootCurrent.{u}))
    (literal_next frame)).symm
 · exact HEq.rfl
theorem whole_first : type_of% (generatedAction frame).target.firstDestination_heq :=
 (generatedAction frame).target.firstDestination_heq
theorem all_old_projection (projection : (old frame).root.toAuthoritativeRoot.source.projectionLaw.Projection) :
 type_of% ((generatedAction frame).target.oldOutcome_heq projection) :=
 (generatedAction frame).target.oldOutcome_heq projection
theorem actual_query_state : (actualMaterial frame).state=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace frame Disposition.programme).rootRead.2.1 := rfl
theorem actual_updated_environment : (registered frame).input.environment=afterEnvironment frame := add_sub_cancel _ _
theorem source_effect : type_of% (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.updated_value (R:=ℤ) (actualMaterial frame)) :=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.updated_value (R:=ℤ) (actualMaterial frame)
theorem source_inverse : type_of% (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_value (R:=ℤ) (actualMaterial frame)) :=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_value (R:=ℤ) (actualMaterial frame)
abbrev generated := (sourcePresentation frame,targetPresentation frame,generatedAction frame,Disposition.generated frame)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations.Disposition.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
