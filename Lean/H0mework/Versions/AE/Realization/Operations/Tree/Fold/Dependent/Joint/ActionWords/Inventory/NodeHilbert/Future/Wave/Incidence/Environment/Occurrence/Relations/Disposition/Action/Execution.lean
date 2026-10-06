import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Relations.Disposition.Action.Source
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
private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement
 (RootGeneratedDebtActivationJointSource.initialEvent (registered frame)).state) : False := by
 have zero := (RootGeneratedDebtActivationJointSource.Idle.law (registered frame).input.environment
  (registered frame).input.expression).settlement_budget_zero settled
 have sourceBudget := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (actualMaterial frame)
 change remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (actualMaterial frame))=0 at zero
 omega
def firstStep := match _selected : RootGeneratedDebtActivationJointSource.mathAction
 (RootGeneratedDebtActivationJointSource.initialEvent (registered frame)) with
 | .inl settled => False.elim (not_settled frame settled)
 | .inr paid => paid
theorem first_action : RootGeneratedDebtActivationJointSource.Successor.Inquiry.sourceAction
 (old frame) (registered frame) (packetAt frame)=.inr (firstStep frame) := by
 apply (RootGeneratedDebtActivationJointSource.Successor.Inquiry.sourceAction_eq (old frame) (registered frame) (packetAt frame)).trans
 unfold firstStep
 cases selected : RootGeneratedDebtActivationJointSource.mathAction (RootGeneratedDebtActivationJointSource.initialEvent (registered frame)) with
 | inl settled => exact False.elim (not_settled frame settled)
 | inr paid => rfl
def birthProgram := RootGeneratedDebtActivationJointSource.Successor.Inquiry.birthProgram
 (old frame) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame Disposition.programme) (registered frame) (packetAt frame)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority frame Disposition.programme)
 (firstStep frame) (first_action frame)
def sourceEvent := (old frame).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (old frame).visit
def generatedAction := (birthProgram frame).generate (sourceEvent frame)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations.Disposition.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
