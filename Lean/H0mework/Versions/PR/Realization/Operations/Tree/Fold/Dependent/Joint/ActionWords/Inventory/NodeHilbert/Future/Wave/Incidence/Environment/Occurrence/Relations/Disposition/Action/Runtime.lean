import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Relations.Disposition.Action.Consumer
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Target
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Payment
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
def bornFrame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) where
 N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
 V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
 old := old frame
 registered := registered frame
 packetAt := packetAt frame
 environment := fun {_current} supplied => ((Shared.datum frame Disposition.programme).reader supplied).environment
 depth := 0
 inventory := some (Disposition.completeWritten (A.epoch frame) (Shared.actualOccurrence frame))
abbrev runtime := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.runtime (bornFrame frame)
theorem born_current : (bornFrame frame).currentState=targetState frame := rfl
theorem born_inventory : (bornFrame frame).inventory=
 some (Disposition.completeWritten (A.epoch frame) (Shared.actualOccurrence frame)) := rfl
theorem runtime_current : (runtime frame).initialState.engine.node.erase=(targetPresentation frame).erase :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.actual_current (bornFrame frame) 0
theorem runtime_next (stage : Nat) : type_of%
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next (bornFrame frame) stage) :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next (bornFrame frame) stage
theorem runtime_preserves (stage : Nat) : type_of%
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next_preserves (bornFrame frame) stage) :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next_preserves (bornFrame frame) stage
theorem no_refill : type_of%
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.no_refill (bornFrame frame)) :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.no_refill (bornFrame frame)
theorem noetherian : type_of%
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.continuation_wellFounded (bornFrame frame)) :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.continuation_wellFounded (bornFrame frame)
abbrev actualGenerated := (generated frame,runtime frame)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations.Disposition.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
