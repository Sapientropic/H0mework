import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Relations.Disposition.Consumer
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
abbrev old := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.answeredState frame Disposition.programme
abbrev current := (old frame).visit.current
abbrev occurrence := (old frame).root.emitted (current frame)
def afterEnvironment : Env (PairValue Value.{u}) Var.{u} := (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame Disposition.programme) Disposition.programme).raw.environment
def material (supplied : (old frame).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (current frame)) :
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
 (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) supplied :=
 let sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) := (Shared.datum frame Disposition.programme).reader supplied
 { environment:=sourceRaw.environment
   increment:=afterEnvironment frame-sourceRaw.environment
   raw:=sourceRaw.expression
   state:=(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultAt frame Disposition.programme supplied).2.1
   owner:=SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.entryAt frame supplied }
def registered := RootGeneratedDebtActivationJointSource.register (fun supplied => RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (material frame supplied))
abbrev actualMaterial := material frame (occurrence frame)
def packetAt (candidate : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered) :=
 (RootGeneratedDebtActivationJointSource.Successor.read? (old frame).root.toAuthoritativeRoot.toLedgerRoot candidate).get (by rfl)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations.Disposition.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
