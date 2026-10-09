import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Consumer
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift RootInquiryCompletion
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (root visit actualOccurrence datum next nextBorn frames runtime presentation targetAt resultFace)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial registered)
end R
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured (lowInitial lowProgramme)
end CF
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (expression input expression_eval updated_value residual_value)
end N
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
  (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace Intake
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower
  (targetAt generatedAction state sourcePresentation targetPresentation target_root target_next compiles successor_valid)
end Intake
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current)
end J
def nativeEventValue {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ target, AddCommGroup (Value target)] {sort : Sorts}
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}} {lower : SourceNativeLedgerRootClosure N V}
    {origin current : V.Current}
    {registered : RootGeneratedDebtActivationJointSource.RegisteredAt
      (Value := Value) (Var := Var) (sort := sort) lower origin}
    (event : RootGeneratedDebtActivationJointSource.EventAt registered current) : Value sort :=
  match RootGeneratedDebtActivationJointSource.mathAction event with
  | .inl settled => settled.1
  | .inr _paid => 0

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

abbrev material := R.actualMaterial frame cfg
abbrev oldPaid := (R.actionResultAt frame cfg (S.actualOccurrence frame)).2.2.1
abbrev initial := CF.lowInitial frame cfg

/-- The occurrence indexes the actual mathematical event, including its paid state. -/
def nativeAt (currentFrame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := PairValue Value)
    (Var := cfg.LowVar) (sort := sort))
    {sourceCurrent : J.Current currentFrame.registered}
    (_supplied : SourceOperationInquiry.Context.Installation.Occurrence currentFrame (current := sourceCurrent)) : PairValue Value sort :=
  nativeEventValue sourceCurrent.2

variable (write : PairValue Value sort → Env (PairValue Value) cfg.LowVar)

/-- Only the actual settlement branch uses this decoder; paid ticks keep their frame. -/
def programme : A.Programme (PhysicalValue := PairValue Value)
    (PhysicalVar := cfg.LowVar) (sort := sort) :=
  { CF.lowProgramme frame cfg with
    datum := fun currentFrame =>
      { (CF.lowProgramme frame cfg).datum currentFrame with
        nextEnvironmentReadAt := some (fun {_sourceCurrent} supplied _queryPaid =>
          write (oldPaid frame cfg + nativeAt cfg currentFrame supplied)) } }

abbrev receipt := Complete.receipt (programme frame cfg write) (initial frame cfg) 0
abbrev selected := Complete.atReceipt (programme frame cfg write) (initial frame cfg) 0
def nativeValue := (receipt frame cfg write).2.1.1
abbrev born := S.nextBorn (selected frame cfg write) (programme frame cfg write)

abbrev sourceTarget := Intake.generatedAction frame cfg (programme frame cfg write)
end SourceGeneratedInquiryReceiptAction.Configured.Writeback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
