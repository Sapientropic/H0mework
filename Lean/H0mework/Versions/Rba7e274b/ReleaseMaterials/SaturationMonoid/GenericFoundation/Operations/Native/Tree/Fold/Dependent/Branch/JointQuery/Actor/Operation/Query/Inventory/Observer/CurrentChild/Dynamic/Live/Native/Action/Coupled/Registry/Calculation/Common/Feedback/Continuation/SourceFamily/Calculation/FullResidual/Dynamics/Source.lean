import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.FullResidual.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export Lower.SourceFamily (Factory Packet Seed cfg)
end SF
namespace L
export Lower (Value groups)
end L
namespace AS
export Lower.SourceFamily.ActivationSource
  (stockCfg receiver nextCfg nextBase write nativeAfterAdmission bornAfterNative AdmissionPacket localNativeReceipt)
end AS
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (datum actualVisit actualOccurrence next nextBorn frames)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial)
end R
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeValue nativeAt nativeEventValue native_value updated_total)
end WB
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input)
end N
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor (write)
end SS
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active)
end E
variable {W X : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (W target)]
local instance levelGroups (n : Nat) (target : PUnit.{u+1}) : AddCommGroup (L.Value W n target) := L.groups W n target
variable (factory : SF.Factory W X PUnit.unit) (n : Nat)
variable (data : SF.Packet (W := W) (X := X) (s := PUnit.unit) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : sourceCfg.LowVar = X)
abbrev receiver := AS.receiver factory n data sourceCfg language
abbrev configuration : A.Programme (PhysicalValue := PairValue (L.Value W n))
    (PhysicalVar := sourceCfg.LowVar) (sort := PUnit.unit) := AS.nextCfg factory n data sourceCfg language
abbrev receipt := Complete.receipt (configuration factory n data sourceCfg language) (receiver factory n data sourceCfg language) 0
abbrev selected := Complete.atReceipt (configuration factory n data sourceCfg language) (receiver factory n data sourceCfg language) 0
abbrev born := S.nextBorn (selected factory n data sourceCfg language) (configuration factory n data sourceCfg language)
def nativeValue : PairValue (L.Value W n) PUnit.unit := (receipt factory n data sourceCfg language).2.1.1

theorem write_all (value : PairValue (L.Value W n) PUnit.unit) :
    AS.write factory n data sourceCfg language value = SS.write n sourceCfg value := by
  funext target name
  cases target
  simp only [AS.write, SS.write]
  exact dif_pos trivial

theorem decoder_source (currentFrame : A.M.Frame (Value := PairValue (L.Value W n)) (Var := sourceCfg.LowVar) (sort := PUnit.unit)) :
    ((configuration factory n data sourceCfg language).datum currentFrame).nextEnvironmentReadAt =
      some (fun {_current} supplied _queryPaid =>
        AS.write factory n data sourceCfg language (WB.oldPaid data.1 sourceCfg + WB.nativeAt sourceCfg currentFrame supplied)) := rfl

theorem selected_raw : (selected factory n data sourceCfg language).rawRead =
    (receiver factory n data sourceCfg language).rawRead := by
  apply Prefix.receipt_read (configuration factory n data sourceCfg language) (receiver factory n data sourceCfg language)
    (fun stage => (S.frames (receiver factory n data sourceCfg language) (configuration factory n data sourceCfg language) stage).rawRead)
  intro stage paid action
  have next : S.frames (receiver factory n data sourceCfg language) (configuration factory n data sourceCfg language) (stage + 1) =
      (S.frames (receiver factory n data sourceCfg language) (configuration factory n data sourceCfg language) stage).mathNext := by
    change S.next _ _ = _
    unfold S.next
    rw [action]
  exact (congrArg (fun candidate : A.M.Frame (Value := PairValue (L.Value W n))
    (Var := sourceCfg.LowVar) (sort := PUnit.unit) => candidate.rawRead) next).trans rfl

theorem native_value : nativeValue factory n data sourceCfg language =
    (N.expression (R.actualMaterial data.1 sourceCfg)).eval (N.input (R.actualMaterial data.1 sourceCfg)).environment := by
  have value := SourceOperationExecutionDebt.completed_value
    (selected factory n data sourceCfg language).event.state (receipt factory n data sourceCfg language).2.1
  change nativeValue factory n data sourceCfg language =
    (selected factory n data sourceCfg language).rawRead.expression.eval
      (selected factory n data sourceCfg language).rawRead.environment at value
  rw [selected_raw] at value
  exact value

theorem updated_total : WB.oldPaid data.1 sourceCfg + nativeValue factory n data sourceCfg language =
    (R.actualMaterial data.1 sourceCfg).raw.eval (N.input (R.actualMaterial data.1 sourceCfg)).environment :=
  (congrArg (fun value => WB.oldPaid data.1 sourceCfg + value)
    ((native_value factory n data sourceCfg language).trans
      (WB.native_value data.1 sourceCfg (AS.write factory n data sourceCfg language)).symm)).trans
        (WB.updated_total data.1 sourceCfg (AS.write factory n data sourceCfg language))

theorem born_environment : E.At (born factory n data sourceCfg language)
    (AS.write factory n data sourceCfg language (WB.oldPaid data.1 sourceCfg + nativeValue factory n data sourceCfg language)) := by
  intro current occurrence
  change AS.write factory n data sourceCfg language (WB.oldPaid data.1 sourceCfg +
    WB.nativeEventValue (S.actualVisit (selected factory n data sourceCfg language)).current.2) = _
  have event : (S.actualVisit (selected factory n data sourceCfg language)).current.2 =
      (selected factory n data sourceCfg language).event := rfl
  have atEvent := congrArg WB.nativeEventValue event
  have actual : WB.nativeEventValue (selected factory n data sourceCfg language).event =
      nativeValue factory n data sourceCfg language := by
    unfold WB.nativeEventValue
    have chosen := (receipt factory n data sourceCfg language).2.2.2
    dsimp only [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.action] at chosen
    rw [chosen]
    rfl
  exact congrArg (fun value => AS.write factory n data sourceCfg language (WB.oldPaid data.1 sourceCfg + value))
    (atEvent.trans actual)

theorem actual_writeback : E.At (born factory n data sourceCfg language)
    (AS.write factory n data sourceCfg language
      ((R.actualMaterial data.1 sourceCfg).raw.eval (N.input (R.actualMaterial data.1 sourceCfg)).environment)) := by
  intro current occurrence
  exact ((born_environment factory n data sourceCfg language) occurrence).trans
    (congrArg (AS.write factory n data sourceCfg language) (updated_total factory n data sourceCfg language))

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
