import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Consumer
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Runtime
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Births
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (datum root visit actualVisit actualOccurrence frames runtime next nextBorn)
end S
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (Factory Packet cfg nextSeed step)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
  (Value groups)
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock
  (scalar pair)
end Stock
end L
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
  (preserve)
end T
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap
  (initial originalTargetAt original_target_root)
end B
namespace Admission
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission
  (targetAt generatedAction sourceEvent compiles target_root target_current successor_valid query)
end Admission
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback
  (oldPaid material nativeAt nativeEventValue programme nativeValue native_value updated_total)
end WB
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt receipt_compiles receipt_next)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace Births
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Births (birthIndex cover actual_action actual_compiles)
end Births
namespace NF
export SourceOperationInquiry.Context.Native.Frame (read actual fullword_read model_next observer)
end NF
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input)
end N

variable {W X : PUnit.{u+1} → Type u} [∀ t, AddCommGroup (W t)]
local instance levelGroups (n : Nat) (t : PUnit.{u+1}) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X PUnit.unit) (n : Nat)
variable (data : SF.Packet (W := W) (X := X) (s := PUnit.unit) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : sourceCfg.LowVar = X)

def write : PairValue (L.Value W n) PUnit.unit → Env (PairValue (L.Value W n)) sourceCfg.LowVar :=
  fun pair coordinate _name => by cases coordinate; exact pair

abbrev oldPair := WB.oldPaid data.1 sourceCfg
abbrev sourceMaterial := WB.material data.1 sourceCfg

def scalar := T.preserve (language.symm ▸ factory.extraScalar n data.2 data.1)
  (L.Stock.scalar data.1 sourceCfg language)
def pair := T.preserve (language.symm ▸ factory.extraPair n data.2 data.1)
  (L.Stock.pair data.1 sourceCfg language)
abbrev receiver := B.initial data.1 sourceCfg (scalar factory n data sourceCfg language)
  (pair factory n data sourceCfg language)
def seed := SourceHistoryCommon.seed (scalar factory n data sourceCfg language)
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
    (receiver factory n data sourceCfg language).registered.input.expression))
def nextFactory : SF.Factory W sourceCfg.LowVar PUnit.unit := language.symm ▸ factory
def template : A.Programme (PhysicalValue := PairValue (L.Value W n))
    (PhysicalVar := sourceCfg.LowVar) (sort := PUnit.unit) := SF.cfg (nextFactory factory n sourceCfg language) (n + 1)
  (seed factory n data sourceCfg language)

def nextCfg := {template factory n data sourceCfg language with
  datum := fun currentFrame => { (template factory n data sourceCfg language).datum currentFrame with
    nextEnvironmentReadAt :=
      ((WB.programme data.1 sourceCfg (write n sourceCfg)).datum currentFrame).nextEnvironmentReadAt } }

theorem decoder_source (currentFrame : A.M.Frame (Value := PairValue (L.Value W n))
    (Var := sourceCfg.LowVar) (sort := PUnit.unit)) :
    ((nextCfg factory n data sourceCfg language).datum currentFrame).nextEnvironmentReadAt =
      some (fun {_current} supplied _queryPaid =>
        write n sourceCfg (oldPair n data sourceCfg + WB.nativeAt sourceCfg currentFrame supplied)) := rfl

theorem reader_preserved (currentFrame : A.M.Frame (Value := PairValue (L.Value W n))
    (Var := sourceCfg.LowVar) (sort := PUnit.unit))
    (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered) :
    ((nextCfg factory n data sourceCfg language).datum currentFrame).reader (current := current) =
      ((template factory n data sourceCfg language).datum currentFrame).reader (current := current) := rfl
theorem calculation_reader_preserved (currentFrame : A.M.Frame (Value := PairValue (L.Value W n))
    (Var := sourceCfg.LowVar) (sort := PUnit.unit)) :
    ((nextCfg factory n data sourceCfg language).datum currentFrame).calculationReader =
      ((template factory n data sourceCfg language).datum currentFrame).calculationReader := rfl
theorem inventories_preserved :
    (nextCfg factory n data sourceCfg language).nextInventory = (template factory n data sourceCfg language).nextInventory ∧
    (nextCfg factory n data sourceCfg language).nextPairInventory = (template factory n data sourceCfg language).nextPairInventory := ⟨rfl, rfl⟩


end SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
