import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Runtime
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (Factory Seed Packet cfg)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
  (Value groups)
end L
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme SourceDatum epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (datum baseRoot actualOccurrence)
end S
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial afterEnvironment)
end R
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (n : Nat) (target : Sorts) : AddCommGroup (L.Value W n target) := L.groups W n target

def codeAt (sourceCode : Expr (PairValue W) X s) :
    (n : Nat) → Expr (PairValue (L.Value W n)) X s
  | 0 => sourceCode
  | n + 1 => liftExpr (codeAt sourceCode n)

variable (factory : SF.Factory W X s) (sourceCode : Expr (PairValue W) X s)
variable (n : Nat) (seed : SF.Seed W X s n)
variable (frame : A.M.Frame (Value := L.Value W n) (Var := X) (sort := s))

def raw {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    O.Raw (Value := PairValue (L.Value W n)) (Var := X) (sort := s) :=
  ⟨((factory.datum n seed frame).reader supplied).environment, codeAt sourceCode n⟩

-- The source datum is changed before admission; the original reader, its environment and lifecycle callbacks remain the source.
def withCalculation : SF.Factory W X s :=
  { factory with datum := fun grade inventory currentFrame =>
      { factory.datum grade inventory currentFrame with
        calculationReader := some (fun {_current} supplied => raw factory sourceCode grade inventory currentFrame supplied) } }

theorem reader_source {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered} :
    ((withCalculation factory sourceCode).datum n seed frame).reader (current := current) =
      (factory.datum n seed frame).reader (current := current) := rfl

theorem source_callbacks :
    (withCalculation factory sourceCode).nextInventory = factory.nextInventory ∧
    (withCalculation factory sourceCode).nextPairInventory = factory.nextPairInventory ∧
    (withCalculation factory sourceCode).extraScalar = factory.extraScalar ∧
    (withCalculation factory sourceCode).extraPair = factory.extraPair := ⟨rfl, rfl, rfl, rfl⟩

theorem decoder_source :
    ((withCalculation factory sourceCode).datum n seed frame).nextEnvironmentReadAt =
      (factory.datum n seed frame).nextEnvironmentReadAt := rfl

theorem action_reader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    R.actionReader frame (SF.cfg (withCalculation factory sourceCode) n seed) supplied =
      raw factory sourceCode n seed (A.epoch frame) supplied := rfl

theorem transported_action_code {Y Z : Sorts → Type u} (same : Y = Z)
    (baseFactory : SF.Factory W Z s) (baseCode : Expr (PairValue W) Z s)
    (grade : Nat) (inventory : SF.Seed W Y s grade)
    (currentFrame : A.M.Frame (Value := L.Value W grade) (Var := Y) (sort := s))
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence currentFrame (current := current)) :
    (R.actionReader currentFrame (SF.cfg (same.symm ▸ withCalculation baseFactory baseCode : SF.Factory W Y s)
      grade inventory) supplied).expression =
        (same.symm ▸ codeAt baseCode grade : Expr (PairValue (L.Value W grade)) Y s) := by
  cases same
  rfl

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
