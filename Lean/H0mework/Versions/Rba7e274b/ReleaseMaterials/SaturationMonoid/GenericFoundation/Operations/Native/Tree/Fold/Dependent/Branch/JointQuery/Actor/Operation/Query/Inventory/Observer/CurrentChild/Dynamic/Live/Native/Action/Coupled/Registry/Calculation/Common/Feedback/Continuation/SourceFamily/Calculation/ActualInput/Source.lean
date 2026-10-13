import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.Factory.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
  (codeAt collapseValue code_base_value)
end CF
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (Factory Seed Packet cfg)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
  (Value groups)
end L
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence baseRoot next)
end S
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence residualAt)
end I
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial afterEnvironment)
end R
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (n : Nat) (target : Sorts) : AddCommGroup (L.Value W n target) := L.groups W n target
variable (n : Nat)
variable (frame : A.M.Frame (Value := L.Value W n) (Var := X) (sort := s))

def environment {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : I.Occurrence frame (current := current)) : Env (L.Value W n) X :=
  (N.input (I.residualAt frame supplied)).environment

theorem environment_at_current {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : I.Occurrence frame (current := current)) :
    environment n frame supplied = frame.environment (frame.old.root.emitted current.1) := by
  rcases supplied with ⟨support, event⟩
  cases event
  exact add_sub_cancel _ _

theorem actual_environment : environment n (A.epoch frame) (S.actualOccurrence frame) = frame.activeEnvironment := by
  exact environment_at_current n (A.epoch frame) (S.actualOccurrence frame)

variable (sourceCode : Expr (PairValue W) X s)

def raw {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : I.Occurrence frame (current := current)) :
    O.Raw (Value := PairValue (L.Value W n)) (Var := X) (sort := s) :=
  ⟨pairEnvironment (environment n frame supplied) 0, CF.codeAt sourceCode n⟩

variable (factory : SF.Factory W X s)

-- Read the supplied occurrence's already generated physical update before admission.
def withActualInput : SF.Factory W X s :=
  { factory with datum := fun grade inventory currentFrame =>
      { factory.datum grade inventory currentFrame with
        calculationReader := some (fun {_current} supplied => raw grade currentFrame sourceCode supplied) } }

theorem action_reader (seed : SF.Seed W X s n)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : I.Occurrence frame (current := current)) :
    R.actionReader frame (SF.cfg (withActualInput sourceCode factory) n seed) supplied =
      raw n (A.epoch frame) sourceCode supplied := rfl

theorem actual_reader_environment (seed : SF.Seed W X s n) :
    (R.actionReader frame (SF.cfg (withActualInput sourceCode factory) n seed) (S.actualOccurrence frame)).environment =
      pairEnvironment frame.activeEnvironment 0 :=
  congrArg (fun env => pairEnvironment env (0 : Env (L.Value W n) X)) (actual_environment n frame)

theorem source_callbacks (seed : SF.Seed W X s n) :
    (withActualInput sourceCode factory).nextInventory = factory.nextInventory ∧
    (withActualInput sourceCode factory).nextPairInventory = factory.nextPairInventory ∧
    (withActualInput sourceCode factory).extraScalar = factory.extraScalar ∧
    (withActualInput sourceCode factory).extraPair = factory.extraPair ∧
    ((withActualInput sourceCode factory).datum n seed frame).nextEnvironmentReadAt =
      (factory.datum n seed frame).nextEnvironmentReadAt := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem transported_action_raw {Y Z : Sorts → Type u} (same : Y = Z)
    (baseFactory : SF.Factory W Z s) (baseCode : Expr (PairValue W) Z s)
    (grade : Nat) (inventory : SF.Seed W Y s grade)
    (currentFrame : A.M.Frame (Value := L.Value W grade) (Var := Y) (sort := s))
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : I.Occurrence currentFrame (current := current)) :
    R.actionReader currentFrame (SF.cfg (same.symm ▸ withActualInput baseCode baseFactory : SF.Factory W Y s)
      grade inventory) supplied = raw grade (A.epoch currentFrame) (same.symm ▸ baseCode) supplied := by
  cases same
  rfl

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
