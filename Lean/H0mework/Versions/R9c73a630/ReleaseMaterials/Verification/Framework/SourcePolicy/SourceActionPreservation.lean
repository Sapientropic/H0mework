import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyActionPreservation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (stockCfg stock_action_reader stock_query_reader next_action_reader generatedStock)
end AS
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme SourceDatum epoch)
end A
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader)
end R
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (programme raw)
end I
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end S
abbrev Value (_ : Unit) := ℤ
abbrev Var (_ : Unit) := Unit
abbrev Frame := SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := Value) (Var := Var) (sort := ())
def constRaw (value : ℤ × ℤ) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue Value) (Var := Var) (sort := ()) := ⟨fun _ _ => (0,0),.const value⟩
def defaultSource : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()) where
 LowVar := Var
 datum := fun _ => {component := none,reader := fun _ => constRaw (2,1)}
def overriddenSource : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()) :=
 {defaultSource with datum := fun _ => {
   component := none
   reader := fun _ => constRaw (2,1)
   calculationReader := some (fun _ => constRaw (7,3)) }}
def lookalikeSource : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()) :=
 {defaultSource with datum := fun _ => {component := none,reader := fun _ => constRaw (7,3)}}

example (frame : Frame) : R.actionReader frame (AS.stockCfg defaultSource) (S.actualOccurrence frame) = constRaw (2,1) := rfl
example (frame : Frame) : R.actionReader frame (AS.stockCfg overriddenSource) (S.actualOccurrence frame) = constRaw (7,3) := rfl
example (frame : Frame) : R.actionReader frame (AS.stockCfg lookalikeSource) (S.actualOccurrence frame) = constRaw (7,3) := rfl
example (frame : Frame) : (defaultSource.datum frame).calculationReader = none := rfl
example (frame : Frame) : (lookalikeSource.datum frame).calculationReader = none := rfl
example (frame : Frame) : R.actionReader frame (I.programme lookalikeSource) (S.actualOccurrence frame) =
 I.raw (A.epoch frame) lookalikeSource (S.actualOccurrence frame) := rfl

example (frame : Frame) :
 (R.actionReader frame (AS.stockCfg defaultSource) (S.actualOccurrence frame)).expression.eval
  (R.actionReader frame (AS.stockCfg defaultSource) (S.actualOccurrence frame)).environment = (2,1) := rfl
example (frame : Frame) :
 (R.actionReader frame (AS.stockCfg overriddenSource) (S.actualOccurrence frame)).expression.eval
  (R.actionReader frame (AS.stockCfg overriddenSource) (S.actualOccurrence frame)).environment = (7,3) := rfl
example (frame : Frame) :
 R.actionReader frame (AS.stockCfg overriddenSource) (S.actualOccurrence frame) ≠
 R.actionReader frame (AS.stockCfg defaultSource) (S.actualOccurrence frame) := by
 intro same
 have first := congrArg (fun x => x.expression.eval x.environment) same
 change (7,3) = (2,1) at first
 exact (by decide : ((7,3) : ℤ × ℤ) ≠ (2,1)) first

example (frame : Frame) (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ())) :
 type_of% (AS.stock_action_reader frame base (S.actualOccurrence frame)) := AS.stock_action_reader _ _ _
example (frame : Frame) (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ())) :
 type_of% (AS.stock_query_reader frame base (S.actualOccurrence frame)) := AS.stock_query_reader _ _ _

#print axioms AS.stock_action_reader
#print axioms AS.stock_query_reader
#print axioms AS.next_action_reader
end SourcePolicyActionPreservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
