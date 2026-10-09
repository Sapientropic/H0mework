import SaturationMonoid.GenericFoundation.Responsibility.Debt.Activation.Root.Direct.JointSource.Successor.Inquiry.Continuation.Completion
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Installation
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Difference.Incoming
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.Source
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Psi
namespace I
export Lower.SourceFamily.Foresight.Contextual.Installed (configuration)
end I
namespace Receipt
export SourceGeneratedInquiryReceiptAction (bornFrame actualMaterial)
end Receipt
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (mathAnswerFace)
end J
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap (initial)
end B
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
 (liftEvent mapped_trace)
end T
variable {S : Type u} {W X : S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀t,X t→Expr W X t) (n:Nat)
variable (seed : Lower.SourceFamily.Seed W X s n)
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Lower.Value W n) (Var:=X) (sort:=s))
def cfg0 := {Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.Installation.configuration binding n seed with
 datum := fun sourceFrame =>
  let original := (Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.Installation.configuration binding n seed).datum sourceFrame
  { original with
    calculationReader :=
      Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.calculationReader
        sourceFrame original }
}
abbrev receipt := Receipt.bornFrame frame (cfg0 binding n seed)
abbrev budget := remaining (receipt binding n seed frame).registered.input.expression
abbrev endpointDepth := budget binding n seed frame-1
def endpointFrame := {receipt binding n seed frame with depth:=endpointDepth binding n seed frame}
abbrev installedFace := J.mathAnswerFace (receipt binding n seed frame).old
 (receipt binding n seed frame).registered (receipt binding n seed frame).packetAt
 (endpointDepth binding n seed frame)
def written := SourceOperationPaidRelations.exposure (installedFace binding n seed frame).rootRead.state.2
def lifted := (written binding n seed frame).map T.liftEvent

theorem budget_positive : 0<budget binding n seed frame := by
  have source := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget
    (Receipt.actualMaterial frame (cfg0 binding n seed))
  change budget binding n seed frame=_ at source
  omega

theorem source_clock : (endpointFrame binding n seed frame).depth+1=
    remaining (endpointFrame binding n seed frame).registered.input.expression := by
  have positive := budget_positive binding n seed frame
  change budget binding n seed frame-1+1=budget binding n seed frame
  omega

theorem installed_full_state : type_of% (SourceRegisteredClaimCompletion.terminal_state
    (endpointFrame binding n seed frame) (source_clock binding n seed frame)) :=
  SourceRegisteredClaimCompletion.terminal_state _ (source_clock binding n seed frame)

theorem complete_fee : (installedFace binding n seed frame).rootRead.state.2.length=
    budget binding n seed frame :=
  SourceRegisteredClaimCompletion.terminal_fee (endpointFrame binding n seed frame)
    (source_clock binding n seed frame)

variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt
 (Expr (PairValue (Lower.Value W n)) X s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt
 (Expr (PairValue (PairValue (Lower.Value W n))) X s)))

theorem bootstrap_old : (B.initial frame (cfg0 binding n seed) scalar pair).old=
    (receipt binding n seed frame).old := rfl
theorem bootstrap_registered : (B.initial frame (cfg0 binding n seed) scalar pair).registered=
    (receipt binding n seed frame).registered := rfl
theorem bootstrap_packet : (B.initial frame (cfg0 binding n seed) scalar pair).packetAt=
    (receipt binding n seed frame).packetAt := rfl

theorem bootstrap_written :
    SourceOperationPaidRelations.exposure
      (J.mathAnswerFace (B.initial frame (cfg0 binding n seed) scalar pair).old
        (B.initial frame (cfg0 binding n seed) scalar pair).registered
        (B.initial frame (cfg0 binding n seed) scalar pair).packetAt
        (remaining (B.initial frame (cfg0 binding n seed) scalar pair).registered.input.expression-1)).rootRead.state.2 =
      written binding n seed frame := rfl

omit scalar pair in
theorem lifted_event (event)
    (present : event∈(written binding n seed frame).trace) :
    T.liftEvent event∈(lifted binding n seed frame).trace := by
  rw [lifted,T.mapped_trace]
  exact List.mem_map_of_mem present

omit scalar pair in
def append (existing : RootedAccountedUnfolding (PresentedRelationEventAt
    (Expr (PairValue (PairValue (Lower.Value W n))) X s))) :=
  SourceHistoryCommon.seed existing (lifted binding n seed frame)

omit scalar pair in
theorem append_source_event
    (existing : RootedAccountedUnfolding (PresentedRelationEventAt
      (Expr (PairValue (PairValue (Lower.Value W n))) X s)))
    (event) (present : event∈(written binding n seed frame).trace) :
    T.liftEvent event∈(append binding n seed frame existing).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 _ (lifted_event binding n seed frame event present)

end Lower.SourceFamily.Foresight.Contextual.Psi
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
