import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Joint
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Mixed.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Reader.Core
namespace C
export Lower.SourceFamily.Foresight.Contextual
 (low request sourceEnvironment projection_environment actualIndex)
end C
namespace I
export Lower.SourceFamily.Foresight.Contextual.Inquiry
 (rawAt query written source_query_environment source_complete_preserves source_complete_paid_trace)
end I
namespace G
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated
 (face disposition queryResult)
end G
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence)
end Q
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t, X t → Expr W X t) (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
variable (frame : M.Frame (Value := Lower.Value W n) (Var := X) (sort := s))
variable (index : Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
abbrev completed := G.queryResult seed frame index.2 (I.rawAt binding n seed frame)
def residualExpression := Expr.add (I.query binding n seed frame index).expression
 (Expr.linear (-AddMonoidHom.id _) (completed binding n seed frame index).2.1.1)
abbrev sourceBinding := Future.Replay.pairBinding (Future.Replay.Binding.at binding n)
def feedbackExpression := (residualExpression binding n seed frame index).subst (sourceBinding binding n)

def expression := Expr.add (residualExpression binding n seed frame index)
 (feedbackExpression binding n seed frame index)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (Lower.Value W n)) (Var := X) (sort := s) :=
 ⟨C.sourceEnvironment binding n seed frame index,expression binding n seed frame index⟩
def reader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :=
 raw binding n seed frame ⟨current,supplied⟩
def result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (Q.base frame).root.toAuthoritativeRoot (reader binding n seed frame) index.2

def material := (C.low binding n seed frame index,C.request binding n seed frame index,
 G.face seed frame index.2 (I.rawAt binding n seed frame index.2),
 G.disposition seed frame index.2 (I.rawAt binding n seed frame index.2),
 I.query binding n seed frame index,completed binding n seed frame index,
 I.written binding n seed frame index,raw binding n seed frame index,result binding n seed frame index)
def pairWritten := SourceHistoryCommon.seed (I.written binding n seed frame index)
 (SourceOperationPaidRelations.exposure (result binding n seed frame index).2.1.2)

theorem raw_environment : (raw binding n seed frame index).environment=
 Future.Replay.Source.pairEnvironment (Future.Replay.Binding.at binding n) frame index.2 :=
 C.projection_environment binding n seed frame index

theorem query_environment : (I.query binding n seed frame index).environment=
 (raw binding n seed frame index).environment :=
 (I.source_query_environment binding n seed frame index).trans (raw_environment binding n seed frame index).symm

theorem generated_value : (result binding n seed frame index).2.2.1=
 (raw binding n seed frame index).expression.eval (raw binding n seed frame index).environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
theorem generated_cost : (result binding n seed frame index).2.1.2.length=
 remaining (expression binding n seed frame index) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _

theorem residual_fee : 2≤remaining (residualExpression binding n seed frame index) := by
 change 2≤remaining (I.query binding n seed frame index).expression+
  (remaining (completed binding n seed frame index).2.1.1+1)+1
 omega

theorem source_fee : 3≤remaining (expression binding n seed frame index) := by
 change 3≤remaining (residualExpression binding n seed frame index)+
  remaining (feedbackExpression binding n seed frame index)+1
 have paid:=residual_fee binding n seed frame index
 omega

theorem complete_source_inventory :
 ∀ event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
  seed frame index.2).trace, event ∈ (pairWritten binding n seed frame index).trace := by
 intro event present
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event
  (I.source_complete_preserves binding n seed frame index event present)

theorem complete_query_trace :
 ∀ event ∈ (SourceOperationPaidRelations.exposure (completed binding n seed frame index).2.1.2).trace,
 event ∈ (pairWritten binding n seed frame index).trace := by
 intro event present
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event
  (I.source_complete_paid_trace binding n seed frame index event present)

theorem complete_native_trace :
 ∀ event ∈ (SourceOperationPaidRelations.exposure (result binding n seed frame index).2.1.2).trace,
 event ∈ (pairWritten binding n seed frame index).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1

abbrev actualMaterial := material binding n seed
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (C.actualIndex n frame)
end Lower.SourceFamily.Foresight.Contextual.Reader.Core
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
