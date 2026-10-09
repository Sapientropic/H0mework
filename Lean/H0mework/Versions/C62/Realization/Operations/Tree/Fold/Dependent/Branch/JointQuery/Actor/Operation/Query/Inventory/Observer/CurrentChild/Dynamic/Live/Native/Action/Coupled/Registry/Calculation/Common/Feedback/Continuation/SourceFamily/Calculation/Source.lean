import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Installation
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Packet
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily.Evaluated
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base baseRoot actualOccurrence)
end Q
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw runtimeCurrent)
namespace C
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (targetRuntime completed target_factorizes)
end C
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (lineage debtStep activePayment activeContinuation no_refill wellFounded endpoint_no_paid)
end P
end O
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (binding : ∀ t,X t → Expr W X t)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
abbrev epoch := SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame
abbrev cfg := Future.Replay.Move.Faces.configuration (Future.Replay.Installed.programme binding seed)
def face : SourceNativeRootSemanticFaceAt (StockObservation.root frame (cfg binding seed))
 (StockObservation.visit frame (cfg binding seed)) where
 projection:=.inherited (.inherited (.inherited (.inherited (.component (.inherited (.component PUnit.unit))))))
 active:=PUnit.unit
 classifier_eq:=rfl
-- Both views are eliminations of the already installed source material.
def raw : O.Raw (Value:=PairValue W) (Var:=X) (sort:=s) :=
 (face binding seed frame).rootRead.2.2.2.2.2.2.1
def result := (face binding seed frame).rootRead.2.2.2.2.2.2.2.2.2.1
abbrev authority := (Q.base frame).root.toAuthoritativeRoot
def reader (_other : (authority frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
 frame.currentState.visit.current) : O.Raw (Value:=PairValue W) (Var:=X) (sort:=s) := raw binding seed frame
abbrev context := O.C.targetRuntime (authority frame) frame.currentState.visit.current (reader binding seed frame)

theorem raw_source : raw binding seed frame=Future.Replay.Source.raw binding seed (epoch frame) (Q.actualOccurrence frame) := rfl

theorem same_result : result binding seed frame=Future.Replay.Source.result binding seed (epoch frame) (Q.actualOccurrence frame) := rfl

theorem same_state : (result binding seed frame).2.1=
 O.runtimeCurrent (authority frame) frame.currentState.visit.current (reader binding seed frame) (context binding seed frame) := rfl

def completed : SourceOperationExecutionDebt.Settlement (result binding seed frame).2.1 :=
 O.C.completed (authority frame) frame.currentState.visit.current (reader binding seed frame)

theorem whole_factorizes : type_of% (O.C.target_factorizes (authority frame) frame.currentState.visit.current (reader binding seed frame)) :=
 O.C.target_factorizes _ _ _

def active_payment (count : Fin (remaining (raw binding seed frame).expression)) :=
 O.P.activePayment (authority frame) frame.currentState.visit.current (reader binding seed frame) count

def active_continuation (count : Fin (remaining (raw binding seed frame).expression)) :=
 O.P.activeContinuation (authority frame) frame.currentState.visit.current (reader binding seed frame) count

def lineage (count : Nat) : type_of% (O.P.lineage (authority frame) frame.currentState.visit.current (reader binding seed frame) count) :=
 O.P.lineage _ _ _ count

theorem no_refill (count : Nat) : type_of% (O.P.no_refill (authority frame) frame.currentState.visit.current (reader binding seed frame) count) :=
 O.P.no_refill _ _ _ count

theorem noetherian : type_of% (O.P.wellFounded (authority frame) frame.currentState.visit.current (reader binding seed frame)) :=
 O.P.wellFounded _ _ _

theorem endpoint_no_paid : type_of% (O.P.endpoint_no_paid (authority frame) frame.currentState.visit.current (reader binding seed frame)) :=
 O.P.endpoint_no_paid _ _ _
theorem paid_debit (count : Fin (remaining (raw binding seed frame).expression)) :
 type_of% (active_payment binding seed frame count).strictDebit := (active_payment binding seed frame count).strictDebit

theorem complete_fee : (result binding seed frame).2.1.2.length=remaining (raw binding seed frame).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.completed_history _ _ _

end Lower.SourceFamily.Evaluated
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
