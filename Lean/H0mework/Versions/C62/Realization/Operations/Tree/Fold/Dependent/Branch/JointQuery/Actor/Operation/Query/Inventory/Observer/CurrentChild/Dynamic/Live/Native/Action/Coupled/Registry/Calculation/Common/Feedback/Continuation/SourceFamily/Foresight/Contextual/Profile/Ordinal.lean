import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Producer
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Erasure
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Ordinal
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (Cursor)
end O
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (physical pair)
end P
variable {S:Type u} {V X:S→Type u} [∀t,AddCommGroup (V t)] {s:S}
variable (cursor:O.Cursor (PhysicalValue:=V) (PhysicalVar:=X) (sort:=s))
theorem cursor_physical_next : P.physical cursor.next=
 cursor.environment (cursor.old.emitted (cursor.packetAt cursor.current.1).targetCurrent) :=by
 unfold SourceOperationInquiry.Context.Native.Orbit.Installation.Cursor.next
 cases sourceAction : cursor.action with
 | inr paid=>rfl
 | inl settled=>rfl
variable (binding:∀t,X t→Expr V X t)
theorem cursor_pair_next : P.pair binding cursor.next=
 pairEnvironment (cursor.environment (cursor.old.emitted (cursor.packetAt cursor.current.1).targetCurrent))
  (SourceSubstitution.sourceEnvironment binding
    (cursor.environment (cursor.old.emitted (cursor.packetAt cursor.current.1).targetCurrent))-
   cursor.environment (cursor.old.emitted (cursor.packetAt cursor.current.1).targetCurrent)) :=
 congrArg (fun base=>pairEnvironment base (SourceSubstitution.sourceEnvironment binding base-base))
  (cursor_physical_next cursor)

section RegisteredProjection
variable {N : WorldRelationNetwork.{u}} {L : Vocabulary.{u}}
variable (lower : SourceNativeLedgerRootClosure N L) {origin : L.Current}
variable (registered : RootGeneratedDebtActivationJointSource.RegisteredAt
 (Value:=V) (Var:=X) (sort:=s) lower origin)
variable (packetAt : (current : L.Current) → RootGeneratedDebtActivationJointSource.Successor.Packet lower current)
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current targetCurrent)
end J
def parentAdvance (count : Nat) (current : L.Current) : L.Current :=
 Nat.rec current (fun _ previous => (packetAt previous).targetCurrent) count
def registeredAdvance (count : Nat) (current : J.Current registered) : J.Current registered :=
 Nat.rec current (fun _ previous => J.targetCurrent registered packetAt previous) count
theorem registered_parent_prefix (count : Nat) (current : J.Current registered) :
 (registeredAdvance lower registered packetAt count current).1=parentAdvance lower packetAt count current.1 := by
 induction count with
 | zero => rfl
 | succ count previous =>
  change (packetAt (registeredAdvance lower registered packetAt count current).1).targetCurrent=_
  rw [previous]
  rfl
theorem cross_registered_parent_prefix
 (other : RootGeneratedDebtActivationJointSource.RegisteredAt (Value:=V) (Var:=X) (sort:=s) lower origin)
 (before : J.Current registered) (after : J.Current other) (sameParent : before.1=after.1) (count : Nat) :
 (registeredAdvance lower registered packetAt count before).1=
 (registeredAdvance lower other packetAt count after).1 :=
 (registered_parent_prefix lower registered packetAt count before).trans
  ((congrArg (parentAdvance lower packetAt count) sameParent).trans
   (registered_parent_prefix lower other packetAt count after).symm)
end RegisteredProjection
end Lower.SourceFamily.Foresight.Contextual.Profile.Ordinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
