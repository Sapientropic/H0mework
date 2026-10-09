import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Ordinal
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation SourceOperationScalarRelations
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Origin
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (Cursor)
end O
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (physical pair source source_fibre)
end P
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Ordinal (parentAdvance registeredAdvance registered_parent_prefix)
end A
variable {S : Type u} {V X : S→Type u} [∀t,AddCommGroup (V t)] {s:S}

private theorem parent_shift {N : WorldRelationNetwork.{u}} {L : Vocabulary.{u}}
 (lower : SourceNativeLedgerRootClosure N L)
 (packetAt : (current : L.Current) → RootGeneratedDebtActivationJointSource.Successor.Packet lower current)
 (current : L.Current) (k : Nat) :
 A.parentAdvance lower packetAt k (packetAt current).targetCurrent=
 A.parentAdvance lower packetAt (k+1) current := by
 induction k with
 | zero => rfl
 | succ k prior => exact congrArg (fun c => (packetAt c).targetCurrent) prior

private theorem advance_shift (cursor : O.Cursor (PhysicalValue:=V) (PhysicalVar:=X) (sort:=s)) (k : Nat) :
 cursor.next.advance k=cursor.advance (k+1) := by
 induction k with
 | zero=>rfl
 | succ k prior=>exact congrArg (fun c=>c.next) prior

variable (cursor : O.Cursor (PhysicalValue:=V) (PhysicalVar:=X) (sort:=s))
theorem physical_prefix (k : Nat) :
 P.physical (cursor.advance k)=cursor.environment
  (cursor.old.emitted (A.parentAdvance cursor.old cursor.packetAt k cursor.current.1)) := by
 induction k generalizing cursor with
 | zero => rfl
 | succ k prior =>
   rw [←advance_shift]
   unfold SourceOperationInquiry.Context.Native.Orbit.Installation.Cursor.next
   cases selected : cursor.action with
   | inr paid =>
     rw [prior]
     change cursor.environment (cursor.old.emitted
       (A.parentAdvance cursor.old cursor.packetAt k (cursor.packetAt cursor.current.1).targetCurrent))=_
     exact congrArg (fun c => cursor.environment (cursor.old.emitted c))
       (parent_shift cursor.old cursor.packetAt cursor.current.1 k)
   | inl settled =>
     rw [prior]
     change cursor.environment (cursor.old.emitted
       (A.registeredAdvance cursor.old cursor.registered cursor.packetAt k
        (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.targetCurrent
         cursor.registered cursor.packetAt cursor.current)).1)=_
     rw [A.registered_parent_prefix]
     exact congrArg (fun c => cursor.environment (cursor.old.emitted c))
       (parent_shift cursor.old cursor.packetAt cursor.current.1 k)

variable (binding : ∀t,X t→Expr V X t)
def parentPair (k : Nat) :=
 let base := cursor.environment (cursor.old.emitted (A.parentAdvance cursor.old cursor.packetAt k cursor.current.1))
 pairEnvironment base (SourceSubstitution.sourceEnvironment binding base-base)
theorem pair_prefix (k : Nat) : P.pair binding (cursor.advance k)=parentPair cursor binding k :=
 congrArg (fun base=>pairEnvironment base (SourceSubstitution.sourceEnvironment binding base-base))
  (physical_prefix cursor k)
theorem source_parent_fibre (left right : Formal ℤ (PairValue V) X s) :
 P.source binding cursor left=P.source binding cursor right ↔
 ∀k,evaluation (R:=ℤ) (parentPair cursor binding k) left=evaluation (R:=ℤ) (parentPair cursor binding k) right := by
 rw [P.source_fibre]
 simp only [pair_prefix]
end Lower.SourceFamily.Foresight.Contextual.Profile.Origin
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
