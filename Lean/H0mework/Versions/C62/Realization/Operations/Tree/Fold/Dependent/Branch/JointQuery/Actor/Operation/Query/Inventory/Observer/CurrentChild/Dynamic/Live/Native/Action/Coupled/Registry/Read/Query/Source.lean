import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationScalarInventoryLift
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action (PhysicalValue LowValue LowVar sort)
end Act
namespace R
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry (queryInput query)
namespace A
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Activated (runtime process presentationAt queryAt actual_query actual_node)
end A
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Boot (frame programme targetConfiguration)
end B
namespace P
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled (frameAt configuration)
end P
end R
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (GermAt germAt germ_unique datum actualOccurrence resultAt)
end S
end E
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)

def QueryValue : Nat → (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) → Type u
 | 0 => Act.LowValue root visit rec
 | _+1 => PairValue (Act.LowValue root visit rec)
def QueryVar : Nat → (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) → Type u
 | 0 => Act.LowVar root visit rec
 | _+1 => Act.LowVar root visit rec
local instance instQueryValue (count : Nat) : ∀ slot,AddCommGroup (QueryValue root visit rec count slot) := by
 cases count with
 | zero =>
  intro slot
  change AddCommGroup (Act.LowValue root visit rec slot)
  infer_instance
 | succ count =>
  intro slot
  change AddCommGroup (PairValue (Act.LowValue root visit rec) slot)
  infer_instance

def sourceInput : (count : Nat) → SourceNativeRootInquiryInputAt
 (R.A.presentationAt root visit rec U7 calculus anchor sourceStage stage count).state.base.root
 (R.A.presentationAt root visit rec U7 calculus anchor sourceStage stage count).state.base.visit
 (R.A.presentationAt root visit rec U7 calculus anchor sourceStage stage count).Query
 | 0 => R.queryInput (R.B.frame root visit rec U7 calculus anchor sourceStage stage)
  (R.B.programme root visit rec U7 calculus anchor sourceStage)
 | count+1 => R.queryInput (R.P.frameAt root visit rec U7 calculus anchor sourceStage stage count)
  (R.B.targetConfiguration root visit rec U7 calculus anchor sourceStage stage)

def sourceRaw : (count : Nat) → SourceOperationInquiry.Context.Raw
 (PhysicalValue:=QueryValue root visit rec count) (PhysicalVar:=QueryVar root visit rec count)
 (sort:=Act.sort root rec)
 | 0 => (sourceInput root visit rec U7 calculus anchor sourceStage stage 0).query.raw
 | count+1 => (sourceInput root visit rec U7 calculus anchor sourceStage stage (count+1)).query.raw

def paidValue : (count : Nat) → QueryValue root visit rec count (Act.sort root rec)
 | 0 => (E.S.resultAt (R.B.frame root visit rec U7 calculus anchor sourceStage stage)
  (R.B.programme root visit rec U7 calculus anchor sourceStage)
  (E.S.actualOccurrence (R.B.frame root visit rec U7 calculus anchor sourceStage stage))).2.2.1
 | count+1 => (E.S.resultAt (R.P.frameAt root visit rec U7 calculus anchor sourceStage stage count)
  (R.B.targetConfiguration root visit rec U7 calculus anchor sourceStage stage)
  (E.S.actualOccurrence (R.P.frameAt root visit rec U7 calculus anchor sourceStage stage count))).2.2.1

theorem paid_source (count : Nat) : paidValue root visit rec U7 calculus anchor sourceStage stage count=
 (sourceRaw root visit rec U7 calculus anchor sourceStage stage count).expression.eval
 (sourceRaw root visit rec U7 calculus anchor sourceStage stage count).environment := by
 cases count with
 | zero => exact RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
 | succ count => exact RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _

def paidState : (count : Nat) → SourceOperationExecutionDebt.State
 (sourceRaw root visit rec U7 calculus anchor sourceStage stage count).environment
 (sourceRaw root visit rec U7 calculus anchor sourceStage stage count).expression
 | 0 => (E.S.resultAt (R.B.frame root visit rec U7 calculus anchor sourceStage stage)
  (R.B.programme root visit rec U7 calculus anchor sourceStage)
  (E.S.actualOccurrence (R.B.frame root visit rec U7 calculus anchor sourceStage stage))).2.1
 | count+1 => (E.S.resultAt (R.P.frameAt root visit rec U7 calculus anchor sourceStage stage count)
  (R.B.targetConfiguration root visit rec U7 calculus anchor sourceStage stage)
  (E.S.actualOccurrence (R.P.frameAt root visit rec U7 calculus anchor sourceStage stage count))).2.1

theorem paid_trace_length (count : Nat) :
 (paidState root visit rec U7 calculus anchor sourceStage stage count).2.length=
 SourceOperationExecution.remaining (sourceRaw root visit rec U7 calculus anchor sourceStage stage count).expression := by
 cases count with
 | zero => exact RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
 | succ count => exact RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _

theorem source_query (count : Nat) :
 (sourceInput root visit rec U7 calculus anchor sourceStage stage count).query=
 R.A.queryAt root visit rec U7 calculus anchor sourceStage stage count := by
 cases count <;> rfl
theorem actual_source_query (count : Nat) : HEq
 ((R.A.runtime root visit rec U7 calculus anchor sourceStage stage).stateAt count).activation.query
 (sourceInput root visit rec U7 calculus anchor sourceStage stage count).query :=
 (R.A.actual_query root visit rec U7 calculus anchor sourceStage stage count).trans
 (heq_of_eq (source_query root visit rec U7 calculus anchor sourceStage stage count).symm)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
