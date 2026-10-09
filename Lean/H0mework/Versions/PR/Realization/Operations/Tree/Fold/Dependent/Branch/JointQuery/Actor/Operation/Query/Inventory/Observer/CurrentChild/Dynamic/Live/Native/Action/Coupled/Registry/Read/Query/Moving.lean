import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Query.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Query.Difference
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)

namespace Relation
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable (offset : Nat)
abbrev Value := PairValue (Act.LowValue root visit rec)
abbrev Variable := Act.LowVar root visit rec
local instance tailFamilyGroup : ∀ slot,AddCommGroup (Value root visit rec slot) :=
 instQueryValue root visit rec 1
local instance tailSlotGroup : AddCommGroup (Value root visit rec (Act.sort root rec)) :=
 tailFamilyGroup root visit rec (Act.sort root rec)
def tailRaw (count : Nat) : SourceOperationInquiry.Context.Raw
 (PhysicalValue:=Value root visit rec) (PhysicalVar:=Variable root visit rec) (sort:=Act.sort root rec) :=
 sourceRaw root visit rec U7 calculus anchor sourceStage stage (count+1)
abbrev currentRaw := tailRaw root visit rec U7 calculus anchor sourceStage stage offset
abbrev nextRaw := tailRaw root visit rec U7 calculus anchor sourceStage stage (offset+1)
def tailPaid (count : Nat) : Value root visit rec (Act.sort root rec) :=
 paidValue root visit rec U7 calculus anchor sourceStage stage (count+1)

def deltaWord : Formal ℤ (Value root visit rec) (Variable root visit rec) (Act.sort root rec) :=
 Finsupp.single (nextRaw root visit rec U7 calculus anchor sourceStage stage offset).expression 1-
 Finsupp.single (currentRaw root visit rec U7 calculus anchor sourceStage stage offset).expression 1
def deltaExpression := SourceOperationInquiry.Context.Faces.Execution.expression
 (deltaWord root visit rec U7 calculus anchor sourceStage stage offset)
def deltaRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=Value root visit rec) (Var:=Variable root visit rec) (sort:=Act.sort root rec) :=
 ⟨(nextRaw root visit rec U7 calculus anchor sourceStage stage offset).environment,
  deltaExpression root visit rec U7 calculus anchor sourceStage stage offset⟩
def deltaTrace := SourceOperationExecution.execution
 (deltaRaw root visit rec U7 calculus anchor sourceStage stage offset).environment
 (deltaRaw root visit rec U7 calculus anchor sourceStage stage offset).expression

def increment := (nextRaw root visit rec U7 calculus anchor sourceStage stage offset).environment-
 (currentRaw root visit rec U7 calculus anchor sourceStage stage offset).environment

theorem delta_eval : (deltaRaw root visit rec U7 calculus anchor sourceStage stage offset).expression.eval
 (deltaRaw root visit rec U7 calculus anchor sourceStage stage offset).environment=
 (nextRaw root visit rec U7 calculus anchor sourceStage stage offset).expression.eval
 (nextRaw root visit rec U7 calculus anchor sourceStage stage offset).environment-
 (currentRaw root visit rec U7 calculus anchor sourceStage stage offset).expression.eval
 (nextRaw root visit rec U7 calculus anchor sourceStage stage offset).environment :=
 Lower.delta_eval (W:=Value root visit rec) (X:=Variable root visit rec) (s:=Act.sort root rec)
  (currentRaw root visit rec U7 calculus anchor sourceStage stage offset)
  (nextRaw root visit rec U7 calculus anchor sourceStage stage offset)

theorem moving_paid : type_of% (Lower.moving_paid (W:=Value root visit rec) (X:=Variable root visit rec) (s:=Act.sort root rec)
 (currentRaw root visit rec U7 calculus anchor sourceStage stage offset)
 (nextRaw root visit rec U7 calculus anchor sourceStage stage offset)
 (tailPaid root visit rec U7 calculus anchor sourceStage stage offset)
 (tailPaid root visit rec U7 calculus anchor sourceStage stage (offset+1))
 (paid_source root visit rec U7 calculus anchor sourceStage stage (offset+1))
 (paid_source root visit rec U7 calculus anchor sourceStage stage (offset+2))) :=
 Lower.moving_paid (W:=Value root visit rec) (X:=Variable root visit rec) (s:=Act.sort root rec)
 (currentRaw root visit rec U7 calculus anchor sourceStage stage offset)
 (nextRaw root visit rec U7 calculus anchor sourceStage stage offset)
 (tailPaid root visit rec U7 calculus anchor sourceStage stage offset)
 (tailPaid root visit rec U7 calculus anchor sourceStage stage (offset+1))
 (paid_source root visit rec U7 calculus anchor sourceStage stage (offset+1))
 (paid_source root visit rec U7 calculus anchor sourceStage stage (offset+2))

theorem delta_trace_cost : (deltaTrace root visit rec U7 calculus anchor sourceStage stage offset).length=
 SourceOperationExecution.remaining (deltaRaw root visit rec U7 calculus anchor sourceStage stage offset).expression :=
 SourceOperationExecution.execution_length _ _
end Relation
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
