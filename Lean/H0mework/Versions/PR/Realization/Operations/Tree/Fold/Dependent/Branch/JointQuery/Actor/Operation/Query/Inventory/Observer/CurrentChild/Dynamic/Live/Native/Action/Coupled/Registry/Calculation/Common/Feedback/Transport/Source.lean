import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Source
import H0mework.Realization.Operations.Execution.Substitution.Source
import H0mework.Versions.PR.Realization.Operations.Relations.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Transport
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
namespace Square
variable {S : Type u} {Value Var : S → Type u} [∀ slot,AddCommGroup (Value slot)]
variable (binding : ∀ slot,Var slot → Expr Value Var slot) (old : Env Value Var)
theorem generated : SourceSubstitution.sourceEnvironment (fun slot name => liftExpr (binding slot name))
 (pairEnvironment old (SourceSubstitution.sourceEnvironment binding old-old))=
 pairEnvironment (SourceSubstitution.sourceEnvironment binding old)
 (SourceSubstitution.sourceEnvironment binding (SourceSubstitution.sourceEnvironment binding old)-
 SourceSubstitution.sourceEnvironment binding old) := by
 funext slot name
 change (liftExpr (binding slot name)).eval
   (pairEnvironment old (SourceSubstitution.sourceEnvironment binding old-old))=_
 rw [eval_liftExpr]
 apply Prod.ext
 · rfl
 · have source := Expr.eval_update (binding slot name) old (SourceSubstitution.sourceEnvironment binding old-old)
   rw [add_sub_cancel] at source
   change (binding slot name).effect old (SourceSubstitution.sourceEnvironment binding old-old)=
    (binding slot name).eval (SourceSubstitution.sourceEnvironment binding old)-(binding slot name).eval old
   rw [source]
   exact (add_sub_cancel_left ((binding slot name).eval old)
    ((binding slot name).effect old (SourceSubstitution.sourceEnvironment binding old-old))).symm
end Square
namespace F
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback
 (raw nextQueryEnv nextTrace)
end F
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
 (PhysicalValue LowValue LowVar sort lowBinding pairBinding actualEnvironment physicalNext)
end Act
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
local instance queryFamily : ∀ slot,AddCommGroup (PairValue (Act.LowValue root visit rec) slot) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ.instQueryValue root visit rec 1
local instance querySlot : AddCommGroup (PairValue (Act.LowValue root visit rec) (Act.sort root rec)) :=
 queryFamily root visit rec (Act.sort root rec)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))

theorem actual_binding_square : SourceSubstitution.sourceEnvironment (Act.pairBinding root visit rec)
 (F.raw root visit rec U7 calculus anchor sourceStage stage frame actual).environment=
 F.nextQueryEnv root visit rec frame actual :=
 Square.generated (Act.lowBinding root visit rec) (Act.actualEnvironment root visit rec frame actual)

def sourceNextTrace := execution
 (SourceSubstitution.sourceEnvironment (Act.pairBinding root visit rec)
 (F.raw root visit rec U7 calculus anchor sourceStage stage frame actual).environment)
 (F.raw root visit rec U7 calculus anchor sourceStage stage frame actual).expression
def pulledTrace := (sourceNextTrace root visit rec U7 calculus anchor sourceStage stage frame actual).substitutedTrace
 (Act.pairBinding root visit rec) (F.raw root visit rec U7 calculus anchor sourceStage stage frame actual).environment
def retained := (actual,F.nextTrace root visit rec U7 calculus anchor sourceStage stage frame actual,
 pulledTrace root visit rec U7 calculus anchor sourceStage stage frame actual)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
