import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Pair.Source
import H0mework.Realization.Operations.Execution.Cochain.Inventory
set_option autoImplicit false
noncomputable section
universe u z
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Pair.Mixed
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
def environment (state : runtime.State) := mixedEnvironment
 (Pair.environment runtime source (SourceOperationInquiry.point runtime state))
 (Pair.environment runtime source (SourceOperationInquiry.point runtime state.tick.nextState-SourceOperationInquiry.point runtime state))
def binding : ∀ sort,ChangedVar (Orbit.Var Var) sort → Expr (PairValue Value) (ChangedVar (Orbit.Var Var)) sort :=
 fun _ name => .var ((name.1.1+1,name.1.2),name.2)
theorem binding_next (state : runtime.State) :
 (fun sort name => (binding (Value:=Value) (Var:=Var) sort name).eval (environment runtime source state))=
 environment runtime source state.tick.nextState := by
 funext sort name
 cases part : name.2 with
 | old =>
  have h := congrArg (fun env : Env (PairValue Value) (Orbit.Var Var) => env sort name.1)
   (Pair.binding_point runtime source state)
  change (Pair.environment runtime source (SourceOperationInquiry.point runtime state)) sort (name.1.1+1,name.1.2)=_ at h
  simpa only [binding,Expr.eval,environment,mixedEnvironment,part] using h
 | increment =>
  have h := congrArg (fun env : Env (PairValue Value) (Orbit.Var Var) => env sort name.1)
   (Pair.binding_difference runtime source state)
  change (Pair.environment runtime source (SourceOperationInquiry.point runtime state.tick.nextState-SourceOperationInquiry.point runtime state))
   sort (name.1.1+1,name.1.2)=_ at h
  simpa only [binding,Expr.eval,environment,mixedEnvironment,part] using h

def vectorBinding (Index : Type z) : ∀ sort,ChangedVar (Orbit.Var Var) sort →
 Expr (SourceOperationExecution.InventoryVector.VectorValue Index (Value:=PairValue Value)) (ChangedVar (Orbit.Var Var)) sort :=
 fun _ name => .var ((name.1.1+1,name.1.2),name.2)
theorem vector_next (Index : Type z) (state : runtime.State) :
 (fun sort name => (vectorBinding (Value:=Value) (Var:=Var) Index sort name).eval
  (SourceOperationExecution.InventoryVector.environment Index (environment runtime source state)))=
 SourceOperationExecution.InventoryVector.environment Index (environment runtime source state.tick.nextState) := by
 funext sort name index
 have h := congrArg (fun env : Env (PairValue Value) (ChangedVar (Orbit.Var Var)) => env sort name)
  (binding_next runtime source state)
 exact h
end SourceOperationInquiry.Context.Native.Orbit.Pair.Mixed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
