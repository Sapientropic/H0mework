import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Source
import H0mework.Realization.Operations.Execution.Substitution.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Pair
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
def environment : SourceOperationInquiry.Carrier runtime →+ Env (PairValue Value) (Orbit.Var Var) where
 toFun material := pairEnvironment (Orbit.environment runtime source material)
  (Orbit.environment runtime source (SourceOperationInquiry.sourceAction runtime material-material))
 map_zero' := by
  funext sort name
  simp only [map_zero,sub_self]
  rfl
 map_add' left right := by
  funext sort name
  change (Orbit.environment runtime source (left+right) sort name,
   Orbit.environment runtime source (SourceOperationInquiry.sourceAction runtime (left+right)-(left+right)) sort name)=_
  rw [map_add,map_add]
  have h : SourceOperationInquiry.sourceAction runtime left+SourceOperationInquiry.sourceAction runtime right-(left+right)=
   (SourceOperationInquiry.sourceAction runtime left-left)+(SourceOperationInquiry.sourceAction runtime right-right) := by abel
  rw [h,map_add]
  rfl
theorem action (material : SourceOperationInquiry.Carrier runtime) :
 (fun sort name => (Orbit.binding (PhysicalValue:=PairValue Value) (PhysicalVar:=Var) sort name).eval
  (environment runtime source material))=environment runtime source (SourceOperationInquiry.sourceAction runtime material) := by
 funext sort name
 change (Orbit.environment runtime source material sort (name.1+1,name.2),
  Orbit.environment runtime source (SourceOperationInquiry.sourceAction runtime material-material) sort (name.1+1,name.2))=_
 have first := congrArg (fun env : Env Value (Orbit.Var Var) => env sort name)
  (Orbit.binding_eval runtime source material)
 have second := congrArg (fun env : Env Value (Orbit.Var Var) => env sort name)
  (Orbit.binding_eval runtime source (SourceOperationInquiry.sourceAction runtime material-material))
 change Orbit.environment runtime source material sort (name.1+1,name.2)=_ at first
 change Orbit.environment runtime source (SourceOperationInquiry.sourceAction runtime material-material) sort (name.1+1,name.2)=_ at second
 rw [first,second,map_sub]
 rfl
theorem point (state : runtime.State) (sort : S) (name : Var sort) :
 environment runtime source (SourceOperationInquiry.point runtime state) sort (0,name)=
 SourceOperationInquiry.Context.pairEnvironmentAt runtime source state sort name := by
 change (Orbit.environment runtime source (SourceOperationInquiry.point runtime state) sort (0,name),
  Orbit.environment runtime source (SourceOperationInquiry.sourceAction runtime (SourceOperationInquiry.point runtime state)-
   SourceOperationInquiry.point runtime state) sort (0,name))=_
 rw [Orbit.environment_point,SourceOperationInquiry.point_action,map_sub]
 change (SourceOperationInquiry.Context.readEnv runtime source state sort name,
  Orbit.environment runtime source (SourceOperationInquiry.point runtime state.tick.nextState) sort (0,name)-
   Orbit.environment runtime source (SourceOperationInquiry.point runtime state) sort (0,name))=_
 rw [Orbit.environment_point,Orbit.environment_point]
 rfl
theorem binding_point (state : runtime.State) :
 (fun sort name => (Orbit.binding (PhysicalValue:=PairValue Value) (PhysicalVar:=Var) sort name).eval
  (environment runtime source (SourceOperationInquiry.point runtime state)))=
 environment runtime source (SourceOperationInquiry.point runtime state.tick.nextState) :=
 (action runtime source _).trans (congrArg (environment runtime source) (SourceOperationInquiry.point_action runtime state))
def embedding : ∀ sort, Var sort → Expr (PairValue Value) (Orbit.Var Var) sort :=
 fun _ name => .var (0,name)
theorem embedding_point (state : runtime.State) :
 (fun sort name => (embedding (Value:=Value) (Var:=Var) sort name).eval
  (environment runtime source (SourceOperationInquiry.point runtime state)))=
 SourceOperationInquiry.Context.pairEnvironmentAt runtime source state := by
 funext sort name
 exact point runtime source state sort name

def embeddedTrace (state : runtime.State) {sort : S} {before after : Expr (PairValue Value) Var sort}
 (trace : Trace (SourceOperationInquiry.Context.pairEnvironmentAt runtime source state) before after) :
 Trace (environment runtime source (SourceOperationInquiry.point runtime state))
  (before.subst embedding) (after.subst embedding) :=
 Trace.substitutedTrace embedding _ (by rw [embedding_point]; exact trace)
theorem binding_difference (state : runtime.State) :
 (fun sort name => (Orbit.binding (PhysicalValue:=PairValue Value) (PhysicalVar:=Var) sort name).effect
  (environment runtime source (SourceOperationInquiry.point runtime state))
  (environment runtime source (SourceOperationInquiry.point runtime state.tick.nextState-SourceOperationInquiry.point runtime state)))=
 environment runtime source (SourceOperationInquiry.point runtime state.tick.nextState.tick.nextState-SourceOperationInquiry.point runtime state.tick.nextState) := by
 funext sort name
 change environment runtime source (SourceOperationInquiry.point runtime state.tick.nextState-SourceOperationInquiry.point runtime state) sort (name.1+1,name.2)=_
 have a := congrArg (fun env : Env (PairValue Value) (Orbit.Var Var) => env sort name)
  (action runtime source (SourceOperationInquiry.point runtime state.tick.nextState-SourceOperationInquiry.point runtime state))
 change environment runtime source (SourceOperationInquiry.point runtime state.tick.nextState-SourceOperationInquiry.point runtime state) sort (name.1+1,name.2)=_ at a
 rw [a,map_sub,SourceOperationInquiry.point_action,SourceOperationInquiry.point_action]
end SourceOperationInquiry.Context.Native.Orbit.Pair
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
