import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Iteration
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Pairing.Orbit
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
private theorem source_pair (seed : Expr Value (O.Var Var) slot) (state : runtime.State) :
 ((seed.subst O.binding).eval (old runtime source state),(seed.subst O.binding).effect
  (old runtime source state) (increment runtime source state))=
 (seed.eval (old runtime source state.tick.nextState),seed.effect
  (old runtime source state.tick.nextState) (increment runtime source state.tick.nextState)) := by
 rw [Expr.eval_subst,Expr.effect_subst]
 have first : (fun target name => (O.binding target name).eval (old runtime source state))=
   old runtime source state.tick.nextState := O.binding_point runtime source state
 have second : (fun target name => (O.binding target name).effect (old runtime source state) (increment runtime source state))=
   increment runtime source state.tick.nextState := O.binding_difference runtime source state
 exact congrArg₂ (fun environment delta => (seed.eval environment,seed.effect environment delta)) first second
theorem iterate_current (seed : Expr Value (O.Var Var) slot) (depth count : Nat) :
 ((iterate seed count).eval (old runtime source (runtime.stateAt depth)),(iterate seed count).effect
  (old runtime source (runtime.stateAt depth)) (increment runtime source (runtime.stateAt depth)))=
 (seed.eval (old runtime source (runtime.stateAt (depth+count))),seed.effect
  (old runtime source (runtime.stateAt (depth+count))) (increment runtime source (runtime.stateAt (depth+count)))) := by
 induction count generalizing depth with
 | zero => rfl
 | succ count previous =>
  change (((iterate seed count).subst O.binding).eval _,((iterate seed count).subst O.binding).effect _ _)=_
  have step := source_pair runtime source (iterate seed count) (runtime.stateAt depth)
  change _=(seed.eval (old runtime source (runtime.stateAt (depth+(count+1)))),seed.effect
   (old runtime source (runtime.stateAt (depth+(count+1)))) (increment runtime source (runtime.stateAt (depth+(count+1)))))
  have equal : depth+1+count=depth+(count+1) := by omega
  exact step.trans ((previous (depth+1)).trans (congrArg (fun n =>
   (seed.eval (old runtime source (runtime.stateAt n)),seed.effect (old runtime source (runtime.stateAt n))
    (increment runtime source (runtime.stateAt n)))) equal))
end SourceOperationInquiry.Context.Native.Pairing.Orbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
