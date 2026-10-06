import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Iteration.Current
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Finite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
def depth {target : S} : Expr Value (Orbit.Var Var) target → Nat
 | .var name => name.1
 | .const _ => 0
 | .add first second => max (depth first) (depth second)
 | .linear _ argument => depth argument
 | .bilinear _ first second => max (depth first) (depth second)
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
theorem action_power_point (offset count : Nat) :
 (SourceOperationInquiry.sourceAction runtime ^ count) (SourceOperationInquiry.point runtime (runtime.stateAt offset))=
 SourceOperationInquiry.point runtime (runtime.stateAt (offset+count)) := by
 induction count with
 | zero => rfl
 | succ count previous =>
  rw [pow_succ',Module.End.mul_apply,previous,SourceOperationInquiry.point_action]
  rfl
theorem variable_read (offset : Nat) (target : S) (name : Orbit.Var Var target) :
 Orbit.environment runtime source (SourceOperationInquiry.point runtime (runtime.stateAt offset)) target name=
 readEnv runtime source (runtime.stateAt (offset+name.1)) target name.2 := by
 change Context.environment runtime source
  ((SourceOperationInquiry.sourceAction runtime ^ name.1) (SourceOperationInquiry.point runtime (runtime.stateAt offset))) target name.2=_
 rw [action_power_point,Context.environment_point]
def old (offset : Nat) : Env Value (Orbit.Var Var) := fun target name =>
 readEnv runtime source (runtime.stateAt (offset+name.1)) target name.2
def increment (offset : Nat) : Env Value (Orbit.Var Var) := fun target name =>
 readEnv runtime source (runtime.stateAt (offset+name.1+1)) target name.2-
 readEnv runtime source (runtime.stateAt (offset+name.1)) target name.2
theorem old_source (offset : Nat) : old runtime source offset=
 Pairing.Orbit.old runtime source (runtime.stateAt offset) := by
 funext target name
 exact (variable_read runtime source offset target name).symm
theorem increment_source (offset : Nat) : increment runtime source offset=
 Pairing.Orbit.increment runtime source (runtime.stateAt offset) := by
 funext target name
 change _=Orbit.environment runtime source
  (SourceOperationInquiry.point runtime (runtime.stateAt offset).tick.nextState-SourceOperationInquiry.point runtime (runtime.stateAt offset)) target name
 rw [map_sub]
 change _=Orbit.environment runtime source (SourceOperationInquiry.point runtime (runtime.stateAt (offset+1))) target name-
  Orbit.environment runtime source (SourceOperationInquiry.point runtime (runtime.stateAt offset)) target name
 rw [variable_read,variable_read]
 have shifted : offset+1+name.1=offset+name.1+1 := by omega
 rw [shifted]
 rfl
theorem bounded_pair (expression : Expr Value (Orbit.Var Var) slot)
 (old first second increment : Env Value (Orbit.Var Var))
 (sameOld : ∀ target (name : Orbit.Var Var target),name.1≤depth expression → first target name=old target name)
 (sameIncrement : ∀ target (name : Orbit.Var Var target),name.1≤depth expression → second target name=increment target name) :
 (expression.eval first,expression.effect first second)=(expression.eval old,expression.effect old increment) := by
 induction expression with
 | var name => exact Prod.ext (sameOld _ name le_rfl) (sameIncrement _ name le_rfl)
 | const value => rfl
 | add left right ih1 ih2 =>
  have firstRead := ih1
   (fun t n h => sameOld t n (h.trans (Nat.le_max_left _ _)))
   (fun t n h => sameIncrement t n (h.trans (Nat.le_max_left _ _)))
  have secondRead := ih2
   (fun t n h => sameOld t n (h.trans (Nat.le_max_right _ _)))
   (fun t n h => sameIncrement t n (h.trans (Nat.le_max_right _ _)))
  exact congrArg₂ (fun a b : Value _ × Value _ => (a.1+b.1,a.2+b.2)) firstRead secondRead
 | linear op argument ih =>
  have argumentRead := ih sameOld sameIncrement
  exact congrArg (fun a : Value _ × Value _ => (op a.1,op a.2)) argumentRead
 | bilinear op left right ih1 ih2 =>
  have firstRead := ih1
   (fun t n h => sameOld t n (h.trans (Nat.le_max_left _ _)))
   (fun t n h => sameIncrement t n (h.trans (Nat.le_max_left _ _)))
  have secondRead := ih2
   (fun t n h => sameOld t n (h.trans (Nat.le_max_right _ _)))
   (fun t n h => sameIncrement t n (h.trans (Nat.le_max_right _ _)))
  exact congrArg₂ (fun a b : Value _ × Value _ => (op a.1 b.1,op a.1 b.2+op a.2 b.1+op a.2 b.2)) firstRead secondRead
def environments (offset bound : Nat) :=
 List.ofFn (fun index : Fin (bound+2) => readEnv runtime source (runtime.stateAt (offset+index.val)))
def finiteOld (offset bound : Nat) : Env Value (Orbit.Var Var) :=
 fun target name => if bounded : name.1≤bound then
  (environments runtime source offset bound).get ⟨name.1,by simp only [environments,List.length_ofFn]; omega⟩ target name.2 else 0
def finiteIncrement (offset bound : Nat) : Env Value (Orbit.Var Var) :=
 fun target name => if bounded : name.1≤bound then
  (environments runtime source offset bound).get ⟨name.1+1,by simp only [environments,List.length_ofFn]; omega⟩ target name.2-
   (environments runtime source offset bound).get ⟨name.1,by simp only [environments,List.length_ofFn]; omega⟩ target name.2 else 0
theorem finite_old (offset bound : Nat) (target : S)
 (name : Orbit.Var Var target) (bounded : name.1≤bound) :
 finiteOld runtime source offset bound target name=old runtime source offset target name := by
 simp only [finiteOld,dif_pos bounded,environments,List.get_ofFn]
 rfl
theorem finite_increment (offset bound : Nat) (target : S)
 (name : Orbit.Var Var target) (bounded : name.1≤bound) :
 finiteIncrement runtime source offset bound target name=increment runtime source offset target name := by
 simp only [finiteIncrement,dif_pos bounded,environments,List.get_ofFn]
 rfl
theorem finite_pair_bound (expression : Expr Value (Orbit.Var Var) slot) (offset bound : Nat)
 (bounded : depth expression≤bound) :
 (expression.eval (finiteOld runtime source offset bound),
  expression.effect (finiteOld runtime source offset bound) (finiteIncrement runtime source offset bound))=
 (expression.eval (Pairing.Orbit.old runtime source (runtime.stateAt offset)),
  expression.effect (Pairing.Orbit.old runtime source (runtime.stateAt offset))
   (Pairing.Orbit.increment runtime source (runtime.stateAt offset))) :=
 (bounded_pair expression (old runtime source offset) (finiteOld runtime source offset bound)
  (finiteIncrement runtime source offset bound) (increment runtime source offset)
  (fun t n h => finite_old runtime source offset bound t n (h.trans bounded))
  (fun t n h => finite_increment runtime source offset bound t n (h.trans bounded))).trans
  (congrArg₂ (fun old change => (expression.eval old,expression.effect old change))
   (old_source runtime source offset) (increment_source runtime source offset))
theorem finite_pair (expression : Expr Value (Orbit.Var Var) slot) (offset : Nat) :
 type_of% (finite_pair_bound runtime source expression offset (depth expression) le_rfl) :=
 finite_pair_bound runtime source expression offset (depth expression) le_rfl
abbrev receipt (expression : Expr Value (Orbit.Var Var) slot) (offset : Nat) (index : Fin (depth expression+1)) :=
 SourceOperationInquiry.actual_next_receipt runtime (offset+index.val)
end SourceOperationInquiry.Context.Native.Orbit.Finite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
