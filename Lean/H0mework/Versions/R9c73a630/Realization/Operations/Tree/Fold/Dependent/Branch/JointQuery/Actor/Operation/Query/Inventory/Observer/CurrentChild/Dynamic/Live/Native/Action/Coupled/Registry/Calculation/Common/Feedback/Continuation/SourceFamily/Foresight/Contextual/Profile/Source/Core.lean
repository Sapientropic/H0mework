import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Renderer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Source
import H0mework.Realization.ObservationActions.Algebraic
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.SourceCore
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (Cursor cursorAt)
end O
namespace C
export Lower.SourceFamily.Foresight.Contextual (sourceEnvironment projection_environment low request)
end C
namespace I
export Lower.SourceFamily.Foresight.Installed (nativeState sourceHigh epochIndex OccurrenceIndex)
end I
section Profile
variable {S : Type u} {V X : S→Type u} [∀t,AddCommGroup (V t)] {s:S}
variable (sigma : ∀t,X t→Expr V X t)
variable (cursor : O.Cursor (PhysicalValue:=V) (PhysicalVar:=X) (sort:=s))
def physical := cursor.environment (cursor.old.emitted cursor.current.1)
def pair := pairEnvironment (physical cursor)
 (SourceSubstitution.sourceEnvironment sigma (physical cursor)-physical cursor)
def carry : (k:Nat)→Formal ℤ (PairValue V) X s→ₗ[ℤ]Formal ℤ (PairValue V) X s :=fun _=>LinearMap.id
def read (k:Nat) := evaluation (R:=ℤ) (s:=s) (pair sigma (cursor.advance k))
def source := AlgebraicDependent.sourceMap (carry (V:=V) (X:=X) (s:=s)) (read sigma cursor) 0
private theorem carry_advance (k:Nat) :
 AlgebraicDependent.advance (carry (V:=V) (X:=X) (s:=s)) 0 k=LinearMap.id :=by
 induction k with
 | zero=>rfl
 | succ k previous=>
  change LinearMap.id.comp (AlgebraicDependent.advance (carry (V:=V) (X:=X) (s:=s)) 0 k)=_
  rw [previous,LinearMap.id_comp]
theorem source_fibre (left right:Formal ℤ (PairValue V) X s) :
 source sigma cursor left=source sigma cursor right ↔
 ∀k,evaluation (R:=ℤ) (pair sigma (cursor.advance k)) left=evaluation (R:=ℤ) (pair sigma (cursor.advance k)) right :=by
 have original:=AlgebraicDependent.source_fibre (carry (V:=V) (X:=X) (s:=s)) (read sigma cursor) 0 left right
 simpa only [source,Nat.zero_add,carry_advance,LinearMap.id_apply,read] using original
private theorem advance_shift (k:Nat) : cursor.next.advance k=cursor.advance (k+1) :=by
 induction k with
 | zero=>rfl
 | succ k previous=>exact congrArg (fun c=>c.next) previous
def increment:=pair sigma cursor.next-pair sigma cursor
theorem source_effect (word:Formal ℤ (PairValue V) X s) :
 evaluation (R:=ℤ) (pair sigma cursor.next) word=
 evaluation (R:=ℤ) (pair sigma cursor) word+effectEvaluator (R:=ℤ) (pair sigma cursor) (increment sigma cursor) word :=
 (congrArg (fun env=>evaluation (R:=ℤ) env word) (add_sub_cancel (pair sigma cursor) (pair sigma cursor.next)).symm).trans
 (LinearMap.congr_fun (evaluation_update (R:=ℤ) (pair sigma cursor) (increment sigma cursor)) word)
end Profile
variable {S : Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (index:I.OccurrenceIndex n frame)
abbrev sigma:=Future.Replay.Binding.at binding n
abbrev nativeCursor:=O.cursorAt frame index.2
abbrev profile:=source (sigma binding n) (nativeCursor n frame index)
def nativeSource := (I.sourceHigh binding n seed frame).2.2.2.1 s
local instance nativeModule :Module ℤ (Lower.SourceFamily.Foresight.Model binding (I.nativeState n seed frame) s 0):=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding (I.nativeState n seed frame) s 0)).module
local instance jointModule : Module ℤ
 ((AlgebraicDependent.completion (carry (V:=Lower.Value W n) (X:=X) (s:=s))
   (read (sigma binding n) (nativeCursor n frame index)) 0) ×
  Lower.SourceFamily.Foresight.Model binding (I.nativeState n seed frame) s 0) := Prod.instModule
def jointSource := (profile binding n frame index).prod (nativeSource binding n seed frame)
def sourceTags := (index,I.epochIndex n frame)
theorem joint_renderer (word : Formal ℤ (PairValue (Lower.Value W n)) X s) :
 jointSource binding n seed frame index (Finsupp.single (Coefficients.expression word) 1)=
 jointSource binding n seed frame index word :=by
 apply Prod.ext
 · exact (source_fibre (sigma binding n) (nativeCursor n frame index) _ _).mpr fun k=>
    Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.rendered_semantics word _
 · exact Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.rendered_source binding
    (I.nativeState n seed frame) s 0 word
theorem joint_scope_renderer (word : Formal ℤ (PairValue (Lower.Value W n)) X s) :
 SourceOperationLogic.q (jointSource binding n seed frame index) (Finsupp.single (Coefficients.expression word) 1)=
 SourceOperationLogic.q (jointSource binding n seed frame index) word :=by
 apply (SourceOperationLogic.q_eq_iff _ _ _).mpr
 rw [LinearMap.mem_ker,map_sub]
 exact sub_eq_zero.mpr (joint_renderer binding n seed frame index word)
theorem profile_head : pair (sigma binding n) (nativeCursor n frame index)=C.sourceEnvironment binding n seed frame index :=by
 rw [C.projection_environment]
 rcases index with ⟨current,occurrence⟩
 rcases occurrence with ⟨support,event⟩
 cases event
 rfl
abbrev actionBinding:=Future.Replay.pairBinding (sigma binding n)

theorem joint_semantic (left right:Formal ℤ (PairValue (Lower.Value W n)) X s)
 (same:Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq left right):
 jointSource binding n seed frame index left=jointSource binding n seed frame index right :=by
 apply Prod.ext
 · exact (source_fibre (sigma binding n) (nativeCursor n frame index) left right).mpr (fun k=>same _)
 · exact (Lower.SourceFamily.Foresight.source_fibre binding (I.nativeState n seed frame) s 0 left right).mpr
    (fun k=>Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.semantic_advance
      binding (I.nativeState n seed frame) s 0 left right same k _)
end Lower.SourceFamily.Foresight.Contextual.Profile.SourceCore
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
