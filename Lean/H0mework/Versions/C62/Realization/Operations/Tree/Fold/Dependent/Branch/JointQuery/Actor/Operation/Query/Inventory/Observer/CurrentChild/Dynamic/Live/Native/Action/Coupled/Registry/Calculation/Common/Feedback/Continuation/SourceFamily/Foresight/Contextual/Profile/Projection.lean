import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Tail
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Projection
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (ofFrame)
end O
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (physical pair)
end P
namespace Curve
export Lower.SourceFamily.Foresight.Contextual.Profile.Curve (replay_physical_prefix)
end Curve
namespace F
export Lower.SourceFamily.Foresight (stage value cfg frame environment Word action read data)
end F
namespace L
export Lower.SourceFamily.Foresight.Tail (State tail)
end L
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (state:L.State (W:=W) (X:=X) (s:=s))
def profileEnvironment (k j:Nat) := P.pair (Future.Replay.Binding.at binding (F.stage binding state k))
 ((O.ofFrame (F.frame binding state k)).advance j)
def projection (t:S) : (k:Nat)→PairValue (F.value binding state k) t→ₗ[ℤ]PairValue (F.value binding state 0) t :=
 Nat.rec (motive:=fun k=>PairValue (F.value binding state k) t→ₗ[ℤ]PairValue (F.value binding state 0) t)
 LinearMap.id (fun k prior=>prior.comp (LinearMap.fst ℤ
  (PairValue (F.value binding state k) t) (PairValue (F.value binding state k) t)))

theorem first_profile (k j:Nat) :
 (fun t x=>(profileEnvironment binding state (k+1) j t x).1)=profileEnvironment binding state k (j+1) :=
 Curve.replay_physical_prefix binding (F.stage binding state k)
  (L.tail binding state k).2.2 (F.frame binding state k) j

theorem projected_profile (k j:Nat) (t:S) (name:X t) :
 projection binding state t k (profileEnvironment binding state k j t name)=
 profileEnvironment binding state 0 (k+j) t name :=by
 induction k generalizing j with
 | zero=>exact congrArg (fun z=>profileEnvironment binding state 0 z t name) (Nat.zero_add j).symm
 | succ k prior=>
  have generated:=congrFun (congrFun (first_profile binding state k j) t) name
  have step:=congrArg (projection binding state t k) generated
  exact step.trans ((prior (j+1)).trans
   (congrArg (fun z=>profileEnvironment binding state 0 z t name) (by omega : k+(j+1)=(k+1)+j)))

theorem head_profile (k:Nat) : F.environment binding state k=profileEnvironment binding state k 0 :=
 congrArg (fun raw=>raw.environment) (Lower.SourceFamily.Replay.factory_raw binding
  (F.stage binding state k) (L.tail binding state k).2.2 (F.frame binding state k))

private theorem lift_first {V:S→Type u} [∀t,AddCommGroup (V t)]
 (t:S) (env:Env (PairValue V) X) (word:Formal ℤ V X t) :
 (evaluation (R:=ℤ) env (liftMap word)).1=evaluation (R:=ℤ) (fun a x=>(env a x).1) word :=
 congrArg (fun point=>point.1) (LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=t)
  (fun a x=>(env a x).1) (fun a x=>(env a x).2)) word)

def advancedMap (t:S) (k:Nat) : F.Word binding state t 0→ₗ[ℤ]F.Word binding state t k :=
 (AlgebraicDependent.familyCast (R:=ℤ) (C:=F.Word binding state t) (Nat.zero_add k)).comp
  (AlgebraicDependent.advance (F.action binding state t) 0 k)
private theorem advanced_zero (t:S) (word:F.Word binding state t 0) : advancedMap binding state t 0 word=word :=rfl
private theorem advanced_succ (t:S) (k:Nat) (word:F.Word binding state t 0) :
 advancedMap binding state t (k+1) word=liftMap (advancedMap binding state t k word) :=
 LinearMap.congr_fun (AlgebraicDependent.cast_action (F.action binding state t) (Nat.zero_add k))
  (AlgebraicDependent.advance (F.action binding state t) 0 k word)

theorem projected_evaluation (t:S) (k:Nat) (env:Env (PairValue (F.value binding state k)) X)
 (word:F.Word binding state t 0) :
 projection binding state t k (evaluation (R:=ℤ) env (advancedMap binding state t k word))=
 evaluation (R:=ℤ) (fun a x=>projection binding state a k (env a x)) word :=by
 induction k with
 | zero=>rfl
 | succ k prior=>
  have emitted:=congrArg (fun current=>projection binding state t (k+1) (evaluation (R:=ℤ) env current))
   (advanced_succ binding state t k word)
  have effect:=congrArg (projection binding state t k)
   (lift_first t env (advancedMap binding state t k word))
  exact emitted.trans (effect.trans (prior (fun a x=>(env a x).1)))

theorem source_read_square (t:S) (k:Nat) (word:F.Word binding state t 0) :
 projection binding state t k (F.read binding state t k (advancedMap binding state t k word))=
 evaluation (R:=ℤ) (profileEnvironment binding state 0 k) word :=by
 have old:=projected_evaluation binding state t k (F.environment binding state k) word
 have generated : (fun a x=>projection binding state a k (F.environment binding state k a x))=
   profileEnvironment binding state 0 k :=by
  funext a x
  exact (congrArg (fun env=>projection binding state a k (env a x)) (head_profile binding state k)).trans
   (projected_profile binding state k 0 a x)
 exact old.trans (congrArg (fun env=>evaluation (R:=ℤ) env word) generated)
end Lower.SourceFamily.Foresight.Contextual.Profile.Projection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
