import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Projection
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Naturality
namespace E
export Lower.SourceFamily.Foresight.Contextual.Profile.Projection (projection profileEnvironment source_read_square advancedMap)
end E
namespace F
export Lower.SourceFamily.Foresight (value Word action read data)
end F
namespace L
export Lower.SourceFamily.Foresight.Tail (State)
end L
open SourceGeneratedScalarCofinalNaturality
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (state:L.State (W:=W) (X:=X) (s:=s)) (t:S)
def ownAction : (j:Nat)→F.Word binding state t 0→ₗ[ℤ]F.Word binding state t 0 :=fun _=>LinearMap.id
def ownRead (j:Nat) := evaluation (R:=ℤ) (s:=t) (E.profileEnvironment binding state 0 j)
def ownData := AlgebraicDependent.data (ownAction binding state t) (ownRead binding state t) 0
abbrev BeforePrefix (bound:Nat) := AlgebraicDependent.Prefix (fun j=>PairValue (F.value binding state j) t) 0 bound
abbrev OwnPrefix (bound:Nat) := AlgebraicDependent.Prefix (fun _=>PairValue (F.value binding state 0) t) 0 bound
def stageMap (bound:Nat) : BeforePrefix binding state t bound→ₗ[ℤ]OwnPrefix binding state t bound :=
 LinearMap.pi fun i=>(E.projection binding state t i.val).comp
  ((AlgebraicDependent.familyCast (R:=ℤ) (C:=fun j=>PairValue (F.value binding state j) t)
    (Nat.zero_add i.val)).comp (LinearMap.proj i))

private theorem cast_read {a b:Nat} (same:a=b) :
 (AlgebraicDependent.familyCast (R:=ℤ) (C:=fun j=>PairValue (F.value binding state j) t) same).comp
   (F.read binding state t a)=
 (F.read binding state t b).comp
  (AlgebraicDependent.familyCast (R:=ℤ) (C:=F.Word binding state t) same) :=by
 cases same;rfl
private theorem own_advance (k:Nat) :
 AlgebraicDependent.advance (ownAction binding state t) 0 k=LinearMap.id :=by
 induction k with
 | zero=>rfl
 | succ k prior=>
  change LinearMap.id.comp (AlgebraicDependent.advance (ownAction binding state t) 0 k)=_
  exact (congrArg (fun previous=>LinearMap.id.comp previous) prior).trans (LinearMap.id_comp _)
private theorem own_evaluator (bound:Nat) (word:F.Word binding state t 0) (i:Fin (bound+1)) :
 (ownData binding state t).evaluator bound word i=
 evaluation (R:=ℤ) (E.profileEnvironment binding state 0 i.val) word :=by
 change ownRead binding state t (0+i.val)
  (AlgebraicDependent.advance (ownAction binding state t) 0 i.val word)=_
 rw[own_advance]
 exact congrArg (fun k=>ownRead binding state t k word) (Nat.zero_add i.val)

def morphism : Morphism (F.data binding state t 0) (ownData binding state t) where
 generatorMap:=LinearMap.id
 stageMap:=stageMap binding state t
 transition_naturality:=by
  intro bound
  apply LinearMap.ext
  intro value
  funext i
  rfl
 evaluator_naturality:=by
  intro bound
  apply LinearMap.ext
  intro word
  funext i
  have index:=LinearMap.congr_fun (cast_read binding state t (Nat.zero_add i.val))
   (AlgebraicDependent.advance (F.action binding state t) 0 i.val word)
  have projected:=congrArg (E.projection binding state t i.val) index
  exact projected.trans ((E.source_read_square binding state t i.val word).trans
   (own_evaluator binding state t bound word i).symm)
end Lower.SourceFamily.Foresight.Contextual.Profile.Naturality
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
