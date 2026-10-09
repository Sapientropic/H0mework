import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Tail
import H0mework.Realization.Integral.CharacterExact
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight
namespace L
export Lower.SourceFamily.Foresight.Tail (State advance tail tail_index exact_actual_tail)
end L
namespace C
export SourceGeneratedScalarCharacterExact (Carrier canonicalMap canonicalMap_injective factor factor_canonicalMap map map_canonicalMap)
end C
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance sourceGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (binding : ∀ t,X t → Expr W X t) (state : L.State (W:=W) (X:=X) (s:=s))
abbrev stage (k : Nat) := (L.tail binding state k).1
abbrev value (k : Nat) := Lower.Value W (stage binding state k)
abbrev cfg (k : Nat) := Lower.SourceFamily.cfg (Lower.SourceFamily.Replay.factory (s:=s) binding)
 (stage binding state k) (L.tail binding state k).2.2
abbrev frame (k : Nat) := (L.tail binding state k).2.1
abbrev scalar (k : Nat) := Lower.SourceFamily.scalar (Lower.SourceFamily.Replay.factory (s:=s) binding)
 (stage binding state k) (L.tail binding state k).2
abbrev pair (k : Nat) := Lower.SourceFamily.pair (Lower.SourceFamily.Replay.factory (s:=s) binding)
 (stage binding state k) (L.tail binding state k).2
abbrev environment (k : Nat) := (Lower.SourceFamily.Effect.Q.query (frame binding state k) (cfg binding state k)).raw.environment
abbrev Word (t : S) (k : Nat) := Formal ℤ (PairValue (value binding state k)) X t
def action (t : S) (k : Nat) : Word binding state t k →ₗ[ℤ] Word binding state t (k+1) := liftMap
def read (t : S) (k : Nat) : Word binding state t k →ₗ[ℤ] PairValue (value binding state k) t :=
 evaluation (R:=ℤ) (s:=t) (environment binding state k)
def data (t : S) (k : Nat) := AlgebraicDependent.data (action binding state t) (read binding state t) k
abbrev completion (t : S) (k : Nat) := AlgebraicDependent.completion (action binding state t) (read binding state t) k
abbrev Model (t : S) (k : Nat) := C.Carrier ℤ (completion binding state t k)
def sourceMap (t : S) (k : Nat) := (C.canonicalMap ℤ (completion binding state t k)).comp
 (AlgebraicDependent.sourceMap (action binding state t) (read binding state t) k)
def readPrefix (t : S) (k bound : Nat) := C.factor (AlgebraicDependent.readPrefix
 (action binding state t) (read binding state t) k bound)
def next (t : S) (k : Nat) := C.map (AlgebraicDependent.successor (action binding state t) (read binding state t) k)

theorem source_prefix (t : S) (k bound : Nat) (word : Word binding state t k) :
 readPrefix binding state t k bound (sourceMap binding state t k word)=
 AlgebraicDependent.evaluator (action binding state t) (read binding state t) k bound word :=
 (LinearMap.congr_fun (C.factor_canonicalMap (AlgebraicDependent.readPrefix
  (action binding state t) (read binding state t) k bound))
  (AlgebraicDependent.sourceMap (action binding state t) (read binding state t) k word)).trans
 (AlgebraicDependent.source_prefix (action binding state t) (read binding state t) k bound word)

theorem source_fibre (t : S) (k : Nat) (left right : Word binding state t k) :
 sourceMap binding state t k left=sourceMap binding state t k right ↔
 ∀ j,read binding state t (k+j) (AlgebraicDependent.advance (action binding state t) k j left)=
 read binding state t (k+j) (AlgebraicDependent.advance (action binding state t) k j right) := by
 constructor
 · intro same
   exact (AlgebraicDependent.source_fibre (action binding state t) (read binding state t) k left right).mp
    (C.canonicalMap_injective ℤ (completion binding state t k) same)
 · intro same
   exact congrArg (C.canonicalMap ℤ (completion binding state t k))
    ((AlgebraicDependent.source_fibre (action binding state t) (read binding state t) k left right).mpr same)

theorem next_source (t : S) (k : Nat) (word : Word binding state t k) :
 next binding state t k (sourceMap binding state t k word)=sourceMap binding state t (k+1) (action binding state t k word) :=
 (C.map_canonicalMap (AlgebraicDependent.successor (action binding state t) (read binding state t) k)
  (AlgebraicDependent.sourceMap (action binding state t) (read binding state t) k word)).trans
 (congrArg (C.canonicalMap ℤ (completion binding state t (k+1)))
  (AlgebraicDependent.successor_source (action binding state t) (read binding state t) k word))

def coordinate (t : S) (k : Nat) (name : X t) : Word binding state t k := Finsupp.single (Expr.var name) 1
def sourceCoordinates (k : Nat) := fun (t : S) (name : X t) => sourceMap binding state t k (coordinate binding state t k name)
def recoveredCurrent (k : Nat) : Env (PairValue (value binding state k)) X := fun t name =>
 readPrefix binding state t k 0 (sourceCoordinates binding state k t name) ⟨0,by omega⟩
def recoveredNext (k : Nat) : Env (PairValue (value binding state (k+1))) X := fun t name =>
 readPrefix binding state t k 1 (sourceCoordinates binding state k t name) (Fin.last 1)
theorem recovered_current (k : Nat) : recoveredCurrent binding state k=environment binding state k := by
 funext t name
 change readPrefix binding state t k 0 (sourceMap binding state t k (coordinate binding state t k name)) ⟨0,by omega⟩=_
 rw [source_prefix]
 change evaluation (R:=ℤ) (environment binding state k) (Finsupp.single (Expr.var name) 1)=_
 simp only [evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval]
theorem recovered_next (k : Nat) : recoveredNext binding state k=environment binding state (k+1) := by
 funext t name
 change readPrefix binding state t k 1 (sourceMap binding state t k (coordinate binding state t k name)) (Fin.last 1)=_
 rw [source_prefix]
 change evaluation (R:=ℤ) (environment binding state (k+1)) (liftMap (Finsupp.single (Expr.var name) 1))=_
 simp only [liftMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,liftExpr,evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval]

theorem dropfirst_evaluator (t : S) (k bound : Nat) : type_of% (AlgebraicDependent.dropFirst_evaluator
 (action binding state t) (read binding state t) k bound) := AlgebraicDependent.dropFirst_evaluator _ _ _ _

end Lower.SourceFamily.Foresight
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
