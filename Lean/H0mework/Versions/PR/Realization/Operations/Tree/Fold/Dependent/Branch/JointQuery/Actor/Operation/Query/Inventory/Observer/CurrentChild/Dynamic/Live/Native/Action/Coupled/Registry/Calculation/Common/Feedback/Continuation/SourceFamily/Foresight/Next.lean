import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Operator
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
open CategoryTheory SourceGeneratedScalarCofinalKernelCompletion
namespace Lower.SourceFamily.Foresight.Successor
namespace F
export Lower.SourceFamily.Foresight (Word Model action read data sourceMap next recoveredCurrent recoveredNext recovered_current recovered_next source_fibre)
end F
namespace T
export Lower.SourceFamily.Foresight.Tail (State tail advance tail_after_actual_step)
end T
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance nextGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (binding : ∀ t,X t → Expr W X t)
abbrev WordAt (t : S) (state : T.State (W:=W) (X:=X) (s:=s)) := Formal ℤ (PairValue (Lower.Value W state.1)) X t
abbrev PairAt (t : S) (state : T.State (W:=W) (X:=X) (s:=s)) := PairValue (Lower.Value W state.1) t
def wordCast (t : S) {a b : T.State (W:=W) (X:=X) (s:=s)} (same : a=b) : WordAt t a →ₗ[ℤ] WordAt t b := by
 cases same
 exact LinearMap.id
def pairCast (t : S) {a b : T.State (W:=W) (X:=X) (s:=s)} (same : a=b) : PairAt t a →ₗ[ℤ] PairAt t b := by
 cases same
 exact LinearMap.id
def stepWord (t : S) (state : T.State (W:=W) (X:=X) (s:=s)) : WordAt t state →ₗ[ℤ] WordAt t (T.advance binding state) := liftMap

theorem cast_step (t : S) {a b : T.State (W:=W) (X:=X) (s:=s)} (same : a=b) (word : WordAt t a) :
 wordCast t (congrArg (T.advance binding) same) (stepWord binding t a word)=
 stepWord binding t b (wordCast t same word) := by
 cases same
 rfl

theorem cast_read (t : S) {a b : T.State (W:=W) (X:=X) (s:=s)} (same : a=b) (word : WordAt t a) :
 pairCast t same (F.read binding a t 0 word)=F.read binding b t 0 (wordCast t same word) := by
 cases same
 rfl

variable (state : T.State (W:=W) (X:=X) (s:=s))
theorem shift (j : Nat) : T.tail binding state (1+j)=T.tail binding (T.advance binding state) (0+j) :=
 (congrArg (T.tail binding state) (Nat.add_comm 1 j)).trans
  ((T.tail_after_actual_step binding state j).symm.trans
   (congrArg (T.tail binding (T.advance binding state)) (Nat.zero_add j).symm))
def generator (t : S) : F.Word binding state t 1 →ₗ[ℤ] F.Word binding (T.advance binding state) t 0 :=
 wordCast t (shift binding state 0)
theorem generator_actual (t : S) (word : F.Word binding state t 1) : generator binding state t word=word := rfl

theorem advance_square (t : S) (j : Nat) (word : F.Word binding state t 1) :
 wordCast t (shift binding state j) (AlgebraicDependent.advance (F.action binding state t) 1 j word)=
 AlgebraicDependent.advance (F.action binding (T.advance binding state) t) 0 j (generator binding state t word) := by
 induction j with
 | zero => rfl
 | succ j prior =>
  change wordCast t (congrArg (T.advance binding) (shift binding state j))
   (stepWord binding t (T.tail binding state (1+j)) (AlgebraicDependent.advance (F.action binding state t) 1 j word))=
   stepWord binding t (T.tail binding (T.advance binding state) (0+j))
    (AlgebraicDependent.advance (F.action binding (T.advance binding state) t) 0 j (generator binding state t word))
  exact (cast_step binding t (shift binding state j)
   (AlgebraicDependent.advance (F.action binding state t) 1 j word)).trans
   (congrArg (stepWord binding t (T.tail binding (T.advance binding state) (0+j))) prior)

def stageMap (t : S) (bound : Nat) :
 AlgebraicDependent.Prefix (fun k => PairValue (Lower.SourceFamily.Foresight.value binding state k) t) 1 bound →ₗ[ℤ]
 AlgebraicDependent.Prefix (fun k => PairValue (Lower.SourceFamily.Foresight.value binding (T.advance binding state) k) t) 0 bound :=
 LinearMap.pi fun index => (pairCast t (shift binding state index.val)).comp (LinearMap.proj index)

def natural (t : S) : SourceGeneratedScalarCofinalNaturality.Morphism (F.data binding state t 1)
 (F.data binding (T.advance binding state) t 0) where
 generatorMap:=generator binding state t
 stageMap:=stageMap binding state t
 transition_naturality _:=by
  apply LinearMap.ext
  intro values
  funext index
  rfl
 evaluator_naturality _:=by
  apply LinearMap.ext
  intro word
  funext index
  change pairCast t (shift binding state index.val)
   (F.read binding state t (1+index.val) (AlgebraicDependent.advance (F.action binding state t) 1 index.val word))=
   F.read binding (T.advance binding state) t (0+index.val)
    (AlgebraicDependent.advance (F.action binding (T.advance binding state) t) 0 index.val (generator binding state t word))
  exact (cast_read binding t (shift binding state index.val) _).trans
   (congrArg (F.read binding (T.advance binding state) t (0+index.val)) (advance_square binding state t index.val word))

abbrev lawOld (t : S) := AlgebraicDependent.compatible (F.action binding state t) (F.read binding state t) 1
abbrev lawNext (t : S) := AlgebraicDependent.compatible (F.action binding (T.advance binding state) t) (F.read binding (T.advance binding state) t) 0
def completionMove (t : S) : Lower.SourceFamily.Foresight.completion binding state t 1 →ₗ[ℤ]
 Lower.SourceFamily.Foresight.completion binding (T.advance binding state) t 0 :=
 ((natural binding state t).completionMorphism (lawOld binding state t) (lawNext binding state t)).hom

theorem completion_source (t : S) (word : F.Word binding state t 1) :
 completionMove binding state t (AlgebraicDependent.sourceMap (F.action binding state t) (F.read binding state t) 1 word)=
 AlgebraicDependent.sourceMap (F.action binding (T.advance binding state) t) (F.read binding (T.advance binding state) t) 0 (generator binding state t word) :=
 ConcreteCategory.congr_hom ((natural binding state t).completionMorphism_source_naturality
 (lawOld binding state t) (lawNext binding state t)) word

def characterMove (t : S) := SourceGeneratedScalarCharacterExact.map (completionMove binding state t)
theorem character_source (t : S) (word : F.Word binding state t 1) :
 characterMove binding state t (F.sourceMap binding state t 1 word)=
 F.sourceMap binding (T.advance binding state) t 0 (generator binding state t word) :=
 (SourceGeneratedScalarCharacterExact.map_canonicalMap (completionMove binding state t)
  (AlgebraicDependent.sourceMap (F.action binding state t) (F.read binding state t) 1 word)).trans
 (congrArg (SourceGeneratedScalarCharacterExact.canonicalMap ℤ (Lower.SourceFamily.Foresight.completion binding (T.advance binding state) t 0))
  (completion_source binding state t word))

def nextCharacter (t : S) : F.Model binding state t 0 →ₗ[ℤ] F.Model binding (T.advance binding state) t 0 := (characterMove binding state t).comp (F.next binding state t 0)
theorem actual_next_source (t : S) (word : F.Word binding state t 0) :
 nextCharacter binding state t (F.sourceMap binding state t 0 word)=
 F.sourceMap binding (T.advance binding state) t 0 (F.action binding state t 0 word) :=
 (congrArg (characterMove binding state t) (Lower.SourceFamily.Foresight.next_source binding state t 0 word)).trans
 ((character_source binding state t (F.action binding state t 0 word)).trans
  (congrArg (F.sourceMap binding (T.advance binding state) t 0) (generator_actual binding state t _)))

theorem next_environment : F.recoveredCurrent binding (T.advance binding state) 0=F.recoveredNext binding state 0 :=
 (F.recovered_current binding (T.advance binding state) 0).trans (F.recovered_next binding state 0).symm
end Lower.SourceFamily.Foresight.Successor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
