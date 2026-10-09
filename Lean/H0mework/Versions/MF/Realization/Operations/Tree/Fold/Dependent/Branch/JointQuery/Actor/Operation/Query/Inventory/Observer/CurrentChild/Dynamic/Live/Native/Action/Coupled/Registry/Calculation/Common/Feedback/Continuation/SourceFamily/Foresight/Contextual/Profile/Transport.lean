import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Naturality
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual SourceGeneratedScalarCofinalNaturality
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Transport
namespace F
export Lower.SourceFamily.Foresight (stage value Word action read data)
end F
namespace L
export Lower.SourceFamily.Foresight.Tail (State tail advance)
end L
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.Tail
 (shape queryShape query_source same_source_tail actualNextState actual_next_curve)
end T
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
abbrev WordAt (W:S→Type u) [∀t,AddCommGroup (W t)] (X:S→Type u) (t:S) (j:Nat) :=
 Formal ℤ (PairValue (Lower.Value W j)) X t
abbrev PairAt (W:S→Type u) [∀t,AddCommGroup (W t)] (t:S) (j:Nat) :=PairValue (Lower.Value W j) t
def wordCast (t:S) {a b:Nat} (same:a=b) :WordAt W X t a→ₗ[ℤ]WordAt W X t b :=
 AlgebraicDependent.familyCast (R:=ℤ) (C:=WordAt W X t) same
def pairCast (t:S) {a b:Nat} (same:a=b) :PairAt W t a→ₗ[ℤ]PairAt W t b :=
 AlgebraicDependent.familyCast (R:=ℤ) (C:=PairAt W t) same
def stepWord (t:S) (j:Nat) :WordAt W X t j→ₗ[ℤ]WordAt W X t (j+1) :=liftMap
private theorem cast_step (t:S) {a b:Nat} (same:a=b) (word:WordAt W X t a) :
 wordCast t (congrArg (·+1) same) (stepWord t a word)=stepWord t b (wordCast t same word) :=
 LinearMap.congr_fun (AlgebraicDependent.cast_action (stepWord (W:=W) (X:=X) t) same) word
private theorem evaluation_square (t:S)
 {left right:Sigma (fun j=>Env (PairValue (Lower.Value W j)) X)} (same:left=right) (word:WordAt W X t left.1) :
 pairCast t (congrArg Sigma.fst same) (evaluation (R:=ℤ) left.2 word)=
 evaluation (R:=ℤ) right.2 (wordCast t (congrArg Sigma.fst same) word) :=by
 cases same;rfl

variable (binding:∀t,X t→Expr W X t)
variable (left right:L.State (W:=W) (X:=X) (s:=s)) (same:T.shape left=T.shape right)
include same
theorem readDiagram (k:Nat) : T.queryShape binding (L.tail binding left k)=T.queryShape binding (L.tail binding right k) :=
 (T.query_source binding (L.tail binding left k)).trans
  ((congrArg (Lower.SourceFamily.Foresight.Contextual.Profile.Tail.readShape binding)
    (T.same_source_tail binding left right same k)).trans
   (T.query_source binding (L.tail binding right k)).symm)
theorem index (k:Nat) : F.stage binding left k=F.stage binding right k :=
 congrArg (fun v:Sigma (fun j=>Env (PairValue (Lower.Value W j)) X)=>v.1)
  (readDiagram binding left right same k)
def generator (t:S) :F.Word binding left t 0→ₗ[ℤ]F.Word binding right t 0 :=wordCast t (index binding left right same 0)

theorem read_square (t:S) (k:Nat) (word:F.Word binding left t k) :
 pairCast t (index binding left right same k) (F.read binding left t k word)=
 F.read binding right t k (wordCast t (index binding left right same k) word) :=
 evaluation_square t (readDiagram binding left right same k) word

theorem advance_square (t:S) (j:Nat) (word:F.Word binding left t 0) :
 wordCast t (index binding left right same (0+j))
  (AlgebraicDependent.advance (F.action binding left t) 0 j word)=
 AlgebraicDependent.advance (F.action binding right t) 0 j (generator binding left right same t word) :=by
 induction j with
 | zero=>rfl
 | succ j previous=>
  change wordCast t (congrArg (·+1) (index binding left right same (0+j)))
   (stepWord t (F.stage binding left (0+j)) (AlgebraicDependent.advance (F.action binding left t) 0 j word))=
   stepWord t (F.stage binding right (0+j))
    (AlgebraicDependent.advance (F.action binding right t) 0 j (generator binding left right same t word))
  exact (cast_step t (index binding left right same (0+j))
   (AlgebraicDependent.advance (F.action binding left t) 0 j word)).trans
   (congrArg (stepWord t (F.stage binding right (0+j))) previous)

def stageMap (t:S) (bound:Nat) :
 AlgebraicDependent.Prefix (fun k=>PairValue (F.value binding left k) t) 0 bound→ₗ[ℤ]
 AlgebraicDependent.Prefix (fun k=>PairValue (F.value binding right k) t) 0 bound :=
 LinearMap.pi fun i=>(pairCast t (index binding left right same (0+i.val))).comp (LinearMap.proj i)
def transport (t:S) :Morphism (F.data binding left t 0) (F.data binding right t 0) where
 generatorMap:=generator binding left right same t
 stageMap:=stageMap binding left right same t
 transition_naturality _:=by
  apply LinearMap.ext
  intro values
  funext i
  rfl
 evaluator_naturality _:=by
  apply LinearMap.ext
  intro word
  funext i
  exact (read_square binding left right same t (0+i.val) _).trans
   (congrArg (F.read binding right t (0+i.val)) (advance_square binding left right same t i.val word))

omit same
section Actual
variable (n:Nat) (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev previousState :L.State (W:=W) (X:=X) (s:=s) :=⟨n,packet⟩
abbrev generatedState :L.State (W:=W) (X:=X) (s:=s) :=T.actualNextState binding n packet
def actualTransport (t:S) :Morphism
 (F.data binding (L.advance binding (previousState n packet)) t 0)
 (F.data binding (generatedState binding n packet) t 0) :=
 transport binding (L.advance binding (previousState n packet)) (generatedState binding n packet)
  (T.actual_next_curve binding n packet).symm t
theorem actual_generator (t:S) : (actualTransport binding n packet t).generatorMap=LinearMap.id :=rfl
end Actual
end Lower.SourceFamily.Foresight.Contextual.Profile.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
