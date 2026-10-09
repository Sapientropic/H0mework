import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Consumer
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Observed
open CurrentChild
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
local instance : DecidableEq (Index root recognition) := Classical.decEq _
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Dynamic.Frame root visit recognition) (read : Dynamic.Read root visit recognition frame)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Dynamic.C.Occurrence frame (current:=current))
abbrev baseEnvironment := fun slot name => read supplied (.inl slot) name
abbrev childEnvironment := fun slot name => read supplied (.inl (.inl slot)) name

private theorem embed_value {slot : Observer.Slot root recognition}
 (term : Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition) slot) :
 (CurrentChild.embed root visit recognition term).eval (read supplied) =
 term.eval (baseEnvironment root visit recognition frame read supplied) := by
 induction term with
 | var => rfl
 | const => rfl
 | add first second one two => exact congrArg₂ (·+·) one two
 | linear operation argument previous => exact congrArg operation previous
 | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two
private theorem child_embed_value {slot : Inventory.Slot root recognition}
 (term : Expr (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition) slot) :
 (Observer.embed root visit recognition term).eval (baseEnvironment root visit recognition frame read supplied) =
 term.eval (childEnvironment root visit recognition frame read supplied) := by
 induction term with
 | var => rfl
 | const => rfl
 | add first second one two => exact congrArg₂ (·+·) one two
 | linear operation argument previous => exact congrArg operation previous
 | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two

def pointAt (index : Index root recognition) :=
 let row := rowAt root recognition index
 childEnvironment root visit recognition frame read supplied (.inr (.inl row.1)) ⟨row.2⟩ row.2
def nextPointAt (index : Index root recognition) := Observer.action root recognition (rowAt root recognition index)
 (pointAt root visit recognition frame read supplied index)
def observationValueAt (index : Index root recognition) (kind : Fin 4) :=
 let row := rowAt root recognition index
 let point := pointAt root visit recognition frame read supplied index
 let next := nextPointAt root visit recognition frame read supplied index
 match kind.val with
 | 0 => Observer.measurement root recognition row point
 | 1 => Observer.measurement root recognition row next
 | 2 => Observer.evolution root recognition row (Observer.measurement root recognition row point)
 | _ => Observer.evolution root recognition row (Observer.measurement root recognition row point) -
   Observer.measurement root recognition row next

private theorem observer_term_value (index : Index root recognition) (kind : Fin 4) :
 (observationTerm root visit recognition index kind).eval (baseEnvironment root visit recognition frame read supplied) =
 observationValueAt root visit recognition frame read supplied index kind := by
 fin_cases kind
 · rfl
 · change Observer.measurement root recognition (rowAt root recognition index)
     (Observer.coordinate root recognition (rowAt root recognition index)
      ((Observer.embed root visit recognition (Inventory.Action.binding root visit recognition
        (.inr (.inl (rowAt root recognition index).1)) ⟨(rowAt root recognition index).2⟩)).eval
        (baseEnvironment root visit recognition frame read supplied))) = _
   rw [child_embed_value]
   rfl
 · rfl
 · change _ + (-AddMonoidHom.id (Observer.Measured (H:=H)))
    ((Observer.nextMeasuredTerm root visit recognition (rowAt root recognition index)).eval
      (baseEnvironment root visit recognition frame read supplied)) = _
   simp only [AddMonoidHom.neg_apply,AddMonoidHom.id_apply]
   have next : (Observer.nextMeasuredTerm root visit recognition (rowAt root recognition index)).eval
       (baseEnvironment root visit recognition frame read supplied) =
       Observer.measurement root recognition (rowAt root recognition index)
        (nextPointAt root visit recognition frame read supplied index) := by
     change Observer.measurement root recognition (rowAt root recognition index)
       (Observer.coordinate root recognition (rowAt root recognition index)
        ((Observer.embed root visit recognition (Inventory.Action.binding root visit recognition
         (.inr (.inl (rowAt root recognition index).1)) ⟨(rowAt root recognition index).2⟩)).eval
          (baseEnvironment root visit recognition frame read supplied))) = _
     rw [child_embed_value]
     rfl
   rw [next]
   exact (sub_eq_add_neg _ _).symm

theorem observation_output_value (index : Index root recognition) (kind : Fin 4) :
 (observationOutput root visit recognition index kind).eval (read supplied) =
 observationInjection root visit recognition index kind (observationValueAt root visit recognition frame read supplied index kind) := by
 change observationInjection root visit recognition index kind
  ((embed root visit recognition (observationTerm root visit recognition index kind)).eval _) = _
 rw [embed_value,observer_term_value]

theorem gram_output_value (first second : Sample root recognition) :
 (gramOutput root visit recognition first second).eval (read supplied) =
 gramInjection root visit recognition first second (ULift.up (inner ℂ
  (observationValueAt root visit recognition frame read supplied first.1 first.2)
  (observationValueAt root visit recognition frame read supplied second.1 second.2))) := by
 change gramInjection root visit recognition first second
  (Observer.innerOperation ((embed root visit recognition (observationTerm root visit recognition first.1 first.2)).eval _)
   ((embed root visit recognition (observationTerm root visit recognition second.1 second.2)).eval _)) = _
 rw [embed_value,embed_value,observer_term_value,observer_term_value]
 rfl

def actorRead : Output root visit recognition →+ Actor.Output root visit recognition where
 toFun value := value.2.1
 map_zero' := rfl
 map_add' _ _ := rfl
def observationRead (index : Index root recognition) (kind : Fin 4) : Output root visit recognition →+ Observer.Measured (H:=H) where
 toFun value := value.2.2.1 index kind
 map_zero' := rfl
 map_add' _ _ := rfl
def gramRead (first second : Sample root recognition) : Output root visit recognition →+ ULift.{u} ℂ where
 toFun value := value.2.2.2 first second
 map_zero' := rfl
 map_add' _ _ := rfl

private theorem mapped_zero {X G : Type u} [AddCommMonoid G] (terms : List X) (read : X → G)
 (zero : ∀ term ∈ terms, read term=0) : (terms.map read).sum=0 := by
 apply List.sum_eq_zero
 intro value belongs
 rcases List.mem_map.mp belongs with ⟨term,present,rfl⟩
 exact zero term present

private theorem position_index_eq (source : SourceActor root recognition)
 (first second : Fin (rowsAtActor root recognition source).length) :
 (⟨source,first⟩ : Index root recognition)=⟨source,second⟩ ↔ first=second := by
 constructor
 · intro same
   exact eq_of_heq (Sigma.mk.inj same).2
 · intro same
   exact congrArg (fun position => (⟨source,position⟩ : Index root recognition)) same

private theorem samples_sum {B : Type u} [AddCommMonoid B] (source : SourceActor root recognition)
 (f : Sample root recognition → B) :
 ((samples root recognition source).map f).sum =
 ∑ position : Fin (rowsAtActor root recognition source).length, ∑ kind : Fin 4, f (⟨source,position⟩,kind) := by
 simp only [samples,indices,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
private theorem samples_double_sum {B : Type u} [AddCommMonoid B] (source : SourceActor root recognition)
 (f : Sample root recognition → Sample root recognition → B) :
 ((samples root recognition source).flatMap (fun first => (samples root recognition source).map (f first))).sum =
 ∑ i : Fin (rowsAtActor root recognition source).length, ∑ k : Fin 4,
 ∑ j : Fin (rowsAtActor root recognition source).length, ∑ l : Fin 4, f (⟨source,i⟩,k) (⟨source,j⟩,l) := by
 rw [List.flatMap_def,List.sum_flatten]
 simp only [List.map_map,Function.comp_def,samples_sum]
private theorem samples_delta {B : Type u} [AddCommMonoid B] (source : SourceActor root recognition)
 (f : Sample root recognition → Sample root recognition → B)
 (first second : Fin (rowsAtActor root recognition source).length × Fin 4) :
 ((samples root recognition source).flatMap (fun a => (samples root recognition source).map
  (fun b => if ((⟨source,first.1⟩ : Index root recognition),first.2)=a ∧ ((⟨source,second.1⟩ : Index root recognition),second.2)=b then f a b else 0))).sum =
 f (⟨source,first.1⟩,first.2) (⟨source,second.1⟩,second.2) := by
 classical
 rw [samples_double_sum]
 rcases first with ⟨i,k⟩
 rcases second with ⟨j,l⟩
 rw [Fintype.sum_eq_single i]
 · rw [Fintype.sum_eq_single k]
   · rw [Fintype.sum_eq_single j]
     · rw [Fintype.sum_eq_single l]
       · simp
       · intro other different
         simp [Ne.symm different]
     · intro other different
       simp [Prod.mk.injEq,Ne.symm different]
   · intro other different
     simp [Prod.mk.injEq,Ne.symm different]
 · intro other different
   simp [Prod.mk.injEq,Ne.symm different]

private theorem observation_read_term (index : Index root recognition) (kind : Fin 4)
 (other : Index root recognition) (channel : Fin 4) :
 observationRead root visit recognition index kind
 ((observationOutput root visit recognition other channel).eval (read supplied)) =
 if index=other then if kind=channel then observationValueAt root visit recognition frame read supplied other channel else 0 else 0 := by
 classical
 rw [observation_output_value]
 by_cases sameIndex : index=other <;> by_cases sameKind : kind=channel <;>
  simp [observationRead,observationInjection,sameIndex,sameKind]
private theorem gram_read_term (first second otherFirst otherSecond : Sample root recognition) :
 gramRead root visit recognition first second
 ((gramOutput root visit recognition otherFirst otherSecond).eval (read supplied)) =
 if first=otherFirst then if second=otherSecond then ULift.up (inner ℂ
  (observationValueAt root visit recognition frame read supplied otherFirst.1 otherFirst.2)
  (observationValueAt root visit recognition frame read supplied otherSecond.1 otherSecond.2)) else 0 else 0 := by
 classical
 rw [gram_output_value]
 by_cases sameFirst : first=otherFirst <;> by_cases sameSecond : second=otherSecond <;>
  simp [gramRead,gramInjection,sameFirst,sameSecond]


private theorem observation_member (term) (present : term ∈ observationsFor root visit recognition frame read supplied) :
 ∃ index : Index root recognition, ∃ kind : Fin 4, term=observationOutput root visit recognition index kind := by
 rcases List.mem_flatten.mp present with ⟨terms,inTerms,inTerm⟩
 rcases List.mem_map.mp inTerms with ⟨index,_,rfl⟩
 rcases List.mem_ofFn.mp inTerm with ⟨kind,same⟩
 exact ⟨index,kind,same.symm⟩

private theorem observation_paid_sum (index : Index root recognition) (kind : Fin 4) :
 (paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1.2.2.1 index kind =
 ((observationsFor root visit recognition frame read supplied).map
  (fun term => observationRead root visit recognition index kind (term.eval (read supplied)))).sum := by
 rw [paid_value_for]
 change observationRead root visit recognition index kind
  (((termsFor root visit recognition U7 calculus anchor frame read supplied).map (fun term => term.eval (read supplied))).sum) = _
 rw [map_list_sum]
 simp only [termsFor,List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
 have childZero : ∀ term ∈ childrenFor root visit recognition frame read supplied,
  observationRead root visit recognition index kind (term.eval (read supplied))=0 := by
  intro term present
  rcases List.mem_map.mp present with ⟨source,_,rfl⟩
  rfl
 have gramZero : ∀ term ∈ gramsFor root visit recognition frame read supplied,
  observationRead root visit recognition index kind (term.eval (read supplied))=0 := by
  intro term present
  rcases List.mem_flatMap.mp present with ⟨first,_,inside⟩
  rcases List.mem_map.mp inside with ⟨second,_,rfl⟩
  rfl
 have oldZero : observationRead root visit recognition index kind
  ((oldTerm root visit recognition U7 calculus anchor).eval (read supplied))=0 := rfl
 have actorZero : observationRead root visit recognition index kind
  ((actorTerm root visit recognition).eval (read supplied))=0 := rfl
 rw [oldZero,actorZero,mapped_zero _ _ childZero,mapped_zero _ _ gramZero]
 simp only [zero_add,add_zero]

private theorem gram_paid_sum (first second : Sample root recognition) :
 (paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1.2.2.2 first second =
 ((gramsFor root visit recognition frame read supplied).map
  (fun term => gramRead root visit recognition first second (term.eval (read supplied)))).sum := by
 rw [paid_value_for]
 change gramRead root visit recognition first second
  (((termsFor root visit recognition U7 calculus anchor frame read supplied).map (fun term => term.eval (read supplied))).sum) = _
 rw [map_list_sum]
 simp only [termsFor,List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
 have childZero : ∀ term ∈ childrenFor root visit recognition frame read supplied,
  gramRead root visit recognition first second (term.eval (read supplied))=0 := by
  intro term present
  rcases List.mem_map.mp present with ⟨source,_,rfl⟩
  rfl
 have obsZero : ∀ term ∈ observationsFor root visit recognition frame read supplied,
  gramRead root visit recognition first second (term.eval (read supplied))=0 := by
  intro term present
  rcases observation_member root visit recognition frame read supplied term present with ⟨index,kind,rfl⟩
  rfl
 have oldZero : gramRead root visit recognition first second
  ((oldTerm root visit recognition U7 calculus anchor).eval (read supplied))=0 := rfl
 have actorZero : gramRead root visit recognition first second
  ((actorTerm root visit recognition).eval (read supplied))=0 := rfl
 rw [oldZero,actorZero,mapped_zero _ _ childZero,mapped_zero _ _ obsZero]
 simp only [zero_add]

theorem paid_observation_of_support (source : SourceActor root recognition)
 (sourceSupport : supportFor root visit recognition frame read supplied=[source])
 (position : Fin (rowsAtActor root recognition source).length) (kind : Fin 4) :
 (paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1.2.2.1 ⟨source,position⟩ kind =
 observationValueAt root visit recognition frame read supplied ⟨source,position⟩ kind := by
 rw [observation_paid_sum]
 simp only [observationsFor,indicesFor,sourceSupport,List.flatMap_cons,List.flatMap_nil,List.append_nil,
  indices,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def,observation_read_term,position_index_eq]
 rw [Fintype.sum_eq_single position]
 · simp only [if_true]
   rw [Fintype.sum_eq_single kind]
   · simp
   · intro other different
     simp [Ne.symm different]
 · intro other different
   simp [Ne.symm different]

theorem paid_gram_of_support (source : SourceActor root recognition)
 (sourceSupport : supportFor root visit recognition frame read supplied=[source])
 (first second : Fin (rowsAtActor root recognition source).length × Fin 4) :
 ((paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1.2.2.2
   (⟨source,first.1⟩,first.2) (⟨source,second.1⟩,second.2)).down =
 inner ℂ (observationValueAt root visit recognition frame read supplied ⟨source,first.1⟩ first.2)
  (observationValueAt root visit recognition frame read supplied ⟨source,second.1⟩ second.2) := by
 rw [gram_paid_sum]
 have observed : ((gramsFor root visit recognition frame read supplied).map
    (fun term => gramRead root visit recognition (⟨source,first.1⟩,first.2) (⟨source,second.1⟩,second.2)
      (term.eval (read supplied)))).sum = ULift.up (inner ℂ
        (observationValueAt root visit recognition frame read supplied ⟨source,first.1⟩ first.2)
        (observationValueAt root visit recognition frame read supplied ⟨source,second.1⟩ second.2)) := by
  simp only [gramsFor,samplesFor,sourceSupport,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   List.map_flatMap,List.map_map,Function.comp_def,gram_read_term]
  simpa only [ite_and] using samples_delta root recognition source
   (fun a b => ULift.up.{u} (inner ℂ (observationValueAt root visit recognition frame read supplied a.1 a.2)
    (observationValueAt root visit recognition frame read supplied b.1 b.2))) first second
 exact congrArg ULift.down observed

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Observed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
