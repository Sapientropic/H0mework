import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Source
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
local instance : DecidableEq (Index root recognition) := Classical.decEq _
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor stage : Nat)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
 (sourceFrame root visit recognition U7 calculus anchor stage).registered}
variable (supplied : Observer.Action.C.Occurrence (sourceFrame root visit recognition U7 calculus anchor stage) (current:=current))
abbrev baseEnvironment := Observer.Action.environmentAt root visit recognition
 (sourceFrame root visit recognition U7 calculus anchor stage) supplied

theorem embed_value {slot : Observer.Slot root recognition}
 (term : Expr (Observer.Value root visit recognition) (Observer.Variable root visit recognition) slot) :
 (embed root visit recognition term).eval (environmentAt root visit recognition U7 calculus anchor stage supplied) =
 term.eval (baseEnvironment root visit recognition U7 calculus anchor stage supplied) :=
 Actor.Extension.embed_eval _ _ _ _ _

def pointAt (index : Index root recognition) := Observer.Action.pointAt root visit recognition
 (sourceFrame root visit recognition U7 calculus anchor stage) supplied (rowAt root recognition index)
def nextPointAt (index : Index root recognition) := Observer.Action.nextPointAt root visit recognition
 (sourceFrame root visit recognition U7 calculus anchor stage) supplied (rowAt root recognition index)
theorem next_point (index : Index root recognition) : nextPointAt root visit recognition U7 calculus anchor stage supplied index =
 Observer.action root recognition (rowAt root recognition index) (pointAt root visit recognition U7 calculus anchor stage supplied index) :=
 Observer.Action.next_point_at root visit recognition _ _ _

def observationValueAt (index : Index root recognition) (kind : Fin 4) :=
 let row := rowAt root recognition index
 let point := pointAt root visit recognition U7 calculus anchor stage supplied index
 let next := nextPointAt root visit recognition U7 calculus anchor stage supplied index
 match kind.val with
 | 0 => Observer.measurement root recognition row point
 | 1 => Observer.measurement root recognition row next
 | 2 => Observer.evolution root recognition row (Observer.measurement root recognition row point)
 | _ => Observer.evolution root recognition row (Observer.measurement root recognition row point) -
   Observer.measurement root recognition row next

private theorem observer_term_value (index : Index root recognition) (kind : Fin 4) :
 (observationTerm root visit recognition index kind).eval (baseEnvironment root visit recognition U7 calculus anchor stage supplied) =
 observationValueAt root visit recognition U7 calculus anchor stage supplied index kind := by
 fin_cases kind
 · rfl
 · change Observer.measurement root recognition (rowAt root recognition index)
     (Observer.coordinate root recognition (rowAt root recognition index)
      ((Observer.embed root visit recognition (Inventory.Action.binding root visit recognition
        (.inr (.inl (rowAt root recognition index).1)) ⟨(rowAt root recognition index).2⟩)).eval
        (baseEnvironment root visit recognition U7 calculus anchor stage supplied))) = _
   rw [Observer.Action.old_embed_eval_at]
   rfl
 · rfl
 · change _ + (-AddMonoidHom.id (Observer.Measured (H:=H)))
    ((Observer.nextMeasuredTerm root visit recognition (rowAt root recognition index)).eval
      (baseEnvironment root visit recognition U7 calculus anchor stage supplied)) = _
   simp only [AddMonoidHom.neg_apply,AddMonoidHom.id_apply]
   have next : (Observer.nextMeasuredTerm root visit recognition (rowAt root recognition index)).eval
       (baseEnvironment root visit recognition U7 calculus anchor stage supplied) =
       Observer.measurement root recognition (rowAt root recognition index)
        (nextPointAt root visit recognition U7 calculus anchor stage supplied index) := by
     change Observer.measurement root recognition (rowAt root recognition index)
       (Observer.coordinate root recognition (rowAt root recognition index)
        ((Observer.embed root visit recognition (Inventory.Action.binding root visit recognition
         (.inr (.inl (rowAt root recognition index).1)) ⟨(rowAt root recognition index).2⟩)).eval
          (baseEnvironment root visit recognition U7 calculus anchor stage supplied))) = _
     rw [Observer.Action.old_embed_eval_at]
     rfl
   rw [next]
   exact (sub_eq_add_neg _ _).symm

theorem observation_output_value (index : Index root recognition) (kind : Fin 4) :
 (observationOutput root visit recognition index kind).eval (environmentAt root visit recognition U7 calculus anchor stage supplied) =
 observationInjection root visit recognition index kind (observationValueAt root visit recognition U7 calculus anchor stage supplied index kind) := by
 change observationInjection root visit recognition index kind
  ((embed root visit recognition (observationTerm root visit recognition index kind)).eval _) = _
 rw [embed_value,observer_term_value]

theorem gram_output_value (first second : Sample root recognition) :
 (gramOutput root visit recognition first second).eval (environmentAt root visit recognition U7 calculus anchor stage supplied) =
 gramInjection root visit recognition first second (ULift.up (inner ℂ
  (observationValueAt root visit recognition U7 calculus anchor stage supplied first.1 first.2)
  (observationValueAt root visit recognition U7 calculus anchor stage supplied second.1 second.2))) := by
 change gramInjection root visit recognition first second
  (Observer.innerOperation ((embed root visit recognition (observationTerm root visit recognition first.1 first.2)).eval _)
   ((embed root visit recognition (observationTerm root visit recognition second.1 second.2)).eval _)) = _
 rw [embed_value,embed_value,observer_term_value,observer_term_value]
 rfl

theorem programme_value (terms : List (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition))) :
 (programme root visit recognition terms).eval (environmentAt root visit recognition U7 calculus anchor stage supplied) =
 (terms.map (fun term => term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))).sum := by
 induction terms with
 | nil => rfl
 | cons first rest previous =>
   simpa only [programme,Expr.eval,List.map_cons,List.sum_cons] using
    congrArg (fun value : Output root visit recognition => first.eval (environmentAt root visit recognition U7 calculus anchor stage supplied)+value) previous

theorem programme_charge (terms : List (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition))) :
 remaining (programme root visit recognition terms) = (terms.map remaining).sum+terms.length := by
 induction terms with
 | nil => rfl
 | cons first rest previous =>
   simp only [programme,remaining,previous,List.map_cons,List.sum_cons,List.length_cons]
   omega

theorem paid_value_at : (paidAt root visit recognition U7 calculus anchor stage supplied).2.2.1 =
 ((oldTerm root visit recognition U7 calculus anchor :: actorTerm root visit recognition ::
   childTerm root visit recognition U7 calculus anchor stage ::
   (observerTerms root visit recognition U7 calculus anchor stage ++ gramTerms root visit recognition U7 calculus anchor stage)).map
   (fun term => term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))).sum :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans (programme_value _ _ _ _ _ _ _ _ _)

theorem paid_fee_at : (paidAt root visit recognition U7 calculus anchor stage supplied).2.1.2.length =
 ((oldTerm root visit recognition U7 calculus anchor :: actorTerm root visit recognition ::
   childTerm root visit recognition U7 calculus anchor stage ::
   (observerTerms root visit recognition U7 calculus anchor stage ++ gramTerms root visit recognition U7 calculus anchor stage)).map remaining).sum+
 (oldTerm root visit recognition U7 calculus anchor :: actorTerm root visit recognition ::
   childTerm root visit recognition U7 calculus anchor stage ::
   (observerTerms root visit recognition U7 calculus anchor stage ++ gramTerms root visit recognition U7 calculus anchor stage)).length :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans (programme_charge _ _ _ _)
theorem trace_fee_at : (traceAt root visit recognition U7 calculus anchor stage supplied).length =
 remaining (expression root visit recognition U7 calculus anchor stage) := execution_length _ _
theorem source_material_at : (paidAt root visit recognition U7 calculus anchor stage supplied).2.2.2 =
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
  (Observer.Live.E.Shared.base (sourceFrame root visit recognition U7 calculus anchor stage)).root.toAuthoritativeRoot supplied := rfl

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

private theorem observation_member (term) (present : term ∈ observerTerms root visit recognition U7 calculus anchor stage) :
 ∃ index : Index root recognition, ∃ kind : Fin 4, term=observationOutput root visit recognition index kind := by
 rcases List.mem_flatten.mp present with ⟨terms,inTerms,inTerm⟩
 rcases List.mem_map.mp inTerms with ⟨index,_,rfl⟩
 rcases List.mem_ofFn.mp inTerm with ⟨kind,same⟩
 exact ⟨index,kind,same.symm⟩
private theorem mapped_zero {X G : Type u} [AddCommMonoid G] (terms : List X) (read : X → G)
 (zero : ∀ term ∈ terms, read term=0) : (terms.map read).sum=0 := by
 apply List.sum_eq_zero
 intro value belongs
 rcases List.mem_map.mp belongs with ⟨term,present,rfl⟩
 exact zero term present

private theorem actor_term_value : actorRead root visit recognition
 ((actorTerm root visit recognition).eval (environmentAt root visit recognition U7 calculus anchor stage supplied)) =
 (CurrentActor.Lower.paidAt root visit recognition (sourceFrame root visit recognition U7 calculus anchor stage) supplied).2.2.1 := by
 change (embed root visit recognition (CurrentActor.actorTerm root visit recognition)).eval _ = _
 rw [embed_value]
 have sourceValue := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (Observer.Live.E.Shared.base (sourceFrame root visit recognition U7 calculus anchor stage)).root.toAuthoritativeRoot
  (fun {_current} occurrence => CurrentActor.Lower.rawAt root visit recognition
    (sourceFrame root visit recognition U7 calculus anchor stage) occurrence) supplied
 exact sourceValue.symm

theorem paid_actor_output : (paidAt root visit recognition U7 calculus anchor stage supplied).2.2.1.2.1 =
 (CurrentActor.Lower.paidAt root visit recognition (sourceFrame root visit recognition U7 calculus anchor stage) supplied).2.2.1 := by
 rw [paid_value_at]
 change actorRead root visit recognition (((oldTerm root visit recognition U7 calculus anchor :: actorTerm root visit recognition ::
   childTerm root visit recognition U7 calculus anchor stage ::
   (observerTerms root visit recognition U7 calculus anchor stage ++ gramTerms root visit recognition U7 calculus anchor stage)).map
   (fun term => term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))).sum) = _
 rw [map_list_sum]
 simp only [List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
 have oldZero : actorRead root visit recognition ((oldTerm root visit recognition U7 calculus anchor).eval
   (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have childZero : actorRead root visit recognition ((childTerm root visit recognition U7 calculus anchor stage).eval
   (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have obsZero : ∀ term ∈ observerTerms root visit recognition U7 calculus anchor stage,
  actorRead root visit recognition (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := by
  intro term present
  rcases observation_member root visit recognition U7 calculus anchor stage term present with ⟨index,kind,rfl⟩
  rfl
 have gramZero : ∀ term ∈ gramTerms root visit recognition U7 calculus anchor stage,
  actorRead root visit recognition (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := by
  intro term present
  simp only [gramTerms,List.mem_flatMap,List.mem_map] at present
  rcases present with ⟨first,_,second,_,rfl⟩
  rfl
 rw [oldZero,childZero,mapped_zero _ _ obsZero,mapped_zero _ _ gramZero,actor_term_value]
 simp only [zero_add,add_zero]

theorem paid_actor_pair : (paidAt root visit recognition U7 calculus anchor stage supplied).2.2.1.2.1.2 =
 (Finsupp.single (CurrentActor.actorAt root visit recognition U7 calculus anchor stage) 1,
  Finsupp.single (CurrentActor.nextActorAt root visit recognition U7 calculus anchor stage) 1 -
   Finsupp.single (CurrentActor.actorAt root visit recognition U7 calculus anchor stage) 1) := by
 rw [paid_actor_output]
 exact CurrentActor.supplied_actor root visit recognition U7 calculus anchor stage supplied


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
 ((observationOutput root visit recognition other channel).eval (environmentAt root visit recognition U7 calculus anchor stage supplied)) =
 if index=other then if kind=channel then observationValueAt root visit recognition U7 calculus anchor stage supplied other channel else 0 else 0 := by
 classical
 rw [observation_output_value]
 by_cases sameIndex : index=other <;> by_cases sameKind : kind=channel <;>
  simp [observationRead,observationInjection,sameIndex,sameKind]
private theorem gram_read_term (first second otherFirst otherSecond : Sample root recognition) :
 gramRead root visit recognition first second
 ((gramOutput root visit recognition otherFirst otherSecond).eval (environmentAt root visit recognition U7 calculus anchor stage supplied)) =
 if first=otherFirst then if second=otherSecond then ULift.up (inner ℂ
  (observationValueAt root visit recognition U7 calculus anchor stage supplied otherFirst.1 otherFirst.2)
  (observationValueAt root visit recognition U7 calculus anchor stage supplied otherSecond.1 otherSecond.2)) else 0 else 0 := by
 classical
 rw [gram_output_value]
 by_cases sameFirst : first=otherFirst <;> by_cases sameSecond : second=otherSecond <;>
  simp [gramRead,gramInjection,sameFirst,sameSecond]

theorem paid_observation_at
 (position : Fin (rowsAtActor root recognition (sourceActor root visit recognition U7 calculus anchor stage)).length) (kind : Fin 4) :
 (paidAt root visit recognition U7 calculus anchor stage supplied).2.2.1.2.2.1
  ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind =
 observationValueAt root visit recognition U7 calculus anchor stage supplied
  ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind := by
 classical
 rw [paid_value_at]
 change observationRead root visit recognition ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind
  (((oldTerm root visit recognition U7 calculus anchor :: actorTerm root visit recognition ::
    childTerm root visit recognition U7 calculus anchor stage ::
    (observerTerms root visit recognition U7 calculus anchor stage ++ gramTerms root visit recognition U7 calculus anchor stage)).map
    (fun term => term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))).sum) = _
 rw [map_list_sum]
 simp only [List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
 have oldZero : observationRead root visit recognition ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind
  ((oldTerm root visit recognition U7 calculus anchor).eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have actorZero : observationRead root visit recognition ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind
  ((actorTerm root visit recognition).eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have childZero : observationRead root visit recognition ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind
  ((childTerm root visit recognition U7 calculus anchor stage).eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have gramZero : ∀ term ∈ gramTerms root visit recognition U7 calculus anchor stage,
  observationRead root visit recognition ⟨sourceActor root visit recognition U7 calculus anchor stage,position⟩ kind
   (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := by
  intro term present
  simp only [gramTerms,List.mem_flatMap,List.mem_map] at present
  rcases present with ⟨first,_,second,_,rfl⟩
  rfl
 rw [oldZero,actorZero,childZero,mapped_zero _ _ gramZero,add_zero,zero_add,zero_add,zero_add]
 simp only [observerTerms,selectedIndices,indices,List.map_flatten,List.sum_flatten,List.map_ofFn,
  List.sum_ofFn,Function.comp_def,observation_read_term,position_index_eq]
 rw [Fintype.sum_eq_single position]
 · simp only [if_true]
   rw [Fintype.sum_eq_single kind]
   · simp
   · intro other different
     simp [Ne.symm different]
 · intro other different
   simp [Ne.symm different]

theorem paid_gram_at
 (first second : Fin (rowsAtActor root recognition (sourceActor root visit recognition U7 calculus anchor stage)).length × Fin 4) :
 ((paidAt root visit recognition U7 calculus anchor stage supplied).2.2.1.2.2.2
   (⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩,first.2)
   (⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩,second.2)).down =
 inner ℂ (observationValueAt root visit recognition U7 calculus anchor stage supplied
   ⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩ first.2)
  (observationValueAt root visit recognition U7 calculus anchor stage supplied
   ⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩ second.2) := by
 classical
 rw [paid_value_at]
 change (gramRead root visit recognition
   (⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩,first.2)
   (⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩,second.2)
   (((oldTerm root visit recognition U7 calculus anchor :: actorTerm root visit recognition ::
     childTerm root visit recognition U7 calculus anchor stage ::
     (observerTerms root visit recognition U7 calculus anchor stage ++ gramTerms root visit recognition U7 calculus anchor stage)).map
     (fun term => term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))).sum)).down = _
 rw [map_list_sum]
 simp only [List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
 let read := gramRead root visit recognition
   (⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩,first.2)
   (⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩,second.2)
 have oldZero : read ((oldTerm root visit recognition U7 calculus anchor).eval
  (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have actorZero : read ((actorTerm root visit recognition).eval
  (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have childZero : read ((childTerm root visit recognition U7 calculus anchor stage).eval
  (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have obsZero : ∀ term ∈ observerTerms root visit recognition U7 calculus anchor stage,
  read (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := by
  intro term present
  rcases observation_member root visit recognition U7 calculus anchor stage term present with ⟨index,kind,rfl⟩
  rfl
 change (read _ + (read _ + (read _ +
   (((observerTerms root visit recognition U7 calculus anchor stage).map
     (fun term => read (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied)))).sum +
    ((gramTerms root visit recognition U7 calculus anchor stage).map
     (fun term => read (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied)))).sum)))).down = _
 rw [oldZero,actorZero,childZero,mapped_zero _ _ obsZero,zero_add,zero_add,zero_add,zero_add]
 have observed : ((gramTerms root visit recognition U7 calculus anchor stage).map
    (fun term => read (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied)))).sum =
    ULift.up (inner ℂ
      (observationValueAt root visit recognition U7 calculus anchor stage supplied
       ⟨sourceActor root visit recognition U7 calculus anchor stage,first.1⟩ first.2)
      (observationValueAt root visit recognition U7 calculus anchor stage supplied
       ⟨sourceActor root visit recognition U7 calculus anchor stage,second.1⟩ second.2)) := by
  simp only [read,gramTerms,selectedSamples,List.map_flatMap,List.map_map,Function.comp_def,gram_read_term]
  simpa only [ite_and] using samples_delta root recognition
    (sourceActor root visit recognition U7 calculus anchor stage)
    (fun a b => ULift.up.{u} (inner ℂ
      (observationValueAt root visit recognition U7 calculus anchor stage supplied a.1 a.2)
      (observationValueAt root visit recognition U7 calculus anchor stage supplied b.1 b.2))) first second
 exact congrArg ULift.down observed

theorem child_term_value : (childTerm root visit recognition U7 calculus anchor stage).eval
 (environmentAt root visit recognition U7 calculus anchor stage supplied) =
 oldInjection root visit recognition (Observer.oldInjection root visit recognition
  ((Inventory.childExpressionAtCode root visit recognition (code root visit recognition U7 calculus anchor stage)).eval
   (Observer.Action.oldEnvironmentAt root visit recognition (sourceFrame root visit recognition U7 calculus anchor stage) supplied))) := by
 change oldInjection root visit recognition ((embed root visit recognition (Observer.oldOutputEmbed root visit recognition
  (Inventory.childExpressionAtCode root visit recognition (code root visit recognition U7 calculus anchor stage)))).eval _) = _
 rw [embed_value]
 change oldInjection root visit recognition (Observer.oldInjection root visit recognition
  ((Observer.embed root visit recognition (Inventory.childExpressionAtCode root visit recognition
    (code root visit recognition U7 calculus anchor stage))).eval
    (baseEnvironment root visit recognition U7 calculus anchor stage supplied))) = _
 rw [Observer.Action.old_embed_eval_at]

theorem child_term_fee : remaining (childTerm root visit recognition U7 calculus anchor stage) =
 Inventory.childCostAtCode root recognition (code root visit recognition U7 calculus anchor stage)+2 := by
 simp only [childTerm,oldOutputEmbed,remaining,Actor.Extension.embed_charge,Observer.oldOutputEmbed,
  Observer.embed_charge,Inventory.child_expression_cost]


private def oldRead : Output root visit recognition →+ Observer.Output root visit recognition where
 toFun value := value.1
 map_zero' := rfl
 map_add' _ _ := rfl
private theorem old_term_value : oldRead root visit recognition
 ((oldTerm root visit recognition U7 calculus anchor).eval (environmentAt root visit recognition U7 calculus anchor stage supplied)) =
 (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
  (baseEnvironment root visit recognition U7 calculus anchor stage supplied) := by
 change (embed root visit recognition (Observer.Action.observerSyntax root visit recognition U7 calculus anchor)).eval _ = _
 exact embed_value _ _ _ _ _ _ _ _ _

theorem paid_old_output : (paidAt root visit recognition U7 calculus anchor stage supplied).2.2.1.1 =
 (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
  (baseEnvironment root visit recognition U7 calculus anchor stage supplied) +
 Observer.oldInjection root visit recognition
  ((Inventory.childExpressionAtCode root visit recognition (code root visit recognition U7 calculus anchor stage)).eval
   (Observer.Action.oldEnvironmentAt root visit recognition (sourceFrame root visit recognition U7 calculus anchor stage) supplied)) := by
 rw [paid_value_at]
 change oldRead root visit recognition (((oldTerm root visit recognition U7 calculus anchor :: actorTerm root visit recognition ::
   childTerm root visit recognition U7 calculus anchor stage ::
   (observerTerms root visit recognition U7 calculus anchor stage ++ gramTerms root visit recognition U7 calculus anchor stage)).map
   (fun term => term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))).sum) = _
 rw [map_list_sum]
 simp only [List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
 have actorZero : oldRead root visit recognition ((actorTerm root visit recognition).eval
  (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := rfl
 have childValue : oldRead root visit recognition ((childTerm root visit recognition U7 calculus anchor stage).eval
   (environmentAt root visit recognition U7 calculus anchor stage supplied)) =
   Observer.oldInjection root visit recognition
    ((Inventory.childExpressionAtCode root visit recognition (code root visit recognition U7 calculus anchor stage)).eval
     (Observer.Action.oldEnvironmentAt root visit recognition (sourceFrame root visit recognition U7 calculus anchor stage) supplied)) :=
   congrArg (oldRead root visit recognition) (child_term_value root visit recognition U7 calculus anchor stage supplied)
 have obsZero : ∀ term ∈ observerTerms root visit recognition U7 calculus anchor stage,
  oldRead root visit recognition (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := by
  intro term present
  rcases observation_member root visit recognition U7 calculus anchor stage term present with ⟨index,kind,rfl⟩
  rfl
 have gramZero : ∀ term ∈ gramTerms root visit recognition U7 calculus anchor stage,
  oldRead root visit recognition (term.eval (environmentAt root visit recognition U7 calculus anchor stage supplied))=0 := by
  intro term present
  simp only [gramTerms,List.mem_flatMap,List.mem_map] at present
  rcases present with ⟨first,_,second,_,rfl⟩
  rfl
 rw [old_term_value,actorZero,childValue,mapped_zero _ _ obsZero,mapped_zero _ _ gramZero]
 simp only [zero_add,add_zero]

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
