import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.Consumer

open scoped BigOperators
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (frame : Inventory.Action.Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Inventory.Action.C.Occurrence frame (current:=current))

theorem embed_eval {slot : Inventory.Slot root recognition} (term : Expr (Inventory.Value root visit recognition)
    (Inventory.Variable root visit recognition) slot) :
    (embed root visit recognition term).eval (environmentAt root visit recognition frame supplied) =
      term.eval (Inventory.Action.environmentAt root visit recognition frame supplied) := by
  induction term with
  | var => rfl
  | const => rfl
  | add first second one two => exact congrArg₂ (·+·) one two
  | linear operation argument previous => exact congrArg operation previous
  | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two

theorem embed_charge {slot : Inventory.Slot root recognition} (term : Expr (Inventory.Value root visit recognition)
    (Inventory.Variable root visit recognition) slot) : remaining (embed root visit recognition term)=remaining term := by
  induction term with
  | var => rfl
  | const => rfl
  | add first second one two => simp only [embed,remaining,one,two]
  | linear operation argument previous => simp only [embed,remaining,previous]
  | bilinear operation first second one two => simp only [embed,remaining,one,two]

theorem point_term_value (row : Row root recognition) :
    (pointTerm root visit recognition row).eval (environmentAt root visit recognition frame supplied)=
      pointAt root visit recognition frame supplied row := rfl
theorem next_point_term_value (row : Row root recognition) :
    (nextPointTerm root visit recognition row).eval (environmentAt root visit recognition frame supplied)=
      nextPointAt root visit recognition frame supplied row := by
  change coordinate root recognition row
    ((embed root visit recognition (Inventory.Action.binding root visit recognition (.inr (.inl row.1)) ⟨row.2⟩)).eval
      (environmentAt root visit recognition frame supplied)) = _
  rw [embed_eval]
  rfl

theorem actual_generated_next_point_at (row : Row root recognition) :
    Inventory.Action.generatedEnvironmentAt root visit recognition frame supplied (.inr (.inl row.1)) ⟨row.2⟩ row.2 =
      nextPointAt root visit recognition frame supplied row := rfl

theorem measured_value (row : Row root recognition) :
    (measuredTerm root visit recognition row).eval (environmentAt root visit recognition frame supplied)=
      measurement root recognition row (pointAt root visit recognition frame supplied row) :=
  congrArg (measurement root recognition row) (point_term_value root visit recognition frame supplied row)
theorem next_measured_value (row : Row root recognition) :
    (nextMeasuredTerm root visit recognition row).eval (environmentAt root visit recognition frame supplied)=
      measurement root recognition row (nextPointAt root visit recognition frame supplied row) :=
  congrArg (measurement root recognition row) (next_point_term_value root visit recognition frame supplied row)
theorem coherent_value (row : Row root recognition) :
    (coherentTerm root visit recognition row).eval (environmentAt root visit recognition frame supplied)=
      evolution root recognition row (measurement root recognition row (pointAt root visit recognition frame supplied row)) :=
  congrArg (evolution root recognition row) (measured_value root visit recognition frame supplied row)
theorem residual_value (row : Row root recognition) :
    (residualTerm root visit recognition row).eval (environmentAt root visit recognition frame supplied)=
      evolution root recognition row (measurement root recognition row (pointAt root visit recognition frame supplied row)) -
        measurement root recognition row (nextPointAt root visit recognition frame supplied row) := by
  change (coherentTerm root visit recognition row).eval (environmentAt root visit recognition frame supplied) +
    (-AddMonoidHom.id (Measured (H:=H)))
      ((nextMeasuredTerm root visit recognition row).eval (environmentAt root visit recognition frame supplied)) = _
  simp only [AddMonoidHom.neg_apply,AddMonoidHom.id_apply]
  rw [coherent_value,next_measured_value]
  exact (sub_eq_add_neg _ _).symm

def observationValueAt (index : Index root visit recognition) (kind : Fin 4) :=
  let row := rowAt root visit recognition index
  match kind.val with
  | 0 => measurement root recognition row (pointAt root visit recognition frame supplied row)
  | 1 => measurement root recognition row (nextPointAt root visit recognition frame supplied row)
  | 2 => evolution root recognition row (measurement root recognition row (pointAt root visit recognition frame supplied row))
  | _ => evolution root recognition row (measurement root recognition row (pointAt root visit recognition frame supplied row)) -
      measurement root recognition row (nextPointAt root visit recognition frame supplied row)
theorem observation_term_value (index : Index root visit recognition) (kind : Fin 4) :
    (observationTerm root visit recognition index kind).eval (environmentAt root visit recognition frame supplied)=
      observationValueAt root visit recognition frame supplied index kind := by
  fin_cases kind
  · exact measured_value root visit recognition frame supplied (rowAt root visit recognition index)
  · exact next_measured_value root visit recognition frame supplied (rowAt root visit recognition index)
  · exact coherent_value root visit recognition frame supplied (rowAt root visit recognition index)
  · exact residual_value root visit recognition frame supplied (rowAt root visit recognition index)

theorem gram_term_value (first second : Sample root visit recognition) :
    (gramTerm root visit recognition first second).eval (environmentAt root visit recognition frame supplied)=
      ULift.up (inner ℂ (observationValueAt root visit recognition frame supplied first.1 first.2)
        (observationValueAt root visit recognition frame supplied second.1 second.2)) := by
  change innerOperation ((observationTerm root visit recognition first.1 first.2).eval _)
    ((observationTerm root visit recognition second.1 second.2).eval _) = _
  rw [observation_term_value,observation_term_value]
  rfl

theorem old_output_value (term : Expr (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition)
    (Inventory.resultSlot root recognition)) :
    (oldOutputEmbed root visit recognition term).eval (environmentAt root visit recognition frame supplied)=
      oldInjection root visit recognition (term.eval (Inventory.Action.environmentAt root visit recognition frame supplied)) :=
  congrArg (oldInjection root visit recognition) (embed_eval root visit recognition frame supplied term)

theorem programme_value (terms : List (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition))) :
    (programme root visit recognition terms).eval (environmentAt root visit recognition frame supplied)=
      (terms.map (fun term => term.eval (environmentAt root visit recognition frame supplied))).sum := by
  induction terms with
  | nil => rfl
  | cons first rest previous =>
      simpa only [programme,Expr.eval,List.map_cons,List.sum_cons] using
        congrArg (fun value : Output root visit recognition => first.eval (environmentAt root visit recognition frame supplied)+value) previous
theorem programme_charge (terms : List (Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition))) :
    remaining (programme root visit recognition terms)=(terms.map remaining).sum+terms.length := by
  induction terms with
  | nil => rfl
  | cons first rest previous =>
      simp only [programme,remaining,previous,List.map_cons,List.sum_cons,List.length_cons]
      omega

theorem source_value_at : (rawAt root visit recognition frame supplied).expression.eval
    (rawAt root visit recognition frame supplied).environment =
      ((oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).map
        (fun term => term.eval (environmentAt root visit recognition frame supplied))).sum := programme_value _ _ _ _ _ _
theorem paid_value_at : (paidAt root visit recognition frame supplied).2.2.1 =
    ((oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).map
      (fun term => term.eval (environmentAt root visit recognition frame supplied))).sum :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans (source_value_at _ _ _ _ _)
theorem trace_fee_at : (traceAt root visit recognition frame supplied).length =
    ((oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).map remaining).sum +
      (oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).length :=
  (execution_length _ _).trans (programme_charge _ _ _ _)
theorem paid_fee_at : (paidAt root visit recognition frame supplied).2.1.2.length =
    ((oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).map remaining).sum +
      (oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).length :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans (programme_charge _ _ _ _)
theorem source_material_at : (paidAt root visit recognition frame supplied).2.2.2 =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt (E.Shared.base frame).root.toAuthoritativeRoot supplied := rfl

theorem observation_output_value (index : Index root visit recognition) (kind : Fin 4) :
    (observationOutput root visit recognition index kind).eval (environmentAt root visit recognition frame supplied)=
      observationInjection root visit recognition index kind (observationValueAt root visit recognition frame supplied index kind) :=
  congrArg (observationInjection root visit recognition index kind) (observation_term_value root visit recognition frame supplied index kind)
theorem gram_output_value (first second : Sample root visit recognition) :
    (gramOutput root visit recognition first second).eval (environmentAt root visit recognition frame supplied)=
      gramInjection root visit recognition first second (ULift.up (inner ℂ
        (observationValueAt root visit recognition frame supplied first.1 first.2)
        (observationValueAt root visit recognition frame supplied second.1 second.2))) :=
  congrArg (gramInjection root visit recognition first second) (gram_term_value root visit recognition frame supplied first second)

private def oldRead : Output root visit recognition →+ Inventory.Output root visit recognition where
  toFun value := value.1
  map_zero' := rfl
  map_add' _ _ := rfl
private def observationRead (index : Index root visit recognition) (kind : Fin 4) :
    Output root visit recognition →+ Measured (H:=H) where
  toFun value := value.2.1 index kind
  map_zero' := rfl
  map_add' _ _ := rfl
private def gramRead (first second : Sample root visit recognition) : Output root visit recognition →+ ULift.{u} ℂ where
  toFun value := value.2.2 first second
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem old_read_term : oldRead root visit recognition
    ((oldTerm root visit recognition frame supplied).eval (environmentAt root visit recognition frame supplied)) =
    (Inventory.Action.C.materialAt frame supplied).raw.expression.eval (Inventory.Action.environmentAt root visit recognition frame supplied) := by
  change (oldInjection root visit recognition
    ((embed root visit recognition (Inventory.Action.C.materialAt frame supplied).raw.expression).eval
      (environmentAt root visit recognition frame supplied))).1 = _
  rw [embed_eval]
  rfl
private theorem observation_read_term (index : Index root visit recognition) (kind : Fin 4)
    (other : Index root visit recognition) (channel : Fin 4) :
    observationRead root visit recognition index kind
      ((observationOutput root visit recognition other channel).eval (environmentAt root visit recognition frame supplied)) =
    if index=other then if kind=channel then observationValueAt root visit recognition frame supplied other channel else 0 else 0 := by
  classical
  rw [observation_output_value]
  by_cases sameIndex : index=other <;> by_cases sameKind : kind=channel <;>
    simp [observationRead,observationInjection,sameIndex,sameKind]
private theorem gram_read_term (first second otherFirst otherSecond : Sample root visit recognition) :
    gramRead root visit recognition first second
      ((gramOutput root visit recognition otherFirst otherSecond).eval (environmentAt root visit recognition frame supplied)) =
    if first=otherFirst then if second=otherSecond then ULift.up (inner ℂ
      (observationValueAt root visit recognition frame supplied otherFirst.1 otherFirst.2)
      (observationValueAt root visit recognition frame supplied otherSecond.1 otherSecond.2)) else 0 else 0 := by
  classical
  rw [gram_output_value]
  by_cases sameFirst : first=otherFirst <;> by_cases sameSecond : second=otherSecond <;>
    simp [gramRead,gramInjection,sameFirst,sameSecond]

private theorem observation_member (term) (present : term ∈ observerTerms root visit recognition) :
    ∃ index : Index root visit recognition, ∃ kind : Fin 4, term=observationOutput root visit recognition index kind := by
  rcases List.mem_flatten.mp present with ⟨terms,inTerms,inTerm⟩
  rcases List.mem_ofFn.mp inTerms with ⟨index,same⟩
  subst terms
  rcases List.mem_ofFn.mp inTerm with ⟨kind,same⟩
  exact ⟨index,kind,same.symm⟩
private theorem mapped_zero {X G : Type u} [AddCommMonoid G] (terms : List X) (read : X → G)
    (zero : ∀ term ∈ terms, read term=0) : (terms.map read).sum=0 := by
  apply List.sum_eq_zero
  intro value belongs
  rcases List.mem_map.mp belongs with ⟨term,present,rfl⟩
  exact zero term present

private theorem samples_sum {B : Type u} [AddCommMonoid B] (f : Index root visit recognition × Fin 4 → B) :
 ((samples root visit recognition).map f).sum = ∑ i : Index root visit recognition, ∑ k : Fin 4, f (i,k) := by
 simp only [samples,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
private theorem samples_double_sum {B : Type u} [AddCommMonoid B] (f : (Index root visit recognition × Fin 4) → (Index root visit recognition × Fin 4) → B) :
 ((samples root visit recognition).flatMap (fun first => (samples root visit recognition).map (f first))).sum =
 ∑ i : Index root visit recognition, ∑ k : Fin 4, ∑ j : Index root visit recognition, ∑ l : Fin 4, f (i,k) (j,l) := by
 rw [List.flatMap_def,List.sum_flatten]
 simp only [List.map_map,Function.comp_def,samples_sum]
private theorem samples_delta {B : Type u} [AddCommMonoid B] (f : (Index root visit recognition × Fin 4) → (Index root visit recognition × Fin 4) → B)
 (first second : Index root visit recognition × Fin 4) :
 ((samples root visit recognition).flatMap (fun a => (samples root visit recognition).map (fun b => if first=a ∧ second=b then f a b else 0))).sum =
 f first second := by
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

theorem paid_old_at : (paidAt root visit recognition frame supplied).2.2.1.1 =
    (Inventory.Action.C.materialAt frame supplied).raw.expression.eval
      (Inventory.Action.environmentAt root visit recognition frame supplied) := by
  classical
  rw [paid_value_at]
  change oldRead root visit recognition ((oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).map
    (fun term => term.eval (environmentAt root visit recognition frame supplied))).sum = _
  rw [map_list_sum]
  simp only [List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append,old_read_term]
  have obsZero : ∀ term ∈ observerTerms root visit recognition,
      oldRead root visit recognition (term.eval (environmentAt root visit recognition frame supplied))=0 := by
    intro term present
    rcases observation_member root visit recognition term present with ⟨index,channel,rfl⟩
    rfl
  have gramZero : ∀ term ∈ gramTerms root visit recognition,
      oldRead root visit recognition (term.eval (environmentAt root visit recognition frame supplied))=0 := by
    intro term present
    simp only [gramTerms,List.mem_flatMap,List.mem_map] at present
    rcases present with ⟨first,_,second,_,rfl⟩
    rfl
  rw [mapped_zero _ _ obsZero,
    mapped_zero _ _ gramZero,zero_add,add_zero]

theorem paid_observation_at (index : Index root visit recognition) (kind : Fin 4) :
    (paidAt root visit recognition frame supplied).2.2.1.2.1 index kind =
      observationValueAt root visit recognition frame supplied index kind := by
  classical
  rw [paid_value_at]
  change observationRead root visit recognition index kind ((oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).map
    (fun term => term.eval (environmentAt root visit recognition frame supplied))).sum = _
  rw [map_list_sum]
  simp only [List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
  have oldZero : observationRead root visit recognition index kind
      ((oldTerm root visit recognition frame supplied).eval (environmentAt root visit recognition frame supplied))=0 := rfl
  have gramZero : ∀ term ∈ gramTerms root visit recognition,
      observationRead root visit recognition index kind (term.eval (environmentAt root visit recognition frame supplied))=0 := by
    intro term present
    simp only [gramTerms,List.mem_flatMap,List.mem_map] at present
    rcases present with ⟨first,_,second,_,rfl⟩
    rfl
  have gramSum := mapped_zero (gramTerms root visit recognition)
    (fun term => observationRead root visit recognition index kind (term.eval (environmentAt root visit recognition frame supplied))) gramZero
  rw [oldZero,gramSum,add_zero,zero_add]
  simp only [observerTerms,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def,
    observation_read_term]
  rw [Fintype.sum_eq_single index]
  · simp only [if_true]
    rw [Fintype.sum_eq_single kind]
    · simp
    · intro other different
      simp [Ne.symm different]
  · intro other different
    simp [Ne.symm different]

theorem paid_gram_at (first second : Sample root visit recognition) :
    ((paidAt root visit recognition frame supplied).2.2.1.2.2 first second).down =
      inner ℂ (observationValueAt root visit recognition frame supplied first.1 first.2)
        (observationValueAt root visit recognition frame supplied second.1 second.2) := by
  classical
  rw [paid_value_at]
  change (gramRead root visit recognition first second ((oldTerm root visit recognition frame supplied :: (observerTerms root visit recognition ++ gramTerms root visit recognition)).map
    (fun term => term.eval (environmentAt root visit recognition frame supplied))).sum).down = _
  rw [map_list_sum]
  simp only [List.map_map,Function.comp_def,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
  have oldZero : gramRead root visit recognition first second
      ((oldTerm root visit recognition frame supplied).eval (environmentAt root visit recognition frame supplied))=0 := rfl
  have obsZero : ∀ term ∈ observerTerms root visit recognition,
      gramRead root visit recognition first second (term.eval (environmentAt root visit recognition frame supplied))=0 := by
    intro term present
    rcases observation_member root visit recognition term present with ⟨index,channel,rfl⟩
    rfl
  rw [oldZero,mapped_zero _ _ obsZero,zero_add,zero_add]
  have read : ((gramTerms root visit recognition).map
      (fun term => gramRead root visit recognition first second (term.eval (environmentAt root visit recognition frame supplied)))).sum =
      ULift.up (inner ℂ (observationValueAt root visit recognition frame supplied first.1 first.2)
        (observationValueAt root visit recognition frame supplied second.1 second.2)) := by
    simp only [gramTerms,List.map_flatMap,List.map_map,Function.comp_def,gram_read_term]
    simpa only [ite_and] using samples_delta root visit recognition
      (fun a b => ULift.up.{u} (inner ℂ (observationValueAt root visit recognition frame supplied a.1 a.2)
        (observationValueAt root visit recognition frame supplied b.1 b.2))) first second
  exact congrArg ULift.down read

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem actual_born_point (stage : Nat) (index : Index root visit recognition) :
    let sourceFrame := Observer.sourceFrame root visit recognition U7 calculus stage
    let born := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn sourceFrame (Inventory.Live.programme root visit recognition U7 calculus)
    born.environment (born.old.root.emitted born.old.visit.current) (.inr (.inl (rowAt root visit recognition index).1))
      ⟨(rowAt root visit recognition index).2⟩ (rowAt root visit recognition index).2 =
    nextPointAt root visit recognition sourceFrame (sourceOccurrence root visit recognition U7 calculus stage)
      (rowAt root visit recognition index) :=
  Inventory.Live.born_environment root visit recognition _ _ |> congrArg
    (fun environment => environment (.inr (.inl (rowAt root visit recognition index).1))
      ⟨(rowAt root visit recognition index).2⟩ (rowAt root visit recognition index).2)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
