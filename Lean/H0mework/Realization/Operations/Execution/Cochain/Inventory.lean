import H0mework.Realization.Operations.Execution.Cochain.Source
import H0mework.Realization.Operations.Execution.InventoryVector.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.SourceOperationExecution.Cochain.Inventory
open SourceOperationEffects SourceOperationScalarRelations
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {sort : S}
variable (expression : Expr Value Var sort)
def terms := SourceOperationScalarCochain.updated expression :: expression.old :: expression.mixedTerms
abbrev Index := Fin (terms expression).length
def term (index : Index expression) := (terms expression).get index
def items := List.ofFn (fun index : Index expression => (index,term expression index))
def query := InventoryVector.query (Index expression) (items expression)
variable (old increment : Env Value Var)
def environment := InventoryVector.environment (Index expression) (mixedEnvironment old increment)
def trace := execution (environment expression old increment) (query expression)
def written := ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations.exposure
 (trace expression old increment)
theorem coordinate (index : Index expression) :
 (query expression).eval (environment expression old increment) index=
 (term expression index).eval (mixedEnvironment old increment) := by
 have h := InventoryVector.query_read (Index expression) (items expression) (mixedEnvironment old increment) index
 have one : ((items expression).map (fun item => if index=item.1 then
  item.2.eval (mixedEnvironment old increment) else 0)).sum=
 (term expression index).eval (mixedEnvironment old increment) := by
  simp only [items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_ite_eq (s:=Finset.univ) index
   (fun coordinate : Index expression => (term expression coordinate).eval (mixedEnvironment old increment))
   |>.trans (if_pos (Finset.mem_univ index))
 exact h.trans one
theorem charge : (trace expression old increment).length=InventoryVector.charge (Index expression) (items expression) :=
 (execution_length _ _).trans (InventoryVector.query_charge _ _)
def updatedIndex : Index expression := ⟨0,by simp [terms]⟩
def oldIndex : Index expression := ⟨1,by simp [terms]⟩
def mixedIndex (index : Fin expression.mixedTerms.length) : Index expression := ⟨index.val+2,by
 simp only [terms,List.length_cons]
 omega⟩
theorem mixed_injective : Function.Injective (mixedIndex expression) := by
 intro a b same
 apply Fin.ext
 have h := congrArg Fin.val same
 change a.val+2=b.val+2 at h
 omega
theorem mixed_read (index : Fin expression.mixedTerms.length) :
 term expression (mixedIndex expression index)=expression.mixedTerms.get index := rfl
theorem updated_coordinate : (query expression).eval (environment expression old increment) (updatedIndex expression)=
 expression.eval (old+increment) := (coordinate expression old increment _).trans
 (SourceOperationScalarCochain.eval_updated expression old increment)
theorem old_coordinate : (query expression).eval (environment expression old increment) (oldIndex expression)=
 expression.eval old := (coordinate expression old increment _).trans (expression.eval_old old increment)
theorem mixed_coordinate (index : Fin expression.mixedTerms.length) :
 (query expression).eval (environment expression old increment) (mixedIndex expression index)=
 (expression.mixedTerms.get index).eval (mixedEnvironment old increment) := coordinate expression old increment _
theorem complete_equation : (query expression).eval (environment expression old increment) (updatedIndex expression)=
 (query expression).eval (environment expression old increment) (oldIndex expression)+
 (List.ofFn (fun index : Fin expression.mixedTerms.length =>
   (query expression).eval (environment expression old increment) (mixedIndex expression index))).sum := by
 rw [updated_coordinate,old_coordinate]
 have h : List.ofFn (fun index : Fin expression.mixedTerms.length =>
  (query expression).eval (environment expression old increment) (mixedIndex expression index))=
  expression.mixedTerms.map (fun term => term.eval (mixedEnvironment old increment)) := by
  simp only [mixed_coordinate]
  change List.ofFn ((fun term : Expr Value (ChangedVar Var) sort => term.eval (mixedEnvironment old increment)) ∘
   expression.mixedTerms.get)=_
  rw [← List.map_ofFn]
  exact congrArg (List.map (fun term : Expr Value (ChangedVar Var) sort => term.eval (mixedEnvironment old increment)))
   (List.ofFn_get expression.mixedTerms)
 rw [h]
 exact expression.eval_update_mixedTerms old increment
end SaturationMonoid.SourceOperationExecution.Cochain.Inventory
end
