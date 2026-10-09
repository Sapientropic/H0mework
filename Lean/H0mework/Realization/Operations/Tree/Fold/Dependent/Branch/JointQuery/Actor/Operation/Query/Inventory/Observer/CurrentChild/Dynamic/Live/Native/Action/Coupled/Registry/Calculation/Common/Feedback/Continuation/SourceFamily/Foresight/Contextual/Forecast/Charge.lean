import H0mework.Realization.Operations.Execution.Coefficients.Words

set_option autoImplicit false
noncomputable section
universe u v w d

namespace SaturationMonoid.SourceOperationExecution.Coefficients.SourceCharge
open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift

theorem integer_charge (integer : ℤ) (argumentCost : Nat) (present : integer ≠ 0) :
    1 ≤ Coefficients.integerSourceCost integer argumentCost := by
  cases integer with
  | ofNat count =>
    cases count with
    | zero => exact (present rfl).elim
    | succ count =>
      change 1 ≤ (count+1)*(argumentCost+1)
      exact Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.succ_pos count) (Nat.succ_pos argumentCost))
  | negSucc count =>
    change 1 ≤ (count+1)*(argumentCost+1)+1
    omega

variable {S : Type u} {Value : S → Type v} {Var : S → Type w}
variable [∀ t, AddCommGroup (Value t)] {sort : S}

theorem nonzero_word_charge (word : Formal ℤ Value Var sort) (present : word ≠ 0) :
    2 ≤ Coefficients.cost word := by
  classical
  cases items : word.support.toList with
  | nil =>
    exact (present (Finsupp.support_eq_empty.mp (Finset.toList_eq_nil.mp items))).elim
  | cons argument rest =>
    have inList : argument ∈ word.support.toList := by
      rw [items]
      exact List.mem_cons_self
    have coefficient : word argument ≠ 0 :=
      Finsupp.mem_support_iff.mp (Finset.mem_toList.mp inList)
    have charged := integer_charge (word argument) (remaining argument) coefficient
    rw [Coefficients.cost,Coefficients.sourceItems,items]
    change 2 ≤ Coefficients.integerSourceCost (word argument) (remaining argument) +
      Coefficients.termsCost (rest.map (fun term => (term,word term))) + 1
    omega

theorem expression_charge (word : Formal ℤ Value Var sort) (present : word ≠ 0) :
    2 ≤ remaining (Coefficients.expression word) :=
  (nonzero_word_charge word present).trans_eq (Coefficients.expression_remaining word).symm

theorem lifted_expression_charge (word : Formal ℤ Value Var sort) (present : word ≠ 0) :
    2 ≤ remaining (liftExpr (Coefficients.expression word)) :=
  (nonzero_word_charge word present).trans_eq (Coefficients.lifted_remaining word).symm

theorem full_trace_charge (word : Formal ℤ Value Var sort) (environment : Env Value Var)
    (present : word ≠ 0) :
    2 ≤ (Coefficients.expressionTrace word environment).length :=
  (nonzero_word_charge word present).trans_eq (Coefficients.expressionTrace_cost word environment).symm

theorem charge_of_nonzero_image {D : Type d} [AddCommGroup D] [Module ℤ D]
    (sourceMap : Formal ℤ Value Var sort →ₗ[ℤ] D) (word : Formal ℤ Value Var sort)
    (present : sourceMap word ≠ 0) : 2 ≤ Coefficients.cost word :=
  nonzero_word_charge word (fun zero => present (zero ▸ sourceMap.map_zero))

theorem zero_word_cost : Coefficients.cost (0 : Formal ℤ Value Var sort) = 0 := by
  simp only [Coefficients.cost,Coefficients.sourceItems,Finsupp.support_zero,
    Finset.toList_empty,List.map_nil,Coefficients.termsCost]

end SaturationMonoid.SourceOperationExecution.Coefficients.SourceCharge
end
