import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralPrimitives

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralFeed
open PreparationVacuumLiteralAdmission PreparationVacuumNumericSource PreparationVacuumArenaRows
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumCentralBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineBudget PreparationVacuumArenaBudget
open PreparationVacuumMoyalBudget PreparationVacuumClockBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators

structure PrimitiveDominates {k : ℕ} (A B : PrimitiveArrays k) : Prop where
  leaf : ∀ d j,Dominates (A.leaf d j) (B.leaf d j)
  clock : ∀ l a,Dominates (A.clock l a) (B.clock l a)
  central : ∀ c,Dominates (A.central c) (B.central c)

theorem expressionArray_mono {k : ℕ} (A B : PrimitiveArrays k)
    (positive : PrimitiveNonnegative A) (dom : PrimitiveDominates A B) (e : ArenaExpression k) :
    Dominates (expressionArray A e) (expressionArray B e) := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>Dominates (expressionArray A e) (expressionArray B e))
    (motive_2:=fun word=>Dominates (orderedArray (word.map (expressionArray A)))
      (orderedArray (word.map (expressionArray B)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c m;exact le_rfl
  · intro d j;exact dom.leaf d j
  · intro l a;exact dom.clock l a
  · intro r e f he hf m
    change moyalScale r*convolution m r (expressionArray A e) (expressionArray A f) ≤
      moyalScale r*convolution m r (expressionArray B e) (expressionArray B f)
    apply mul_le_mul_of_nonneg_left _ (by unfold moyalScale;positivity)
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (he _) (Nat.cast_nonneg _)) (hf _)
      (expressionArray_nonnegative A positive f _)
      (mul_nonneg (Nat.cast_nonneg _) ((expressionArray_nonnegative A positive e _).trans (he _)))
  · intro c word ih
    rw [expressionArray_row,expressionArray_row]
    exact product_mono _ _ _ _ (positive.central c)
      (orderedArray_nonnegative _ (by
        intro b hb
        obtain ⟨e,he,rfl⟩:=List.mem_map.mp hb
        exact expressionArray_nonnegative A positive e)) (dom.central c) ih
  · intro e f he hf m;exact add_le_add (he m) (hf m)
  · intro m;exact le_rfl
  · intro e word he ih
    exact product_mono _ _ _ _ (expressionArray_nonnegative A positive e)
      (orderedArray_nonnegative _ (by
        intro b hb
        obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hb
        exact expressionArray_nonnegative A positive f)) he ih

theorem literal_primitive_dominates : PrimitiveDominates sourcePrimitiveArrays literalPrimitiveArrays where
  leaf:=literal_leaf_dominates
  clock _ _ _:=le_rfl
  central _ _:=le_rfl

def literalExpressionArray (e : ArenaExpression 0) : PreparationVacuumCentralBudget.ArrayBound :=
  expressionArray literalPrimitiveArrays e

theorem source_expression_admitted (e : ArenaExpression 0) :
    Dominates (expressionArray sourcePrimitiveArrays e) (literalExpressionArray e) :=
  expressionArray_mono sourcePrimitiveArrays literalPrimitiveArrays source_primitive_nonnegative
    literal_primitive_dominates e

theorem literalExpressionArray_nonnegative (e : ArenaExpression 0) : Nonnegative (literalExpressionArray e) :=
  expressionArray_nonnegative literalPrimitiveArrays literal_primitive_nonnegative e

-- This is the original ordered word fold: coefficient first, then each atom.
theorem literal_row_fold (c : NormalizedCoefficient) (word : List (ArenaExpression 0)) :
    literalExpressionArray (.row c word)=productArray (sourceCentralArray c)
      ((word.map literalExpressionArray).foldr productArray (constantArray 1)) :=
  expressionArray_row literalPrimitiveArrays c word

theorem literal_moyal_fold (r : ℕ) (e f : ArenaExpression 0) (m : ℕ) :
    literalExpressionArray (.moyal r e f) m=
      ((100 : ℝ)^r/(r.factorial : ℝ))*
        productArray (fun a=>literalExpressionArray e (a+r))
          (fun a=>literalExpressionArray f (a+r)) m := by
  simp only [literalExpressionArray,expressionArray_moyal,moyalScale,convolution,productArray,Nat.add_comm]

theorem actual_literal_expression_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (e : ArenaExpression 0) (M : ℕ) :
    ComplexJetBound (arenaEvaluate e) M (literalExpressionArray e) (z,WithLp.toLp 2 u) :=
  actual_expression_budget literalPrimitiveArrays literal_primitive_nonnegative
    (derivativeDemand e M) _ (sourceUnit_admitted z u zbox ubox unit)
    (literal_primitive_bounds z u zbox ubox unit (derivativeDemand e M)) e M le_rfl

end LowEnergy.PreparationVacuumLiteralFeed
