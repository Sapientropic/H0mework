import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCacheWordOrder

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceCacheRules
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaCollect
open PreparationVacuumMoyalNormalization PreparationVacuumClockSymbol PreparationVacuumArenaRows
open scoped BigOperators Topology

def cacheProduct {k : ℕ} (left right : AtomLabel k) : ArenaExpression k :=
  .row (polynomialCoefficient 1) (orderedRow (polynomialCoefficient 1) [left,right]).word

theorem cacheProduct_source {k : ℕ} (left right : AtomLabel k) (x : Phase) :
    arenaEvaluate (cacheProduct left right) x=
      complexMoyal 0 (arenaEvaluate left.expression) (arenaEvaluate right.expression) x := by
  have source:=orderedRow_source (polynomialCoefficient 1) [left,right] x
  have same : arenaEvaluate (cacheProduct left right) x=
      rowValue (orderedRow (polynomialCoefficient 1) [left,right]) x := by
    simp only [cacheProduct,orderedRow,arenaEvaluate_row,rowValue,orderedProduct,List.foldr_map]
  rw [same,source,complexMoyal_zero]
  simp only [wordValue,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    polynomialCoefficient_source,polynomialSymbol,map_one,Complex.ofReal_one,one_mul]

def originalSwap {k : ℕ} (left right : AtomLabel k) : Bool :=
  (!left.central && right.central) || (left.central && right.central && decide (left.serial>right.serial))

def cachePairCore {k : ℕ} (r : ℕ) (left right : AtomLabel k) : ArenaExpression k := by
  classical
  exact if r=0 then cacheProduct left right else
    if left.expression=.literal 1 ∨ right.expression=.literal 1 then .literal 0 else
    if left.central && right.central && decide (Odd r ∧ left.expression=right.expression) then .literal 0 else
    if originalSwap left right then
      arenaProduct (.literal ((-1 : ℝ)^r)) (.moyal r right.expression left.expression)
    else .moyal r left.expression right.expression

theorem cachePairCore_source {k : ℕ} (r : ℕ) (left right : AtomLabel k) (x : Phase) :
    arenaEvaluate (cachePairCore r left right) x=
      complexMoyal r (arenaEvaluate left.expression) (arenaEvaluate right.expression) x := by
  classical
  unfold cachePairCore
  split_ifs with zero identity diagonal swapped
  · subst r;exact cacheProduct_source left right x
  · obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero zero
    rcases identity with h|h
    · rw [h];exact (arena_moyal_constant_left n 1 right.expression x).symm
    · rw [h];exact (arena_moyal_constant_right n 1 left.expression x).symm
  · have normalized : (left.central=true ∧ right.central=true) ∧
        (Odd r ∧ left.expression=right.expression) := by
      simpa only [Bool.and_eq_true,decide_eq_true_eq] using diagonal
    have pair : Odd r ∧ left.expression=right.expression := normalized.2
    obtain ⟨⟨n,hn⟩,same⟩:=pair
    have order : r=2*n+1 := by omega
    rw [order,same]
    exact (arena_moyal_odd_self n right.expression x).symm
  · simp only [arenaProduct_evaluate,arenaEvaluate_literal,arenaEvaluate_moyal,
      Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
    rw [complexMoyal_swap r (arenaEvaluate left.expression) (arenaEvaluate right.expression) x,
      ←mul_assoc,←mul_pow]
    norm_num
  · rfl

theorem cachePairCore_label_independent {k : ℕ} (r : ℕ) (left right otherLeft otherRight : AtomLabel k)
    (leftSource : left.expression=otherLeft.expression) (rightSource : right.expression=otherRight.expression)
    (x : Phase) : arenaEvaluate (cachePairCore r left right) x=
      arenaEvaluate (cachePairCore r otherLeft otherRight) x := by
  rw [cachePairCore_source,cachePairCore_source,leftSource,rightSource]

theorem cachePairCore_germ {k : ℕ} (r : ℕ) (left right : AtomLabel k) (x : Phase) :
    arenaEvaluate (cachePairCore r left right)=ᶠ[𝓝 x]
      complexMoyal r (arenaEvaluate left.expression) (arenaEvaluate right.expression) :=
  Filter.Eventually.of_forall (cachePairCore_source r left right)

end LowEnergy.PreparationVacuumSourceCacheRules
