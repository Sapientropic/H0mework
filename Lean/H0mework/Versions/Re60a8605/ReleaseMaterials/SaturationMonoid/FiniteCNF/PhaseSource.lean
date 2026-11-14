import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
The original clause residuals generate a Boolean character. Summing its actual
dual indices restores the complete original zero projector. The finite sums are
semantic consumers; their cardinalities are not machine-step budgets.
-/

namespace SaturationMonoid.ComplexityProjection.SATSource.PhaseSource

open scoped BigOperators

def bit (value : Bool) : ℤ := if value then 1 else 0

def sign (value : Bool) : ℤ := if value then -1 else 1

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl
@[simp] theorem sign_false : sign false = 1 := rfl
@[simp] theorem sign_true : sign true = -1 := rfl

theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b - 2 * bit a * bit b := by
  cases a <;> cases b <;> rfl

theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by
  cases a <;> cases b <;> rfl

theorem sign_eq_one_sub_two_mul_bit (a : Bool) : sign a = 1 - 2 * bit a := by
  cases a <;> rfl

theorem sign_xor (a b : Bool) : sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> rfl

theorem sign_foldl (values : List Bool) (initial : Bool) :
    sign (values.foldl Bool.xor initial) = sign initial * (values.map sign).prod := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, sign_xor]
      ring

def character {m : Nat} (residual dual : Fin m → Bool) : ℤ :=
  ∏ j : Fin m, sign (dual j && residual j)

theorem character_eq_sign_xor_fold {m : Nat} (residual dual : Fin m → Bool) :
    character residual dual =
      sign ((List.ofFn fun j => dual j && residual j).foldl Bool.xor false) := by
  rw [sign_foldl]
  simp [character, List.map_ofFn, List.prod_ofFn]

theorem sum_character {m : Nat} (residual : Fin m → Bool) :
    ∑ dual : Fin m → Bool, character residual dual =
      if ∀ j, residual j = false then (2 : ℤ) ^ m else 0 := by
  classical
  unfold character
  rw [← Fintype.prod_sum (fun j b => sign (b && residual j))]
  by_cases vanished : ∀ j, residual j = false
  · simp [vanished]
  · rw [if_neg vanished]
    obtain ⟨j, notFalse⟩ := not_forall.mp vanished
    have isTrue : residual j = true := Bool.eq_true_of_not_eq_false notFalse
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [isTrue]

/-- Both branch amplitudes remain in the weighted one-bit interference. -/
theorem weighted_bit (weight : Bool → ℤ) (constant linear : Bool) :
    (∑ x : Bool, weight x * sign (constant ^^ (x && linear))) =
      sign constant * (weight false + sign linear * weight true) := by
  cases constant <;> cases linear <;> simp <;> ring

/-- Four actual cofactor weights are retained, including the bilinear phase. -/
theorem weighted_pair (weight : Bool → Bool → ℤ) (constant left right joint : Bool) :
    (∑ x : Bool, ∑ y : Bool,
      weight x y * sign (constant ^^ ((x && left) ^^ ((y && right) ^^
        ((x && y) && joint))))) =
      sign constant * (weight false false + sign right * weight false true +
        sign left * weight true false + sign (left ^^ (right ^^ joint)) * weight true true) := by
  cases constant <;> cases left <;> cases right <;> cases joint <;>
    simp <;> ring

def residual {n : Nat} (formula : CNFFormula n) (assignment : Assignment n)
    (j : Fin formula.length) : Bool :=
  !(CNFClause.eval (formula.get j) (extendAssignment assignment))

def phaseSign {n : Nat} (formula : CNFFormula n) (assignment : Assignment n)
    (dual : Fin formula.length → Bool) : ℤ :=
  character (residual formula assignment) dual

theorem residual_all_false_iff {n : Nat} (formula : CNFFormula n)
    (assignment : Assignment n) :
    (∀ j, residual formula assignment j = false) ↔
      CNFFormula.eval formula (extendAssignment assignment) = true := by
  simp only [residual, CNFFormula.eval, List.all_eq_true]
  constructor
  · intro vanished clause member
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp member
    exact Bool.eq_true_of_not_eq_false' (vanished j)
  · intro satisfies j
    rw [satisfies _ (List.get_mem formula j)]
    rfl

theorem dual_sum {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    (∑ dual : Fin formula.length → Bool, phaseSign formula assignment dual) =
      (2 : ℤ) ^ formula.length *
        if CNFFormula.eval formula (extendAssignment assignment) then 1 else 0 := by
  change (∑ dual : Fin formula.length → Bool, character (residual formula assignment) dual) = _
  simp only [sum_character, residual_all_false_iff]
  split_ifs <;> simp

/-- The original assignment and original clause index own disjoint raw addresses. -/
def pack {n m : Nat} (assignment : Assignment n) (dual : Fin m → Bool) : Nat → Bool :=
  fun address => if hx : address < n then assignment ⟨address, hx⟩
    else if hy : address - n < m then dual ⟨address - n, hy⟩ else false

@[simp] theorem pack_source {n m : Nat} (assignment : Assignment n)
    (dual : Fin m → Bool) (address : Fin n) :
    pack assignment dual address.val = assignment address := by
  simp [pack, address.isLt]

@[simp] theorem pack_dual {n m : Nat} (assignment : Assignment n)
    (dual : Fin m → Bool) (address : Fin m) :
    pack assignment dual (n + address.val) = dual address := by
  simp [pack, Nat.not_lt.mpr (Nat.le_add_right n address.val), address.isLt]

noncomputable def dualAction {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  fun assignment => ∑ dual : Fin formula.length → Bool,
    (phaseSign formula assignment dual : ℚ) * source assignment

/-- The complete dual action equals the original projector on every source value. -/
theorem dualAction_eq_projector {n : Nat} (formula : CNFFormula n) (source : Source n) :
    dualAction formula source = (2 : ℚ) ^ formula.length • zeroProjector formula source := by
  funext assignment
  simp only [dualAction, ← Finset.sum_mul, ← Int.cast_sum, dual_sum,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Pi.smul_apply, smul_eq_mul,
    zeroProjector_apply]
  split_ifs <;> norm_num

def numerator {n : Nat} (formula : CNFFormula n) : ℤ :=
  ∑ assignment : Assignment n, ∑ dual : Fin formula.length → Bool,
    phaseSign formula assignment dual

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedFiniteEffectiveCoefficient

/-- The full integer numerator retains the original zero-energy multiplicity. -/
theorem numerator_eq_coefficient {n : Nat} (formula : CNFFormula n) :
    numerator formula = (2 : ℤ) ^ formula.length *
      (effectiveCoefficient (violationCount formula) 0 : ℤ) := by
  simp only [numerator, dual_sum, ← Finset.mul_sum, effectiveCoefficient_eq_card_filter,
    violationCount_eq_zero_iff_eval]
  congr 1
  simp only [Finset.sum_boole]

theorem numerator_pos_iff_satisfiable {n : Nat} (formula : CNFFormula n) :
    0 < numerator formula ↔ CNFSatisfiable formula := by
  rw [numerator_eq_coefficient]
  have powerPositive : (0 : ℤ) < 2 ^ formula.length := pow_pos (by norm_num) _
  rw [mul_pos_iff_of_pos_left powerPositive, Int.natCast_pos]
  exact effectiveCoefficient_pos_iff_satisfiable formula

theorem numerator_eq_zero_iff_unsatisfiable {n : Nat} (formula : CNFFormula n) :
    numerator formula = 0 ↔ ¬ CNFSatisfiable formula := by
  rw [numerator_eq_coefficient]
  have powerNonzero : (2 : ℤ) ^ formula.length ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_eq_zero, or_iff_right powerNonzero, Int.natCast_eq_zero]
  exact effectiveCoefficient_eq_zero_iff_unsatisfiable formula

end SaturationMonoid.ComplexityProjection.SATSource.PhaseSource
