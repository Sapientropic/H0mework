import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Complete positive two-scale cone projection and finite convex dual bounds

The regular readout fiber's squared-scale geometry is a positive linear/reciprocal cone system.
This generic producer eliminates its second scale and constructs it from the projected first
scale. Finite nonnegative dual multipliers and certified square-root lower bounds control every
feasible point. No fitted point, feasible second scale or target objective bound is an input to
the projected witness constructor. The original source/root/ledger/runtime are not modified.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutFiberBounds

noncomputable section

/-- Primitive strictly positive coefficients of the two linear and two reciprocal cones. -/
structure PositiveConeSystem where
  a : Bool → ℝ
  b : Bool → ℝ
  c : Bool → ℝ
  p : Bool → ℝ
  q : Bool → ℝ
  d : Bool → ℝ
  a_positive : ∀ i, 0 < a i
  b_positive : ∀ i, 0 < b i
  c_positive : ∀ i, 0 < c i
  p_positive : ∀ j, 0 < p j
  q_positive : ∀ j, 0 < q j
  d_positive : ∀ j, 0 < d j

structure Feasible (system : PositiveConeSystem) (S T : ℝ) : Prop where
  S_positive : 0 < S
  T_positive : 0 < T
  alice : ∀ i, system.a i * S + system.b i * T ≤ system.c i
  bob : ∀ j, system.p j / S + system.q j / T ≤ system.d j

def PositiveConeSystem.denominator (system : PositiveConeSystem) (S : ℝ) (j : Bool) : ℝ :=
  system.d j * S - system.p j

def PositiveConeSystem.upper (system : PositiveConeSystem) (S : ℝ) (i : Bool) : ℝ :=
  (system.c i - system.a i * S) / system.b i

def PositiveConeSystem.lower (system : PositiveConeSystem) (S : ℝ) (j : Bool) : ℝ :=
  system.q j * S / system.denominator S j

def PositiveConeSystem.quadratic (system : PositiveConeSystem) (S : ℝ) (i j : Bool) : ℝ :=
  (system.c i - system.a i * S) * system.denominator S j - system.b i * system.q j * S

/-- Reduced first-scale conditions contain no second-scale witness. -/
structure Projected (system : PositiveConeSystem) (S : ℝ) : Prop where
  S_positive : 0 < S
  denominator_positive : ∀ j, 0 < system.denominator S j
  quadratic_nonnegative : ∀ i j, 0 ≤ system.quadratic S i j

/-- A nonnegative certified square-root lower bound gives reciprocal AM--GM, including zero weights. -/
theorem reciprocal_amgm (A B r x : ℝ) (A_nonnegative : 0 ≤ A) (B_nonnegative : 0 ≤ B)
    (r_nonnegative : 0 ≤ r) (r_square : r ^ 2 ≤ A * B) (x_positive : 0 < x) :
    2 * r ≤ A * x + B / x := by
  have product : (A * x) * (B / x) = A * B := by
    field_simp [ne_of_gt x_positive]
  have weighted_nonnegative : 0 ≤ A * x + B / x :=
    add_nonneg (mul_nonneg A_nonnegative x_positive.le) (div_nonneg B_nonnegative x_positive.le)
  have squares : (2 * r) ^ 2 ≤ (A * x + B / x) ^ 2 := by
    nlinarith [sq_nonneg (A * x - B / x)]
  exact (sq_le_sq₀ (mul_nonneg (by norm_num) r_nonnegative) weighted_nonnegative).mp squares

/-- Linear upper cones are exactly upper bounds for the second scale. -/
theorem alice_iff_upper (system : PositiveConeSystem) (S T : ℝ) (i : Bool) :
    system.a i * S + system.b i * T ≤ system.c i ↔ T ≤ system.upper S i := by
  rw [PositiveConeSystem.upper, le_div_iff₀ (system.b_positive i)]
  constructor <;> intro cone <;> nlinarith only [cone]

theorem reciprocal_cone_iff (p q d S T : ℝ) (S_positive : 0 < S) (T_positive : 0 < T) :
    p / S + q / T ≤ d ↔ q * S ≤ (d * S - p) * T := by
  have clear : (p / S + q / T) * (S * T) = p * T + q * S := by
    field_simp [ne_of_gt S_positive, ne_of_gt T_positive]
  constructor
  · intro cone
    have paid := mul_le_mul_of_nonneg_right cone (mul_pos S_positive T_positive).le
    rw [clear] at paid
    nlinarith only [paid]
  · intro cone
    have paid : (p / S + q / T) * (S * T) ≤ d * (S * T) := by
      rw [clear]
      nlinarith only [cone]
    exact le_of_mul_le_mul_right paid (mul_pos S_positive T_positive)

theorem Feasible.denominator_positive {system : PositiveConeSystem} {S T : ℝ}
    (feasible : Feasible system S T) (j : Bool) : 0 < system.denominator S j := by
  have reciprocal_positive := div_pos (system.q_positive j) feasible.T_positive
  have strict : system.p j / S < system.d j := by
    linarith only [feasible.bob j, reciprocal_positive]
  have paid := (div_lt_iff₀ feasible.S_positive).mp strict
  dsimp [PositiveConeSystem.denominator]
  linarith only [paid]

theorem bob_iff_lower (system : PositiveConeSystem) (S T : ℝ) (j : Bool)
    (S_positive : 0 < S) (T_positive : 0 < T)
    (denominator_positive : 0 < system.denominator S j) :
    system.p j / S + system.q j / T ≤ system.d j ↔ system.lower S j ≤ T := by
  rw [reciprocal_cone_iff _ _ _ _ _ S_positive T_positive,
    PositiveConeSystem.lower, div_le_iff₀ denominator_positive]
  simp only [PositiveConeSystem.denominator]
  constructor <;> intro cone <;> nlinarith only [cone]

/-- Each lower/upper pair is exactly one projected quadratic inequality. -/
theorem pair_iff_quadratic (system : PositiveConeSystem) (S : ℝ) (i j : Bool)
    (denominator_positive : 0 < system.denominator S j) :
    system.lower S j ≤ system.upper S i ↔ 0 ≤ system.quadratic S i j := by
  rw [PositiveConeSystem.lower, PositiveConeSystem.upper,
    div_le_div_iff₀ denominator_positive (system.b_positive i)]
  simp only [PositiveConeSystem.quadratic]
  constructor <;> intro pair <;> nlinarith only [pair]

/-- Every original feasible pair generates all reduced first-scale conditions. -/
theorem Feasible.projected {system : PositiveConeSystem} {S T : ℝ}
    (feasible : Feasible system S T) : Projected system S := by
  refine ⟨feasible.S_positive, feasible.denominator_positive, ?_⟩
  intro i j
  apply (pair_iff_quadratic system S i j (feasible.denominator_positive j)).mp
  have lower := (bob_iff_lower system S T j feasible.S_positive feasible.T_positive
    (feasible.denominator_positive j)).mp (feasible.bob j)
  have upper := (alice_iff_upper system S T i).mp (feasible.alice i)
  exact lower.trans upper

def PositiveConeSystem.selectedT (system : PositiveConeSystem) (S : ℝ) : ℝ :=
  max (system.lower S false) (system.lower S true)

/-- The projected conditions internally generate a positive feasible second scale. -/
theorem projected_generates_feasible (system : PositiveConeSystem) (S : ℝ)
    (projected : Projected system S) : Feasible system S (system.selectedT S) := by
  have lower_positive : ∀ j, 0 < system.lower S j := fun j =>
    div_pos (mul_pos (system.q_positive j) projected.S_positive) (projected.denominator_positive j)
  have selected_positive : 0 < system.selectedT S :=
    (lower_positive false).trans_le (le_max_left _ _)
  have lower_selected : ∀ j, system.lower S j ≤ system.selectedT S := by
    intro j
    cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have selected_upper : ∀ i, system.selectedT S ≤ system.upper S i := by
    intro i
    exact max_le
      ((pair_iff_quadratic system S i false (projected.denominator_positive false)).mpr
        (projected.quadratic_nonnegative i false))
      ((pair_iff_quadratic system S i true (projected.denominator_positive true)).mpr
        (projected.quadratic_nonnegative i true))
  exact
    { S_positive := projected.S_positive
      T_positive := selected_positive
      alice := fun i => (alice_iff_upper system S _ i).mpr (selected_upper i)
      bob := fun j => (bob_iff_lower system S _ j projected.S_positive selected_positive
        (projected.denominator_positive j)).mpr (lower_selected j) }

/-- Complete elimination: projected quadratics are necessary and sufficient for some positive T. -/
theorem feasible_iff_projected (system : PositiveConeSystem) (S : ℝ) :
    (∃ T, Feasible system S T) ↔ Projected system S := by
  constructor
  · rintro ⟨T, feasible⟩
    exact feasible.projected
  · intro projected
    exact ⟨system.selectedT S, projected_generates_feasible system S projected⟩

def dualC (system : PositiveConeSystem) (objectiveA sigma : ℝ) (theta : Bool → ℝ) : ℝ :=
  sigma * objectiveA + ∑ i : Bool, theta i * system.a i

def dualD (system : PositiveConeSystem) (objectiveB sigma : ℝ) (theta : Bool → ℝ) : ℝ :=
  sigma * objectiveB + ∑ i : Bool, theta i * system.b i

def dualP (system : PositiveConeSystem) (lambda : Bool → ℝ) : ℝ :=
  ∑ j : Bool, lambda j * system.p j

def dualQ (system : PositiveConeSystem) (lambda : Bool → ℝ) : ℝ :=
  ∑ j : Bool, lambda j * system.q j

def dualK (system : PositiveConeSystem) (theta lambda : Bool → ℝ) : ℝ :=
  (∑ i : Bool, theta i * system.c i) + ∑ j : Bool, lambda j * system.d j

theorem dualP_nonnegative (system : PositiveConeSystem) (lambda : Bool → ℝ)
    (lambda_nonnegative : ∀ j, 0 ≤ lambda j) : 0 ≤ dualP system lambda :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (lambda_nonnegative j) (system.p_positive j).le)

theorem dualQ_nonnegative (system : PositiveConeSystem) (lambda : Bool → ℝ)
    (lambda_nonnegative : ∀ j, 0 ≤ lambda j) : 0 ≤ dualQ system lambda :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (lambda_nonnegative j) (system.q_positive j).le)

/-- Weighted feasibility pays the complete four-cone Lagrangian at every feasible point. -/
theorem dual_core_bound (system : PositiveConeSystem) (objectiveA objectiveB sigma S T : ℝ)
    (theta lambda : Bool → ℝ) (theta_nonnegative : ∀ i, 0 ≤ theta i)
    (lambda_nonnegative : ∀ j, 0 ≤ lambda j) (feasible : Feasible system S T) :
    dualC system objectiveA sigma theta * S + dualD system objectiveB sigma theta * T +
      dualP system lambda / S + dualQ system lambda / T - dualK system theta lambda ≤
        sigma * (objectiveA * S + objectiveB * T) := by
  have alice_paid : (∑ i : Bool, theta i * (system.a i * S + system.b i * T)) ≤
      ∑ i : Bool, theta i * system.c i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (feasible.alice i) (theta_nonnegative i))
  have bob_paid : (∑ j : Bool, lambda j * (system.p j / S + system.q j / T)) ≤
      ∑ j : Bool, lambda j * system.d j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (feasible.bob j) (lambda_nonnegative j))
  calc
    _ = sigma * (objectiveA * S + objectiveB * T) +
        ((∑ i : Bool, theta i * (system.a i * S + system.b i * T)) -
          ∑ i : Bool, theta i * system.c i) +
        ((∑ j : Bool, lambda j * (system.p j / S + system.q j / T)) -
          ∑ j : Bool, lambda j * system.d j) := by
      simp [dualC, dualD, dualP, dualQ, dualK]
      ring
    _ ≤ _ := by linarith only [alice_paid, bob_paid]

/-- A finite convex dual certificate bounds the signed objective over the complete feasible set. -/
theorem dual_certificate_bound (system : PositiveConeSystem)
    (objectiveA objectiveB sigma S T rS rT : ℝ) (theta lambda : Bool → ℝ)
    (theta_nonnegative : ∀ i, 0 ≤ theta i) (lambda_nonnegative : ∀ j, 0 ≤ lambda j)
    (C_nonnegative : 0 ≤ dualC system objectiveA sigma theta)
    (D_nonnegative : 0 ≤ dualD system objectiveB sigma theta)
    (rS_nonnegative : 0 ≤ rS) (rT_nonnegative : 0 ≤ rT)
    (rS_square : rS ^ 2 ≤ dualC system objectiveA sigma theta * dualP system lambda)
    (rT_square : rT ^ 2 ≤ dualD system objectiveB sigma theta * dualQ system lambda)
    (feasible : Feasible system S T) :
    2 * (rS + rT) - dualK system theta lambda ≤ sigma * (objectiveA * S + objectiveB * T) := by
  have first := reciprocal_amgm (dualC system objectiveA sigma theta) (dualP system lambda) rS S
    C_nonnegative (dualP_nonnegative system lambda lambda_nonnegative)
    rS_nonnegative rS_square feasible.S_positive
  have second := reciprocal_amgm (dualD system objectiveB sigma theta) (dualQ system lambda) rT T
    D_nonnegative (dualQ_nonnegative system lambda lambda_nonnegative)
    rT_nonnegative rT_square feasible.T_positive
  have paid := dual_core_bound system objectiveA objectiveB sigma S T theta lambda
    theta_nonnegative lambda_nonnegative feasible
  linarith only [first, second, paid]

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutFiberBounds
