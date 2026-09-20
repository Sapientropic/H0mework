import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import H0mework.Physics.MotherProgrammesFormationCollision.Operator

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CollisionHistory

open Matrix

noncomputable section

/-- Coordinate zero is retained; coordinate `i.succ` is emission at visit `i`. -/
abbrev H (depth : ℕ) := Fin (depth + 1) → ℂ

def energy {depth : ℕ} (v : H depth) : ℝ :=
  ∑ i : Fin (depth + 1), Complex.normSq (v i)

def emittedEnergy {depth : ℕ} (v : H depth) : ℝ :=
  ∑ i : Fin depth, Complex.normSq (v i.succ)

theorem energy_decomposition {depth : ℕ} (v : H depth) :
    energy v = Complex.normSq (v 0) + emittedEnergy v := by
  exact Fin.sum_univ_succ _

/-- The local collision appends one fresh channel; its input amplitude is zero. -/
def step (a b : ℂ) {depth : ℕ} (v : H depth) : H (depth + 1) :=
  Fin.cons (a * v 0) (Fin.snoc (fun i : Fin depth => v i.succ) (b * v 0))

@[simp] theorem step_retained (a b : ℂ) {depth : ℕ} (v : H depth) :
    step a b v 0 = a * v 0 := rfl

@[simp] theorem step_old_emitted (a b : ℂ) {depth : ℕ} (v : H depth)
    (i : Fin depth) : step a b v i.castSucc.succ = v i.succ := by
  simp [step]

@[simp] theorem step_fresh_emitted (a b : ℂ) {depth : ℕ} (v : H depth) :
    step a b v (Fin.last (depth + 1)) = b * v 0 := by
  change step a b v (Fin.last depth).succ = b * v 0
  simp only [step, Fin.cons_succ, Fin.snoc_last]

theorem fresh_channel_not_old {depth : ℕ} (i : Fin depth) :
    (Fin.last depth).succ ≠ i.castSucc.succ := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at hval
  omega

theorem fresh_channel_recovers_visit (depth : ℕ) :
    ((Fin.last depth).succ : Fin (depth + 2)).val - 1 = depth := by
  simp

theorem emittedEnergy_step (a b : ℂ) {depth : ℕ} (v : H depth) :
    emittedEnergy (step a b v) =
      emittedEnergy v + Complex.normSq b * Complex.normSq (v 0) := by
  unfold emittedEnergy
  rw [Fin.sum_univ_castSucc]
  simp [Complex.normSq_mul]

/-- Conservation holds on the entire carrier, including every earlier emission. -/
theorem energy_step (a b : ℂ) (unit : Complex.normSq a + Complex.normSq b = 1)
    {depth : ℕ} (v : H depth) : energy (step a b v) = energy v := by
  rw [energy_decomposition, step_retained, emittedEnergy_step, energy_decomposition,
    Complex.normSq_mul]
  have balance := congrArg (fun t : ℝ => t * Complex.normSq (v 0)) unit
  nlinarith only [balance]

theorem step_sub (a b : ℂ) {depth : ℕ} (v w : H depth) :
    step a b (v - w) = step a b v - step a b w := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [step, mul_sub]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [step, mul_sub]
    · simp [step]

/-- Squared Hilbert distance is preserved, not only the energy of the seed. -/
theorem energy_difference_step (a b : ℂ)
    (unit : Complex.normSq a + Complex.normSq b = 1)
    {depth : ℕ} (v w : H depth) :
    energy (step a b v - step a b w) = energy (v - w) := by
  rw [← step_sub]
  exact energy_step a b unit (v - w)

/-- Only the finite current is consumed when producing its next finite current. -/
def generated (a b z : ℂ) : (depth : ℕ) → H depth
  | 0 => fun _ => z
  | depth + 1 => step a b (generated a b z depth)

theorem generated_retained (a b z : ℂ) (depth : ℕ) :
    generated a b z depth 0 = a ^ depth * z := by
  induction depth with
  | zero => simp [generated]
  | succ depth ih =>
      simp only [generated, step_retained, ih, pow_succ']
      ring

/-- Every emission has its original visit index and original complex amplitude. -/
theorem generated_emitted (a b z : ℂ) (depth : ℕ) (i : Fin depth) :
    generated a b z depth i.succ = b * (a ^ i.val * z) := by
  induction depth with
  | zero => exact Fin.elim0 i
  | succ depth ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [generated, generated_retained]
      · simpa only [generated, step_old_emitted, Fin.val_castSucc] using ih j

theorem generated_energy (a b z : ℂ)
    (unit : Complex.normSq a + Complex.normSq b = 1) (depth : ℕ) :
    energy (generated a b z depth) = Complex.normSq z := by
  induction depth with
  | zero => simp [energy, generated]
  | succ depth ih =>
      rw [generated, energy_step a b unit]
      exact ih

theorem generated_retained_energy (a b z : ℂ) (depth : ℕ) :
    Complex.normSq (generated a b z depth 0) =
      Complex.normSq a ^ depth * Complex.normSq z := by
  rw [generated_retained, Complex.normSq_mul, map_pow]

theorem generated_emitted_energy (a b z : ℂ) (depth : ℕ) (i : Fin depth) :
    Complex.normSq (generated a b z depth i.succ) =
      Complex.normSq b * (Complex.normSq a ^ i.val * Complex.normSq z) := by
  rw [generated_emitted, Complex.normSq_mul, Complex.normSq_mul, map_pow]

theorem generated_history_energy (a b z : ℂ)
    (unit : Complex.normSq a + Complex.normSq b = 1) (depth : ℕ) :
    emittedEnergy (generated a b z depth) =
      (1 - Complex.normSq a ^ depth) * Complex.normSq z := by
  have total := generated_energy a b z unit depth
  rw [energy_decomposition, generated_retained_energy] at total
  nlinarith

theorem generated_history_prefix (a b z : ℂ) {earlier later : ℕ}
    (order : earlier ≤ later) (i : Fin earlier) :
    generated a b z later (Fin.castLE order i).succ =
      generated a b z earlier i.succ := by
  rw [generated_emitted, generated_emitted]
  rfl

/-- The visit count is part of the finite source, even when amplitudes coincide. -/
structure Current where
  depth : ℕ
  wave : H depth

def Current.next (a b : ℂ) (current : Current) : Current :=
  ⟨current.depth + 1, step a b current.wave⟩

def currentAt (a b z : ℂ) (depth : ℕ) : Current :=
  ⟨depth, generated a b z depth⟩

theorem currentAt_next (a b z : ℂ) (depth : ℕ) :
    (currentAt a b z depth).next a b = currentAt a b z (depth + 1) := rfl

theorem next_visit_distinct (a b : ℂ) (current : Current) :
    current.next a b ≠ current := by
  intro same
  have h := congrArg Current.depth same
  change current.depth + 1 = current.depth at h
  omega

theorem currentAt_injective (a b z : ℂ) : Function.Injective (currentAt a b z) := by
  intro earlier later same
  exact congrArg Current.depth same

theorem collision_balance :
    Complex.normSq ContactCollision.a + Complex.normSq ContactCollision.b = 1 := by
  rw [ContactCollision.normSq_a, ContactCollision.normSq_b]
  norm_num

/-- The two changing coordinates are this same operator acting on a fresh zero input. -/
theorem step_from_actual_operator {depth : ℕ} (v : H depth) :
    ![step ContactCollision.a ContactCollision.b v 0,
      step ContactCollision.a ContactCollision.b v (Fin.last (depth + 1))] =
      ContactCollision.R *ᵥ ![v 0, 0] := by
  rw [ContactCollision.R_apply]
  simp

/-- The zero-th visit has unit retained amplitude and no emitted coordinates. -/
def formed (depth : ℕ) : H depth :=
  generated ContactCollision.a ContactCollision.b 1 depth

theorem formed_next (depth : ℕ) :
    formed (depth + 1) = step ContactCollision.a ContactCollision.b (formed depth) := rfl

theorem formed_retained (depth : ℕ) :
    formed depth 0 = ContactCollision.a ^ depth := by
  simp [formed, generated_retained]

theorem formed_emitted (depth : ℕ) (i : Fin depth) :
    formed depth i.succ = ContactCollision.b * ContactCollision.a ^ i.val := by
  simp [formed, generated_emitted]

theorem formed_energy (depth : ℕ) : energy (formed depth) = 1 := by
  simpa only [formed, Complex.normSq_one] using
    generated_energy ContactCollision.a ContactCollision.b 1 collision_balance depth

theorem formed_retained_weight (depth : ℕ) :
    Complex.normSq (formed depth 0) = (1 / 2 : ℝ) ^ depth := by
  simp [formed, generated_retained_energy, ContactCollision.normSq_a]

theorem formed_retained_weight_div (depth : ℕ) :
    Complex.normSq (formed depth 0) = 1 / (2 : ℝ) ^ depth := by
  rw [formed_retained_weight, one_div_pow]

theorem formed_emitted_weight (depth : ℕ) (i : Fin depth) :
    Complex.normSq (formed depth i.succ) = (1 / 2 : ℝ) ^ (i.val + 1) := by
  simp [formed, generated_emitted_energy, ContactCollision.normSq_a,
    ContactCollision.normSq_b, pow_succ']

theorem formed_history_weight (depth : ℕ) :
    emittedEnergy (formed depth) = 1 - (1 / 2 : ℝ) ^ depth := by
  simpa only [formed, ContactCollision.normSq_a, Complex.normSq_one, mul_one] using
    generated_history_energy ContactCollision.a ContactCollision.b 1 collision_balance depth

theorem actual_collision_isometry {depth : ℕ} (v w : H depth) :
    energy (step ContactCollision.a ContactCollision.b v -
      step ContactCollision.a ContactCollision.b w) = energy (v - w) :=
  energy_difference_step ContactCollision.a ContactCollision.b collision_balance v w

/-- Signed residuals are read from normalized weights; no sign restriction is used. -/
theorem signed_retained_residual (r : ℝ) (depth : ℕ) :
    r * Complex.normSq (formed depth 0) = r / (2 : ℝ) ^ depth := by
  rw [formed_retained_weight_div]
  ring

theorem signed_residual_balance (r : ℝ) (depth : ℕ) :
    r * Complex.normSq (formed depth 0) + r * emittedEnergy (formed depth) = r := by
  rw [formed_retained_weight, formed_history_weight]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CollisionHistory
