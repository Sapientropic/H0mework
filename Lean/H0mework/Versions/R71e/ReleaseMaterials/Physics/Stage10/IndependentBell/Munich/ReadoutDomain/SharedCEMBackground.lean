import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The same two local OR backgrounds generate every reported joint probability. -/

set_option autoImplicit false

namespace BellSharedCEMBackground

noncomputable section

structure BirthSource where
  r00 : ℝ
  r01 : ℝ
  r10 : ℝ
  r11 : ℝ
  nonneg00 : 0 ≤ r00
  nonneg01 : 0 ≤ r01
  nonneg10 : 0 ≤ r10
  nonneg11 : 0 ≤ r11
  total : r00 + r01 + r10 + r11 = 1

def q00 (s : BirthSource) (a b : ℝ) : ℝ := (1-a)*(1-b)*s.r00
def q01 (s : BirthSource) (a b : ℝ) : ℝ := (1-a)*(s.r01+b*s.r00)
def q10 (s : BirthSource) (a b : ℝ) : ℝ := (1-b)*(s.r10+a*s.r00)
def q11 (s : BirthSource) (a b : ℝ) : ℝ := s.r11+a*s.r01+b*s.r10+a*b*s.r00

theorem reported_total (s : BirthSource) (a b : ℝ) :
    q00 s a b + q01 s a b + q10 s a b + q11 s a b = 1 := by
  unfold q00 q01 q10 q11
  linear_combination s.total

theorem first_birth_residual (s : BirthSource) (a b : ℝ) :
    q10 s a b + q11 s a b - a = (1-a)*(s.r10+s.r11) := by
  unfold q10 q11
  linear_combination a * s.total

theorem second_birth_residual (s : BirthSource) (a b : ℝ) :
    q01 s a b + q11 s a b - b = (1-b)*(s.r01+s.r11) := by
  unfold q01 q11
  linear_combination b * s.total

theorem joint_birth_residual (s : BirthSource) (a b : ℝ) :
    q11 s a b - b*(q10 s a b+q11 s a b) -
        a*(q01 s a b+q11 s a b) + a*b = (1-a)*(1-b)*s.r11 := by
  unfold q01 q10 q11
  linear_combination -a*b*s.total

theorem first_residual_nonnegative (s : BirthSource) (a b : ℝ) (ha : a ≤ 1) :
    0 ≤ q10 s a b+q11 s a b-a := by
  rw [first_birth_residual]
  exact mul_nonneg (sub_nonneg.mpr ha) (add_nonneg s.nonneg10 s.nonneg11)

theorem second_residual_nonnegative (s : BirthSource) (a b : ℝ) (hb : b ≤ 1) :
    0 ≤ q01 s a b+q11 s a b-b := by
  rw [second_birth_residual]
  exact mul_nonneg (sub_nonneg.mpr hb) (add_nonneg s.nonneg01 s.nonneg11)

theorem joint_residual_nonnegative (s : BirthSource) (a b : ℝ) (ha : a ≤ 1) (hb : b ≤ 1) :
    0 ≤ q11 s a b-b*(q10 s a b+q11 s a b)-a*(q01 s a b+q11 s a b)+a*b := by
  rw [joint_birth_residual]
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)) s.nonneg11

def jointFactor (x y a b t : ℝ) : ℝ := 1-t*(x-a)*(y-b)

def localFactor (x a t : ℝ) : ℝ := 1-t*(x-a)

theorem reported_nonnegative (s : BirthSource) (a b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ q00 s a b ∧ 0 ≤ q01 s a b ∧ 0 ≤ q10 s a b ∧ 0 ≤ q11 s a b := by
  unfold q00 q01 q10 q11
  have ha : 0 ≤ 1-a := sub_nonneg.mpr ha1
  have hb : 0 ≤ 1-b := sub_nonneg.mpr hb1
  exact ⟨mul_nonneg (mul_nonneg ha hb) s.nonneg00,
    mul_nonneg ha (add_nonneg s.nonneg01 (mul_nonneg hb0 s.nonneg00)),
    mul_nonneg hb (add_nonneg s.nonneg10 (mul_nonneg ha0 s.nonneg00)),
    add_nonneg (add_nonneg (add_nonneg s.nonneg11 (mul_nonneg ha0 s.nonneg01))
      (mul_nonneg hb0 s.nonneg10)) (mul_nonneg (mul_nonneg ha0 hb0) s.nonneg00)⟩

theorem local_factor_nonnegative (x a t : ℝ) (hx : x ≤ 1) (ha : 0 ≤ a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ localFactor x a t := by
  have h := mul_le_mul_of_nonneg_left (show x-a ≤ 1 by linarith) ht0
  unfold localFactor
  nlinarith

theorem joint_factor_nonnegative (x y a b t : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ jointFactor x y a b t := by
  have hu0 : -1 ≤ x-a := by linarith
  have hu1 : x-a ≤ 1 := by linarith
  have hv0 : -1 ≤ y-b := by linarith
  have hv1 : y-b ≤ 1 := by linarith
  have hp : (x-a)*(y-b) ≤ 1 := by
    by_cases hu : 0 ≤ x-a
    · have h := mul_le_mul_of_nonneg_left hv1 hu
      nlinarith
    · have h := mul_le_mul_of_nonpos_left hv0 (le_of_not_ge hu)
      nlinarith
  have h := mul_le_mul_of_nonneg_left hp ht0
  unfold jointFactor
  nlinarith

theorem source_first_factor_mean (s : BirthSource) (a b t : ℝ) :
    q00 s a b * localFactor 0 a t + q01 s a b * localFactor 0 a t +
      q10 s a b * localFactor 1 a t + q11 s a b * localFactor 1 a t =
        1-t*(1-a)*(s.r10+s.r11) := by
  unfold q00 q01 q10 q11 localFactor
  linear_combination s.total

theorem source_second_factor_mean (s : BirthSource) (a b t : ℝ) :
    q00 s a b * localFactor 0 b t + q01 s a b * localFactor 1 b t +
      q10 s a b * localFactor 0 b t + q11 s a b * localFactor 1 b t =
        1-t*(1-b)*(s.r01+s.r11) := by
  unfold q00 q01 q10 q11 localFactor
  linear_combination s.total

theorem source_first_factor_supermean (s : BirthSource) (a b t : ℝ)
    (ha : a ≤ 1) (ht : 0 ≤ t) :
    q00 s a b * localFactor 0 a t + q01 s a b * localFactor 0 a t +
      q10 s a b * localFactor 1 a t + q11 s a b * localFactor 1 a t ≤ 1 := by
  rw [source_first_factor_mean]
  have h := mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ha)) (add_nonneg s.nonneg10 s.nonneg11)
  linarith

theorem source_second_factor_supermean (s : BirthSource) (a b t : ℝ)
    (hb : b ≤ 1) (ht : 0 ≤ t) :
    q00 s a b * localFactor 0 b t + q01 s a b * localFactor 1 b t +
      q10 s a b * localFactor 0 b t + q11 s a b * localFactor 1 b t ≤ 1 := by
  rw [source_second_factor_mean]
  have h := mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hb)) (add_nonneg s.nonneg01 s.nonneg11)
  linarith

theorem source_joint_factor_mean (s : BirthSource) (a b t : ℝ) :
    q00 s a b * jointFactor 0 0 a b t + q01 s a b * jointFactor 0 1 a b t +
      q10 s a b * jointFactor 1 0 a b t + q11 s a b * jointFactor 1 1 a b t =
        1-t*(1-a)*(1-b)*s.r11 := by
  unfold q00 q01 q10 q11 jointFactor
  linear_combination s.total

theorem source_joint_factor_supermean (s : BirthSource) (a b t : ℝ)
    (ha : a ≤ 1) (hb : b ≤ 1) (ht : 0 ≤ t) :
    q00 s a b * jointFactor 0 0 a b t + q01 s a b * jointFactor 0 1 a b t +
      q10 s a b * jointFactor 1 0 a b t + q11 s a b * jointFactor 1 1 a b t ≤ 1 := by
  rw [source_joint_factor_mean]
  have h := mul_nonneg (mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ha))
    (sub_nonneg.mpr hb)) s.nonneg11
  linarith

theorem rectangular_bernstein (x y a₀ a₁ b₀ b₁ s u t : ℝ) :
    jointFactor x y ((1-s)*a₀+s*a₁) ((1-u)*b₀+u*b₁) t =
      (1-s)*(1-u)*jointFactor x y a₀ b₀ t + (1-s)*u*jointFactor x y a₀ b₁ t +
      s*(1-u)*jointFactor x y a₁ b₀ t + s*u*jointFactor x y a₁ b₁ t := by
  unfold jointFactor
  ring

theorem rectangular_factor_lower (x y a₀ a₁ b₀ b₁ s u t m : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h00 : m ≤ jointFactor x y a₀ b₀ t) (h01 : m ≤ jointFactor x y a₀ b₁ t)
    (h10 : m ≤ jointFactor x y a₁ b₀ t) (h11 : m ≤ jointFactor x y a₁ b₁ t) :
    m ≤ jointFactor x y ((1-s)*a₀+s*a₁) ((1-u)*b₀+u*b₁) t := by
  rw [rectangular_bernstein]
  have h0 := mul_le_mul_of_nonneg_left h00 (mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hu1))
  have h1 := mul_le_mul_of_nonneg_left h01 (mul_nonneg (sub_nonneg.mpr hs1) hu0)
  have h2 := mul_le_mul_of_nonneg_left h10 (mul_nonneg hs0 (sub_nonneg.mpr hu1))
  have h3 := mul_le_mul_of_nonneg_left h11 (mul_nonneg hs0 hu0)
  nlinarith

end
end BellSharedCEMBackground
