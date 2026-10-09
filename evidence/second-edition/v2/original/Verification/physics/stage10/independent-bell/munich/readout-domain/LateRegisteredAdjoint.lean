import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

set_option autoImplicit false

namespace BellLateRegisteredAdjoint

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem recycle_zero (p o j : Matrix n n ℂ)
    (hp : p.conjTranspose = p) (hj : p * j = j) (ho : p * o * p = 0) :
    j.conjTranspose * o * j = 0 := by
  have hs : j.conjTranspose * p = j.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul, hp] using congrArg Matrix.conjTranspose hj
  calc
    j.conjTranspose * o * j = (j.conjTranspose * p) * o * (p * j) := by rw [hs, hj]
    _ = j.conjTranspose * (p * o * p) * j := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [ho]; simp

theorem compression_preserved (p o g : Matrix n n ℂ)
    (hl : p * g.conjTranspose = g.conjTranspose * p) (hr : g * p = p * g)
    (ho : p * o * p = 0) : p * (g.conjTranspose * o * g) * p = 0 := by
  calc
    p * (g.conjTranspose * o * g) * p = (p * g.conjTranspose) * o * (g * p) := by
      simp only [Matrix.mul_assoc]
    _ = (g.conjTranspose * p) * o * (p * g) := by rw [hl, hr]
    _ = g.conjTranspose * (p * o * p) * g := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [ho]; simp

theorem pair_price (a b : ℝ) : (1+a)*(1+b)-1 = a+b+a*b := by ring

theorem finite_moment_price {ι : Type*} [Fintype ι] (c m q : ι → ℝ) (e : ℝ)
    (_he : 0 ≤ e) (hm : ∀ i, |m i-q i| ≤ e) :
    |∑ i, c i * (m i-q i)| ≤ e * ∑ i, |c i| := by
  calc
    |∑ i, c i * (m i-q i)| ≤ ∑ i, |c i * (m i-q i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |m i-q i| := by simp only [abs_mul]
    _ ≤ ∑ i, |c i| * e := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hm i) (abs_nonneg _)
    _ = e * ∑ i, |c i| := by rw [← Finset.sum_mul, mul_comm]

end BellLateRegisteredAdjoint
