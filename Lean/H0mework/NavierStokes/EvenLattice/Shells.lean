import H0mework.NavierStokes.EvenLattice.Lattice

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.EvenGram

open scoped BigOperators

noncomputable section

theorem mem_cube (z : Lattice) (a b : Nat) : z ∈ cube a b ↔
    z.1.natAbs ≤ a ∧ z.2.1.natAbs ≤ b ∧ z.2.2.natAbs ≤ b := by
  simp only [cube, Finset.mem_product, Finset.mem_Icc]
  omega

theorem diagonal_nonneg (z : Lattice) (i : Fin 3) : 0 ≤ diagonal z i := by
  unfold diagonal
  positivity

theorem numerator_le (a b c : Nat) (i : Fin 3) : numerator a b c i ≤ squaredRadius a b c := by
  fin_cases i <;> simp [numerator, squaredRadius]

theorem diagonal_le_inverse (z : Lattice) (i : Fin 3) :
    diagonal z i ≤ ((squaredRadius z.1.natAbs z.2.1.natAbs z.2.2.natAbs : Real)⁻¹) ^ 2 := by
  let d := squaredRadius z.1.natAbs z.2.1.natAbs z.2.2.natAbs
  change _ / (d : Real) ^ 3 ≤ ((d : Real)⁻¹) ^ 2
  have num : (numerator z.1.natAbs z.2.1.natAbs z.2.2.natAbs i : Real) ≤ d := by
    exact_mod_cast numerator_le z.1.natAbs z.2.1.natAbs z.2.2.natAbs i
  by_cases zero : d = 0
  · simp [zero]
  have pos : 0 < (d : Real) := by exact_mod_cast Nat.pos_of_ne_zero zero
  change _ / (d : Real) ^ 3 ≤ _
  calc
    _ ≤ (d : Real) / (d : Real) ^ 3 := div_le_div_of_nonneg_right num (by positivity)
    _ = ((d : Real)⁻¹) ^ 2 := by field_simp

theorem shell_sum_le (s : Finset Lattice) (r : Nat) (positive : 0 < r)
    (lower : ∀ z ∈ s, r ^ 2 ≤ squaredRadius z.1.natAbs z.2.1.natAbs z.2.2.natAbs)
    (i : Fin 3) : (∑ z ∈ s, diagonal z i) ≤ (s.card : Real) / (r : Real) ^ 4 := by
  have each (z : Lattice) (hz : z ∈ s) : diagonal z i ≤ ((r : Real) ^ 2)⁻¹ ^ 2 := by
    apply (diagonal_le_inverse z i).trans
    apply (sq_le_sq₀ (by positivity) (by positivity)).2
    exact inv_anti₀ (by positivity) (by exact_mod_cast lower z hz)
  calc
    _ ≤ ∑ _z ∈ s, ((r : Real) ^ 2)⁻¹ ^ 2 := Finset.sum_le_sum each
    _ = (s.card : Real) / (r : Real) ^ 4 := by
      simp only [Finset.sum_const, nsmul_eq_mul, ← inv_pow, ← pow_mul, div_eq_mul_inv]

theorem odd_shell_bound (n : Nat) (i : Fin 3) :
    (∑ z ∈ cube n (2 * n + 1) \ cube n (2 * n), diagonal z i) ≤ 8 / (2 * (n : Real) + 1) ^ 2 := by
  have count : (cube n (2 * n + 1) \ cube n (2 * n)).card = 8 * (2 * n + 1) ^ 2 := by
    rw [Finset.card_sdiff_of_subset (cube_mono le_rfl (by omega)), cube_card, cube_card]
    have polynomial : (2 * n + 1) * (2 * (2 * n + 1) + 1) ^ 2 =
        8 * (2 * n + 1) ^ 2 + (2 * n + 1) * (2 * (2 * n) + 1) ^ 2 := by ring
    rw [polynomial, Nat.add_sub_cancel]
  have lower (z : Lattice) (hz : z ∈ cube n (2 * n + 1) \ cube n (2 * n)) :
      (2 * n + 1) ^ 2 ≤ squaredRadius z.1.natAbs z.2.1.natAbs z.2.2.natAbs := by
    have hi := (mem_cube z n (2 * n + 1)).mp (Finset.mem_sdiff.mp hz).1
    have lo := (Finset.mem_sdiff.mp hz).2
    rw [mem_cube] at lo
    have large : 2 * n + 1 ≤ z.2.1.natAbs ∨ 2 * n + 1 ≤ z.2.2.natAbs := by omega
    rcases large with large | large <;>
      have square := Nat.pow_le_pow_left large 2 <;> dsimp [squaredRadius] <;> omega
  have bound := shell_sum_le _ (2 * n + 1) (by omega) lower i
  rw [count] at bound
  push_cast at bound
  have positive : (0 : Real) < 2 * n + 1 := by positivity
  convert bound using 1
  field_simp

theorem even_shell_bound (n : Nat) (i : Fin 3) :
    (∑ z ∈ cube (n + 1) (2 * (n + 1)) \ cube n (2 * n + 1), diagonal z i) ≤
      (16 * (2 * (n : Real) + 2) ^ 2 + 2) / (2 * (n : Real) + 2) ^ 4 := by
  have count : (cube (n + 1) (2 * (n + 1)) \ cube n (2 * n + 1)).card =
      16 * (2 * n + 2) ^ 2 + 2 := by
    rw [Finset.card_sdiff_of_subset (cube_mono (by omega) (by omega)), cube_card, cube_card]
    have polynomial : (2 * (n + 1) + 1) * (2 * (2 * (n + 1)) + 1) ^ 2 =
        (16 * (2 * n + 2) ^ 2 + 2) + (2 * n + 1) * (2 * (2 * n + 1) + 1) ^ 2 := by ring
    rw [polynomial, Nat.add_sub_cancel]
  have lower (z : Lattice) (hz : z ∈ cube (n + 1) (2 * (n + 1)) \ cube n (2 * n + 1)) :
      (2 * n + 2) ^ 2 ≤ squaredRadius z.1.natAbs z.2.1.natAbs z.2.2.natAbs := by
    have lo := (Finset.mem_sdiff.mp hz).2
    rw [mem_cube] at lo
    have large : n + 1 ≤ z.1.natAbs ∨ 2 * n + 2 ≤ z.2.1.natAbs ∨ 2 * n + 2 ≤ z.2.2.natAbs := by omega
    rcases large with large | large | large
    · have square := Nat.pow_le_pow_left large 2
      dsimp [squaredRadius]
      nlinarith
    · have square := Nat.pow_le_pow_left large 2
      dsimp [squaredRadius]
      omega
    · have square := Nat.pow_le_pow_left large 2
      dsimp [squaredRadius]
      omega
  have bound := shell_sum_le _ (2 * n + 2) (by omega) lower i
  rw [count] at bound
  exact_mod_cast bound

end
end SaturationMonoid.NavierStokes.EvenGram
