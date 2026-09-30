import H0mework.NavierStokes.EvenLattice.Shells

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.EvenGram

open scoped BigOperators

noncomputable section

private theorem paired_shell_payment (n : Real) (positive : 0 < n) :
    8 / (2 * n + 1) ^ 2 + (16 * (2 * n + 2) ^ 2 + 2) / (2 * n + 2) ^ 4 ≤
      6 / n - 6 / (n + 1) := by
  have first : 0 < 2 * n + 1 := by positivity
  have second : 0 < 2 * n + 2 := by positivity
  have successor : 0 < n + 1 := by positivity
  apply sub_nonneg.mp
  have identity : 6 / n - 6 / (n + 1) -
      (8 / (2 * n + 1) ^ 2 + (16 * (2 * n + 2) ^ 2 + 2) / (2 * n + 2) ^ 4) =
      (48 + 239 * n + 460 * n ^ 2 + 396 * n ^ 3 + 128 * n ^ 4) /
        (8 * n * (n + 1) ^ 4 * (2 * n + 1) ^ 2) := by
    field_simp
    ring
  rw [identity]
  positivity

theorem cube_increment_le (n : Nat) (positive : 0 < n) (i : Fin 3) :
    (∑ z ∈ cube (n + 1) (2 * (n + 1)), diagonal z i) -
      (∑ z ∈ cube n (2 * n), diagonal z i) ≤ 6 / (n : Real) - 6 / ((n : Real) + 1) := by
  have first := odd_shell_bound n i
  have second := even_shell_bound n i
  have firstEq := Finset.sum_sdiff (f := fun z => diagonal z i)
    (cube_mono (a := n) (b := 2 * n) le_rfl (by omega : 2 * n ≤ 2 * n + 1))
  have secondEq := Finset.sum_sdiff (f := fun z => diagonal z i)
    (cube_mono (a := n) (b := 2 * n + 1) (by omega : n ≤ n + 1)
      (by omega : 2 * n + 1 ≤ 2 * (n + 1)))
  have scalar := paired_shell_payment (n : Real) (by exact_mod_cast positive)
  linarith

theorem cube_sum_le (n : Nat) (large : 8 ≤ n) (i : Fin 3) :
    (∑ z ∈ cube n (2 * n), diagonal z i) ≤ 787 / 100 - 6 / (n : Real) := by
  induction n, large using Nat.le_induction with
  | base =>
    convert cube_diagonal_le i using 1
    norm_num
  | succ n large ih =>
    have step := cube_increment_le n (by omega) i
    push_cast
    linarith

theorem exists_cube (s : Finset Lattice) : ∃ n : Nat, 8 ≤ n ∧ s ⊆ cube n (2 * n) := by
  let radius := s.sup fun z => max z.1.natAbs (max z.2.1.natAbs z.2.2.natAbs)
  refine ⟨8 + radius, by omega, ?_⟩
  intro z hz
  have bound : max z.1.natAbs (max z.2.1.natAbs z.2.2.natAbs) ≤ radius :=
    Finset.le_sup (f := fun z : Lattice => max z.1.natAbs (max z.2.1.natAbs z.2.2.natAbs)) hz
  rw [mem_cube]
  constructor
  · omega
  · constructor <;> omega

theorem finite_diagonal_le (s : Finset Lattice) (i : Fin 3) :
    (∑ z ∈ s, diagonal z i) ≤ 787 / 100 := by
  obtain ⟨n, large, included⟩ := exists_cube s
  have major := Finset.sum_le_sum_of_subset_of_nonneg included (fun z _ _ => diagonal_nonneg z i)
  have bound := cube_sum_le n large i
  have nonneg : (0 : Real) ≤ 6 / (n : Real) := by positivity
  linarith

theorem diagonal_summable (i : Fin 3) : Summable fun z => diagonal z i :=
  summable_of_sum_le (fun z => diagonal_nonneg z i) (fun s => finite_diagonal_le s i)

theorem diagonal_tsum_le (i : Fin 3) : (∑' z : Lattice, diagonal z i) ≤ 787 / 100 :=
  Real.tsum_le_of_sum_le (fun z => diagonal_nonneg z i) (fun s => finite_diagonal_le s i)

end
end SaturationMonoid.NavierStokes.EvenGram
