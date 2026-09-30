import H0mework.NavierStokes.EvenLattice.Rounded

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.EvenGram

open scoped BigOperators
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore

abbrev Lattice := ℤ × ℤ × ℤ

noncomputable section

def wave (z : Lattice) : IntegerWavevector := ![2 * z.1, z.2.1, z.2.2]

def cube (a b : Nat) : Finset Lattice :=
  Finset.Icc (-(a : ℤ)) a ×ˢ (Finset.Icc (-(b : ℤ)) b ×ˢ Finset.Icc (-(b : ℤ)) b)

def diagonal (z : Lattice) (i : Fin 3) : Real :=
  (numerator z.1.natAbs z.2.1.natAbs z.2.2.natAbs i : Real) /
    (squaredRadius z.1.natAbs z.2.1.natAbs z.2.2.natAbs : Real) ^ 3

theorem wave_injective : Function.Injective wave := by
  intro a b same
  have h0 := congrFun same 0
  have h1 := congrFun same 1
  have h2 := congrFun same 2
  simp only [wave, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  exact Prod.ext (by omega) (Prod.ext h1 h2)

theorem cube_card (a b : Nat) : (cube a b).card = (2 * a + 1) * (2 * b + 1) ^ 2 := by
  simp only [cube, Finset.card_product, Int.card_Icc]
  have count (n : Nat) : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
  rw [count a, count b]
  ring

theorem cube_mono {a b c d : Nat} (ha : a ≤ c) (hb : b ≤ d) : cube a b ⊆ cube c d := by
  intro z hz
  simp only [cube, Finset.mem_product, Finset.mem_Icc] at hz ⊢
  constructor
  · constructor <;> omega
  · constructor <;> constructor <;> omega

theorem sum_symmetric_natAbs (n : Nat) (f : Nat → Real) :
    (∑ z ∈ Finset.Icc (-(n : ℤ)) n, f z.natAbs) =
      ∑ k ∈ Finset.range (n + 1), (multiplicity k : Real) * f k := by
  induction n with
  | zero => simp [multiplicity]
  | succ n ih =>
    have intervals : Finset.Icc (-((n + 1 : Nat) : ℤ)) ((n + 1 : Nat) : ℤ) =
        insert (-((n + 1 : Nat) : ℤ)) (insert ((n + 1 : Nat) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext z
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have top : ((n + 1 : Nat) : ℤ) ∉ Finset.Icc (-(n : ℤ)) n := by simp
    have bot : -((n + 1 : Nat) : ℤ) ∉ insert ((n + 1 : Nat) : ℤ) (Finset.Icc (-(n : ℤ)) n) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [intervals, Finset.sum_insert bot, Finset.sum_insert top,
      ih, Finset.sum_range_succ _ (n + 1)]
    have mult : multiplicity (n + 1) = 2 := by simp [multiplicity]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, mult, Nat.cast_ofNat]
    ring

theorem cube_diagonal_le (i : Fin 3) : (∑ z ∈ cube 8 16, diagonal z i) ≤ 178 / 25 := by
  have expanded : (∑ z ∈ cube 8 16, diagonal z i) =
      ∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 17, ∑ c ∈ Finset.range 17,
        (multiplicity a * multiplicity b * multiplicity c : Nat) *
          ((numerator a b c i : Real) / (squaredRadius a b c : Real) ^ 3) := by
    simp only [cube, Finset.sum_product, diagonal]
    rw [sum_symmetric_natAbs 8 (fun a => ∑ b ∈ Finset.Icc (-((16 : Nat) : ℤ)) ((16 : Nat) : ℤ),
      ∑ c ∈ Finset.Icc (-((16 : Nat) : ℤ)) ((16 : Nat) : ℤ),
        (numerator a b.natAbs c.natAbs i : Real) / (squaredRadius a b.natAbs c.natAbs : Real) ^ 3)]
    apply Finset.sum_congr rfl
    intro a _
    rw [sum_symmetric_natAbs 16 (fun b => ∑ c ∈ Finset.Icc (-((16 : Nat) : ℤ)) ((16 : Nat) : ℤ),
      (numerator a b c.natAbs i : Real) / (squaredRadius a b c.natAbs : Real) ^ 3)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [sum_symmetric_natAbs 16 (fun c =>
      (multiplicity a : Real) * ((multiplicity b : Real) *
        ((numerator a b c i : Real) / (squaredRadius a b c : Real) ^ 3)))]
    apply Finset.sum_congr rfl
    intro c _
    push_cast
    ring
  rw [expanded]
  exact representative_sum_le i

end
end SaturationMonoid.NavierStokes.EvenGram
