import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Source
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open scoped BigOperators Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem quadratic_error (A : Matrix n n ℝ) (error : ℝ)
    (paid : ∀ i j, |(A-1) i j| ≤ error) (v : n → ℝ) :
    |v ⬝ᵥ ((A-1) *ᵥ v)| ≤ error*(∑ i, |v i|)^2 := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, |v i * ((A-1) i j * v j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ j, error * |v i| * |v j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_mul]
      nlinarith [paid i j,abs_nonneg (v i),abs_nonneg (v j),
        mul_le_mul_of_nonneg_left (paid i j) (mul_nonneg (abs_nonneg (v i)) (abs_nonneg (v j)))]
    _ = _ := by
      simp only [Finset.mul_sum,Finset.sum_mul,pow_two]
      rw [Finset.sum_comm]
      simp only [mul_assoc]

theorem positive_of_entry_error (A : Matrix n n ℝ) (symmetric : A.IsHermitian)
    (error : ℝ) (nonnegative : 0 ≤ error) (small : error*Fintype.card n < 1)
    (paid : ∀ i j, |(A-1) i j| ≤ error) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos symmetric
  intro v nonzero
  have square : 0 < ∑ i, v i ^ 2 := by
    apply Finset.sum_pos'
    · intro i _; exact sq_nonneg _
    · obtain ⟨i,hi⟩ := Function.ne_iff.mp nonzero
      exact ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩
  have size : (∑ i, |v i|)^2 ≤ (Fintype.card n : ℝ) * (∑ i, v i^2) := by
    simpa only [Finset.card_univ,sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |v i|))
  have bounded := (quadratic_error A error paid v).trans (mul_le_mul_of_nonneg_left size nonnegative)
  have negative := (abs_le.mp bounded).1
  have split : v ⬝ᵥ ((A-1)*ᵥv) = v ⬝ᵥ (A*ᵥv)-(∑ i, v i^2) := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub]
    simp only [dotProduct,pow_two]
  rw [split] at negative
  simpa only [star_trivial] using show 0 < v ⬝ᵥ (A*ᵥv) by nlinarith

end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
