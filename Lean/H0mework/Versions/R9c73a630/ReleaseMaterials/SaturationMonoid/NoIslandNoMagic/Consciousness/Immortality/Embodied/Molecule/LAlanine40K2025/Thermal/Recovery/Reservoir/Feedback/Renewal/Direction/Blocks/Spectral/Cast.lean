import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Soundness
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Cast
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n]

def complexMatrix (M : Matrix n n Int) : Matrix n n ℂ := fun i j => (M i j : ℂ)

theorem complexMatrix_mul (M N : Matrix n n Int) :
    complexMatrix (M*N) = complexMatrix M * complexMatrix N := by
  ext i j
  simp only [complexMatrix, Matrix.mul_apply, Int.cast_sum, Int.cast_mul]

omit [Fintype n] in
theorem complexMatrix_transpose (M : Matrix n n Int) :
    complexMatrix Mᵀ = (complexMatrix M)ᴴ := by
  ext i j
  simp [complexMatrix, Matrix.conjTranspose_apply]

theorem complexMatrix_gram (M R B C : Matrix n n Int)
    (first : M*R = B) (gram : Rᵀ*B = C) :
    (complexMatrix R)ᴴ * complexMatrix M * complexMatrix R = complexMatrix C := by
  rw [← complexMatrix_transpose, ← complexMatrix_mul, ← complexMatrix_mul]
  rw [Matrix.mul_assoc, first, gram]

section Positive
variable [DecidableEq n]

theorem gram_positive (M R B C : Matrix n n Int)
    (first : M*R = B) (gram : Rᵀ*B = C)
    (margins : ∀ i, 0 < 2*C i i - ∑ j, |C i j|)
    (hermitian : (complexMatrix M).IsHermitian) : (complexMatrix M).PosDef := by
  have representation := complexMatrix_gram M R B C first gram
  have symmetric : (complexMatrix C).IsHermitian := by
    rw [← representation]
    exact Matrix.isHermitian_conjTranspose_mul_mul _ hermitian
  have positive := Soundness.strict_rows_posDef _ symmetric (Soundness.integer_rows_dominant C margins)
  apply Soundness.congruence_posDef (complexMatrix M) (complexMatrix R)
  rw [representation]
  exact positive
end Positive

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral.Cast
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
