import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Gram
open Propagation.Interface
open scoped BigOperators

theorem real_swap (a b : OccupiedSlot) : gramRealError a b = gramRealError b a := by
  have sums : (∑ i : Basis,
      (realNumerator i a * realNumerator i b + imagNumerator i a * imagNumerator i b)) =
      ∑ i : Basis,
        (realNumerator i b * realNumerator i a + imagNumerator i b * imagNumerator i a) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold gramRealError
  rw [sums]
  simp [eq_comm]

theorem imag_swap (a b : OccupiedSlot) : gramImagError a b = -gramImagError b a := by
  have sums : (∑ i : Basis,
      (realNumerator i a * imagNumerator i b - imagNumerator i a * realNumerator i b)) =
      -(∑ i : Basis,
        (realNumerator i b * imagNumerator i a - imagNumerator i b * realNumerator i a)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold gramImagError
  rw [sums]

end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Gram
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
