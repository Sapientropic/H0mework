import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Sum

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators

theorem diagonal_upper_eq_source_pairs (f : Fin 98 → Fin 98 → ℝ) :
    (∑ i : Fin 98, f i i) +
      (∑ i : Fin 98, ∑ j : Fin 98, if i < j then f i j else 0) =
        ∑ pair ∈ UpperTriangle.sourceUpperPairs, f pair.1 pair.2 := by
  have diagonal (i j : Fin 98) :
      (if i ≤ j then f i j else 0) =
        (if i = j then f i j else 0) + (if i < j then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, h.le]
    · simp [h]
    · simp [ne_of_gt h, not_le.mpr h, not_lt_of_gt h]
  calc
    _ = (∑ i : Fin 98, ∑ j : Fin 98,
      ((if i = j then f i j else 0) + (if i < j then f i j else 0))) := by
      simp only [Finset.sum_add_distrib]
      simp
    _ = (∑ i : Fin 98, ∑ j : Fin 98, if i ≤ j then f i j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (diagonal i j).symm
    _ = _ := by
      simp only [UpperTriangle.sourceUpperPairs,Finset.sum_filter]
      rw [← Finset.univ_product_univ, Finset.sum_product]

end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
