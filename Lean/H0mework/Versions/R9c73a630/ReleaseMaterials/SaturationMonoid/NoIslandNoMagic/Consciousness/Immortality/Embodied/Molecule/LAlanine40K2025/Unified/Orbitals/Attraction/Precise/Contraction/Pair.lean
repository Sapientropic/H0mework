import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Symmetry
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Ledger

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

private theorem double_sum_eq_diag_upper (g : Basis → Basis → ℝ)
    (hsym : ∀ i j : Basis, g i j = g j i) :
    (∑ i : Basis, ∑ j : Basis, g i j) =
      (∑ i : Basis, g i i) +
        (∑ i : Basis, ∑ j : Basis, if i < j then g i j + g j i else 0) := by
  have pieces (i j : Basis) : g i j =
      (if i = j then g i j else 0) + (if i < j then g i j else 0) +
        (if j < i then g i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, lt_asymm h]
    · simp [h]
    · simp [h, ne_of_gt h, lt_asymm h]
  have transpose :
      (∑ i : Basis, ∑ j : Basis, if j < i then g i j else 0) =
        ∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : j < i
    · simp [h, hsym i j]
    · simp [h]
  calc
    (∑ i : Basis, ∑ j : Basis, g i j) =
        ∑ i : Basis, ∑ j : Basis,
          ((if i = j then g i j else 0) + (if i < j then g i j else 0) +
            (if j < i then g i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact pieces i j
    _ = ((∑ i : Basis, ∑ j : Basis, if i = j then g i j else 0) +
          (∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0)) +
            (∑ i : Basis, ∑ j : Basis, if j < i then g i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i : Basis, ∑ j : Basis, if i = j then g i j else 0) +
          ((∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0) +
            (∑ i : Basis, ∑ j : Basis, if j < i then g i j else 0)) :=
        add_assoc _ _ _
    _ = (∑ i : Basis, g i i) +
          ((∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0) +
            (∑ i : Basis, ∑ j : Basis, if i < j then g i j else 0)) := by
      rw [transpose]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = (∑ i : Basis, g i i) +
          ∑ i : Basis, ∑ j : Basis, if i < j then g i j + g j i else 0 := by
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i < j
      · simp [h, hsym i j]
      · simp [h]


theorem precise_pair_expansion :
    (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * aoIntegral i j) =
      ∑ pair ∈ sourceUpperPairs,
        pairWeight pair * aoIntegral pair.1 pair.2 := by
  have sym : ∀ i j : Basis,
      (densityMatrix i j : ℝ) * aoIntegral i j =
        (densityMatrix j i : ℝ) * aoIntegral j i := by
    intro i j
    rw [ao_integral_symmetric]
    rw [show (densityMatrix i j : ℝ) = (densityMatrix j i : ℝ)
      from congrArg _ (original_D3_AO_symmetric i j)]
  have expand := double_sum_eq_diag_upper
    (fun i j => (densityMatrix i j : ℝ) * aoIntegral i j) sym
  rw [expand]
  rw [← diagonal_upper_eq_source_pairs
    (fun k l => pairWeight (k,l) * aoIntegral k l)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j
  · have pw : pairWeight (i,j) =
        (densityMatrix i j : ℝ) + (densityMatrix j i : ℝ) := by
      unfold pairWeight
      rw [if_neg (ne_of_lt h)]
      rfl
    rw [if_pos h, if_pos h, pw, ao_integral_symmetric j i]
    ring
  · rw [if_neg h, if_neg h]


end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
