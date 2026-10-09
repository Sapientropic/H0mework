import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Recorded

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
noncomputable section

theorem ao_integral_symmetric (i j : Basis) : aoIntegral i j = aoIntegral j i := by
  unfold aoIntegral
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  congr 1
  funext x
  ring

theorem recorded_attraction_symmetric (i j : Basis) :
    recordedAttraction i j = recordedAttraction j i := by
  by_cases hij : i.val ≤ j.val
  · by_cases hji : j.val ≤ i.val
    · have same : i = j := Fin.ext (Nat.le_antisymm hij hji)
      rw [same]
    · simp only [recordedAttraction, if_pos hij, if_neg hji]
  · have hji : j.val ≤ i.val := Nat.le_of_not_ge hij
    simp only [recordedAttraction, if_neg hij, if_pos hji]

theorem precise_error_from_upper (i j : Basis) (error : ℚ)
    (upper : i ≤ j →
      |aoIntegral i j - (recordedAttraction i j : ℝ)| ≤ (error : ℝ))
    (lower : j ≤ i →
      |aoIntegral j i - (recordedAttraction j i : ℝ)| ≤ (error : ℝ)) :
    |aoIntegral i j - (recordedAttraction i j : ℝ)| ≤ (error : ℝ) := by
  rcases le_total i j with hij | hji
  · exact upper hij
  · rw [ao_integral_symmetric,recorded_attraction_symmetric]
    exact lower hji

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
