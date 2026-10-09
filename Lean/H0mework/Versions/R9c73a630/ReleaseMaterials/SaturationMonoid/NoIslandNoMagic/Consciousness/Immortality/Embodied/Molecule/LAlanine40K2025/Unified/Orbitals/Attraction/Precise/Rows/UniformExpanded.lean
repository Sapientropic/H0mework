import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.ExpandedPaid
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V027
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V028
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V049
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V050
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V052

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin

theorem uniform_expanded_upper_error (b j : Basis)
    (selected : b.val ≤ 12 ∨ b.val = 14 ∨ (20 ≤ b.val ∧ b.val ≤ 28) ∨ (41 ≤ b.val ∧ b.val ≤ 50) ∨ b.val = 52) (ordered : b ≤ j) :
    |aoIntegral b j - (recordedAttraction b j : ℝ)| ≤ (1/10^12 : ℝ) := by
  fin_cases b
  · exact upper_row_0 j ordered
  · exact upper_row_1 j ordered
  · exact upper_row_2 j ordered
  · exact upper_row_3 j ordered
  · exact upper_row_4 j ordered
  · exact upper_row_5 j ordered
  · exact upper_row_6 j ordered
  · exact upper_row_7 j ordered
  · exact upper_row_8 j ordered
  · exact upper_row_9 j ordered
  · exact upper_row_10 j ordered
  · exact upper_row_11 j ordered
  · exact upper_row_12 j ordered
  · norm_num at selected
  · exact upper_row_14 j ordered
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · exact upper_row_20 j ordered
  · exact upper_row_21 j ordered
  · exact upper_row_22 j ordered
  · exact upper_row_23 j ordered
  · exact upper_row_24 j ordered
  · exact upper_row_25 j ordered
  · exact upper_row_26 j ordered
  · exact upper_row_27 j ordered
  · exact upper_row_28 j ordered
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · exact upper_row_41 j ordered
  · exact upper_row_42 j ordered
  · exact upper_row_43 j ordered
  · exact upper_row_44 j ordered
  · exact upper_row_45 j ordered
  · exact upper_row_46 j ordered
  · exact upper_row_47 j ordered
  · exact upper_row_48 j ordered
  · exact upper_row_49 j ordered
  · exact upper_row_50 j ordered
  · norm_num at selected
  · exact upper_row_52 j ordered
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected
  · norm_num at selected

noncomputable def uniformExpandedAddresses : Finset (Fin 4851) :=
  Finset.univ.filter fun a =>
    (targetLeft a.val).val ≤ 12 ∨
      (targetLeft a.val).val = 14 ∨
      (20 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 28) ∨
      (41 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 50) ∨
      (targetLeft a.val).val = 52

theorem uniform_expanded_addresses_card : uniformExpandedAddresses.card = 2517 := by
  decide +kernel

theorem expanded_subset_uniform : expandedPaidAddresses ⊆ uniformExpandedAddresses := by
  intro a old
  simp only [expandedPaidAddresses,uniformExpandedAddresses,Finset.mem_filter,Finset.mem_univ, true_and] at old ⊢
  rcases old with old | old | old
  · exact Or.inl old
  · exact Or.inr (Or.inr (Or.inl ⟨old.1,le_trans old.2 (by decide)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨old.1,le_trans old.2 (by decide)⟩)))

theorem uniform_expanded_address_error (a : Fin 4851) (paid : a ∈ uniformExpandedAddresses) :
    |aoIntegral (targetLeft a.val) (targetRight a.val) -
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
        (1/10^12 : ℝ) := by
  have selected : (targetLeft a.val).val ≤ 12 ∨
      (targetLeft a.val).val = 14 ∨
      (20 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 28) ∨
      (41 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 50) ∨
      (targetLeft a.val).val = 52 :=
    (Finset.mem_filter.mp paid).2
  rcases all_target_rows_certified a with ⟨_,_,_,_,ordered,_,_,_⟩
  exact uniform_expanded_upper_error _ _ selected ordered

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
