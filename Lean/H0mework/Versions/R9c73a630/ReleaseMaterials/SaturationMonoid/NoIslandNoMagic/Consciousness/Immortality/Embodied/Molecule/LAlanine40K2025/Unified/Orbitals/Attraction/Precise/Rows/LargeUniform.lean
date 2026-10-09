import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.UniformExpanded
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V016
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V017
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V018
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V019
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V029
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V030
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V031
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V032
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V033
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V034
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V053
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V054
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V055
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V056
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V057
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V058
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V059

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin

theorem large_uniform_upper_error (b j : Basis)
    (selected : b.val ≤ 12 ∨ (14 ≤ b.val ∧ b.val ≤ 19) ∨ (20 ≤ b.val ∧ b.val ≤ 34) ∨ (41 ≤ b.val ∧ b.val ≤ 50) ∨ (52 ≤ b.val ∧ b.val ≤ 59)) (ordered : b ≤ j) :
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
  · exact upper_row_15 j ordered
  · exact upper_row_16 j ordered
  · exact upper_row_17 j ordered
  · exact upper_row_18 j ordered
  · exact upper_row_19 j ordered
  · exact upper_row_20 j ordered
  · exact upper_row_21 j ordered
  · exact upper_row_22 j ordered
  · exact upper_row_23 j ordered
  · exact upper_row_24 j ordered
  · exact upper_row_25 j ordered
  · exact upper_row_26 j ordered
  · exact upper_row_27 j ordered
  · exact upper_row_28 j ordered
  · exact upper_row_29 j ordered
  · exact upper_row_30 j ordered
  · exact upper_row_31 j ordered
  · exact upper_row_32 j ordered
  · exact upper_row_33 j ordered
  · exact upper_row_34 j ordered
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
  · exact upper_row_53 j ordered
  · exact upper_row_54 j ordered
  · exact upper_row_55 j ordered
  · exact upper_row_56 j ordered
  · exact upper_row_57 j ordered
  · exact upper_row_58 j ordered
  · exact upper_row_59 j ordered
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

noncomputable def largeUniformAddresses : Finset (Fin 4851) :=
  Finset.univ.filter fun a =>
    (targetLeft a.val).val ≤ 12 ∨
      (14 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 19) ∨
      (20 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 34) ∨
      (41 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 50) ∨
      (52 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 59)

theorem large_uniform_addresses_card : largeUniformAddresses.card = 3615 := by
  decide +kernel

theorem uniform_expanded_subset_large : uniformExpandedAddresses ⊆ largeUniformAddresses := by
  intro a old
  simp only [uniformExpandedAddresses,largeUniformAddresses,Finset.mem_filter,Finset.mem_univ, true_and] at old ⊢
  omega

theorem large_uniform_address_error (a : Fin 4851) (paid : a ∈ largeUniformAddresses) :
    |aoIntegral (targetLeft a.val) (targetRight a.val) -
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
        (1/10^12 : ℝ) := by
  have selected : (targetLeft a.val).val ≤ 12 ∨
      (14 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 19) ∨
      (20 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 34) ∨
      (41 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 50) ∨
      (52 ≤ (targetLeft a.val).val ∧ (targetLeft a.val).val ≤ 59) :=
    (Finset.mem_filter.mp paid).2
  rcases all_target_rows_certified a with ⟨_,_,_,_,ordered,_,_,_⟩
  exact large_uniform_upper_error _ _ selected ordered

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
