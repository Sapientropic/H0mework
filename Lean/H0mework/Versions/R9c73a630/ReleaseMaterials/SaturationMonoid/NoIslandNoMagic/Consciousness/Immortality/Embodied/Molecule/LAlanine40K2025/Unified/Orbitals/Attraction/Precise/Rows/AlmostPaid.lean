import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.DoubleRows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V035
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V036
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V037
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V038
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V039
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V040
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V060
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V061
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V062
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V063
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V064
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V065
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V066
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V067
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V068
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V069
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V070

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin

theorem almost_uniform_upper_error (b j : Basis)
    (selected : b.val ≤ 70 ∧ b.val ≠ 13 ∧ b.val ≠ 51) (ordered : b ≤ j) :
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
  · exact upper_row_35 j ordered
  · exact upper_row_36 j ordered
  · exact upper_row_37 j ordered
  · exact upper_row_38 j ordered
  · exact upper_row_39 j ordered
  · exact upper_row_40 j ordered
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
  · exact upper_row_60 j ordered
  · exact upper_row_61 j ordered
  · exact upper_row_62 j ordered
  · exact upper_row_63 j ordered
  · exact upper_row_64 j ordered
  · exact upper_row_65 j ordered
  · exact upper_row_66 j ordered
  · exact upper_row_67 j ordered
  · exact upper_row_68 j ordered
  · exact upper_row_69 j ordered
  · exact upper_row_70 j ordered
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

@[irreducible] noncomputable def almostUniformAddresses : Finset (Fin 4851) :=
  Finset.univ.filter fun a =>
    (targetLeft a.val).val ≤ 70 ∧
      (targetLeft a.val).val ≠ 13 ∧ (targetLeft a.val).val ≠ 51

theorem almost_uniform_addresses_card : almostUniformAddresses.card = 4341 := by
  rw [almostUniformAddresses]
  decide +kernel

theorem almost_uniform_address_error (a : Fin 4851)
    (paid : a ∈ almostUniformAddresses) :
    |aoIntegral (targetLeft a.val) (targetRight a.val) -
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
        (1/10^12 : ℝ) := by
  rw [almostUniformAddresses] at paid
  have selected := (Finset.mem_filter.mp paid).2
  rcases all_target_rows_certified a with ⟨_,_,_,_,ordered,_,_,_⟩
  exact almost_uniform_upper_error _ _ selected ordered

theorem almost_double_disjoint : Disjoint almostUniformAddresses doubleRowsAddresses := by
  apply Finset.disjoint_left.mpr
  intro a uniform double
  rw [almostUniformAddresses] at uniform
  have selected := (Finset.mem_filter.mp uniform).2
  have exceptional := (Finset.mem_filter.mp double).2
  omega

@[irreducible] noncomputable def almostPaidAddresses : Finset (Fin 4851) :=
  almostUniformAddresses ∪ doubleRowsAddresses

theorem almost_paid_addresses_card : almostPaidAddresses.card = 4473 := by
  rw [almostPaidAddresses,Finset.card_union_of_disjoint almost_double_disjoint,
    almost_uniform_addresses_card,double_rows_addresses_card]

theorem large_subset_almost : largePaidAddresses ⊆ almostPaidAddresses := by
  intro a old
  rw [largePaidAddresses] at old
  rw [almostPaidAddresses]
  rcases Finset.mem_union.mp old with uniform | double
  · apply Finset.mem_union.mpr (Or.inl ?_)
    rw [almostUniformAddresses]
    have selected := (Finset.mem_filter.mp uniform).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  · exact Finset.mem_union.mpr (Or.inr double)

theorem almost_paid_address_error (a : Fin 4851) (paid : a ∈ almostPaidAddresses) :
    |aoIntegral (targetLeft a.val) (targetRight a.val) -
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
        largeError a := by
  rw [almostPaidAddresses] at paid
  rcases Finset.mem_union.mp paid with uniform | double
  · have paidUniform : a ∈ almostUniformAddresses := uniform
    rw [almostUniformAddresses] at uniform
    have selected := (Finset.mem_filter.mp uniform).2
    have outside : ¬((targetLeft a.val).val = 13 ∨
        (targetLeft a.val).val = 51) := by omega
    simpa [largeError,outside] using almost_uniform_address_error a paidUniform
  · have selected := (Finset.mem_filter.mp double).2
    simpa [largeError,selected] using double_rows_address_error a double

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
