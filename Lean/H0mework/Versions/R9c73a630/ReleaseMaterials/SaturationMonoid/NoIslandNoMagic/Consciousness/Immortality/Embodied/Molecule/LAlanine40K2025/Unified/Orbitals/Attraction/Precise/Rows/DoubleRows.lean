import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.LargeUniform
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.MixedPaid
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V051

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin

noncomputable def doubleRowsAddresses : Finset (Fin 4851) :=
  Finset.univ.filter fun a =>
    (targetLeft a.val).val = 13 ∨ (targetLeft a.val).val = 51

theorem double_rows_addresses_card : doubleRowsAddresses.card = 132 := by
  decide +kernel

theorem large_double_disjoint : Disjoint largeUniformAddresses doubleRowsAddresses := by
  apply Finset.disjoint_left.mpr
  intro a uniform double
  have selected := (Finset.mem_filter.mp uniform).2
  have exceptional := (Finset.mem_filter.mp double).2
  omega

theorem double_rows_address_error (a : Fin 4851) (paid : a ∈ doubleRowsAddresses) :
    |aoIntegral (targetLeft a.val) (targetRight a.val) -
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
        (2/10^12 : ℝ) := by
  have selected := (Finset.mem_filter.mp paid).2
  rcases all_target_rows_certified a with ⟨_,_,_,_,ordered,_,_,_⟩
  rcases selected with row13 | row51
  · have same : targetLeft a.val = (13 : Basis) := Fin.ext row13
    rw [same] at ordered ⊢
    exact upper_row_13 (targetRight a.val) ordered
  · have same : targetLeft a.val = (51 : Basis) := Fin.ext row51
    rw [same] at ordered ⊢
    exact upper_row_51 (targetRight a.val) ordered

@[irreducible] noncomputable def largePaidAddresses : Finset (Fin 4851) :=
  largeUniformAddresses ∪ doubleRowsAddresses

theorem large_paid_addresses_card : largePaidAddresses.card = 3747 := by
  rw [largePaidAddresses,Finset.card_union_of_disjoint large_double_disjoint,
    large_uniform_addresses_card,double_rows_addresses_card]

theorem old_mixed_subset_large : mixedPaidAddresses ⊆ largePaidAddresses := by
  intro a old
  rw [largePaidAddresses]
  rcases Finset.mem_insert.mp old with special | uniform
  · subst a
    apply Finset.mem_union.mpr (Or.inr ?_)
    have source : (targetLeft exceptionalAddress.val).val = 13 :=
      congrArg Fin.val exceptional_source_pair.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl source⟩
  · exact Finset.mem_union.mpr
      (Or.inl (uniform_expanded_subset_large uniform))

noncomputable def largeError (a : Fin 4851) : ℝ :=
  if (targetLeft a.val).val = 13 ∨ (targetLeft a.val).val = 51 then
    2/10^12 else 1/10^12

theorem large_paid_address_error (a : Fin 4851) (paid : a ∈ largePaidAddresses) :
    |aoIntegral (targetLeft a.val) (targetRight a.val) -
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
        largeError a := by
  rw [largePaidAddresses] at paid
  rcases Finset.mem_union.mp paid with uniform | double
  · have selected := (Finset.mem_filter.mp uniform).2
    have outside : ¬((targetLeft a.val).val = 13 ∨
        (targetLeft a.val).val = 51) := by omega
    simpa [largeError,outside] using large_uniform_address_error a uniform
  · have selected := (Finset.mem_filter.mp double).2
    simpa [largeError,selected] using double_rows_address_error a double

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
