import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.UniformExpanded
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013Precision

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin

def exceptionalAddress : Fin 4851 := ⟨1196,by decide⟩

theorem exceptional_source_pair :
    targetLeft exceptionalAddress.val = (13 : Basis) ∧
      targetRight exceptionalAddress.val = (13 : Basis) := by
  decide +kernel

noncomputable def mixedPaidAddresses : Finset (Fin 4851) :=
  insert exceptionalAddress uniformExpandedAddresses

theorem exceptional_not_uniform : exceptionalAddress ∉ uniformExpandedAddresses := by
  decide +kernel

theorem mixed_paid_addresses_card : mixedPaidAddresses.card = 2518 := by
  simp [mixedPaidAddresses, exceptional_not_uniform,
    uniform_expanded_addresses_card]

theorem expanded_subset_mixed : expandedPaidAddresses ⊆ mixedPaidAddresses := by
  intro a old
  exact Finset.mem_insert_of_mem (expanded_subset_uniform old)

def mixedErrorQ (a : Fin 4851) : ℚ :=
  if a = exceptionalAddress then 2/10^12 else 1/10^12

theorem mixed_paid_address_error (a : Fin 4851) (paid : a ∈ mixedPaidAddresses) :
    |aoIntegral (targetLeft a.val) (targetRight a.val) -
      (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤
        (mixedErrorQ a : ℝ) := by
  by_cases special : a = exceptionalAddress
  · subst a
    simp only [mixedErrorQ, ite_true]
    rw [exceptional_source_pair.1, exceptional_source_pair.2]
    exact vcell13_13_actual_two
  · have uniform : a ∈ uniformExpandedAddresses := by
      rcases Finset.mem_insert.mp paid with exceptional | uniform
      · exact False.elim (special exceptional)
      · exact uniform
    simpa [mixedErrorQ,special] using uniform_expanded_address_error a uniform

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
