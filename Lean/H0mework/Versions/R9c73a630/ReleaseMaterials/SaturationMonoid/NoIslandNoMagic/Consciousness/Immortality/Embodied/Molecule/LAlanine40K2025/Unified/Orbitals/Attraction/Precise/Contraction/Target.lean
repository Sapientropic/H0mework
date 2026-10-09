import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Pair

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

theorem precise_target_row_sum :
    (∑ pair ∈ sourceUpperPairs,
        pairWeight pair * aoIntegral pair.1 pair.2) =
      ∑ address : Fin 4851, (sourceCoefficientAt address : ℝ) *
        aoIntegral (targetLeft address.val) (targetRight address.val) := by
  rw [← Finset.sum_coe_sort]
  rw [← (targetUpperEquiv.sum_comp
    (fun pair : sourceUpperPairs =>
      pairWeight pair.1 * aoIntegral pair.1.1 pair.1.2))]
  apply Finset.sum_congr rfl
  intro address _
  have eval : (targetUpperEquiv address).1 = targetPair address := rfl
  rw [eval]
  change pairWeight (targetPair address) *
      aoIntegral (targetLeft address.val) (targetRight address.val) = _
  rw [pair_weight_target]


/-- Column 6 of the same original target row is the attraction readout. -/
theorem recorded_attraction_at_target (address : Fin 4851) :
    recordedAttraction (targetLeft address.val) (targetRight address.val) =
      (((targetAORow address.val)[6]! : ℤ) : ℚ) / 10^12 := by
  rcases all_target_rows_certified address with ⟨_,_,_,_,ordered,indexed,_,_⟩
  have idx : Kinetic.kineticPairIndex (targetLeft address.val)
      (targetRight address.val) = address.val := indexed
  unfold recordedAttraction
  rw [if_pos ordered, idx]

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
