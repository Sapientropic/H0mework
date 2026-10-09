import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Address
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Coefficient
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.UpperSum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Source

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

def pairWeight (pair : Basis × Basis) : ℝ :=
  if pair.1 = pair.2 then Proxy.Correction.d3AO pair.1 pair.2
  else Proxy.Correction.d3AO pair.1 pair.2 + Proxy.Correction.d3AO pair.2 pair.1

theorem pair_weight_target (address : Fin 4851) :
    pairWeight (targetPair address) = (sourceCoefficientAt address : ℝ) := by
  unfold pairWeight targetPair sourceCoefficientAt Proxy.Correction.d3AO
  by_cases h : targetLeft address.val = targetRight address.val
  · simp [h]
  · simp [h]

theorem sourceJ_upper_pair_sum (i j : Basis) :
    UpperTriangle.sourceJUpper i j =
      ∑ pair ∈ UpperTriangle.sourceUpperPairs,
        pairWeight pair * electronRepulsion pair.1 pair.2 i j := by
  calc
    UpperTriangle.sourceJUpper i j =
      (∑ k : Basis, pairWeight (k,k) * electronRepulsion k k i j) +
        (∑ k : Basis, ∑ l : Basis,
          if k < l then pairWeight (k,l) * electronRepulsion k l i j else 0) := by
      unfold UpperTriangle.sourceJUpper
      congr 1
    _ = _ := diagonal_upper_eq_source_pairs
      (fun k l => pairWeight (k,l) * electronRepulsion k l i j)

theorem sourceJ_target_row_sum (i j : Basis) :
    UpperTriangle.sourceJUpper i j =
      ∑ address : Fin 4851,
        (sourceCoefficientAt address : ℝ) *
          electronRepulsion (targetLeft address.val) (targetRight address.val) i j := by
  rw [sourceJ_upper_pair_sum]
  rw [← Finset.sum_coe_sort]
  rw [← (targetUpperEquiv.sum_comp
    (fun pair : UpperTriangle.sourceUpperPairs =>
      pairWeight pair.1 * electronRepulsion pair.1.1 pair.1.2 i j))]
  apply Finset.sum_congr rfl
  intro address _
  change pairWeight (targetPair address) *
      electronRepulsion (targetLeft address.val) (targetRight address.val) i j = _
  rw [pair_weight_target]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
