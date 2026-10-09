import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Sum

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

/-- The actual D3 coefficient times column 6 of the original target AO row. -/
def recordedAttractionTermFin (a : Fin 4851) : ℚ :=
  sourceCoefficientAt a * (((targetAORow a.val)[6]! : ℤ) : ℚ) / 10^12

def recordedAttractionChunk (b : Fin 99) : ℚ :=
  ((List.finRange 49).map fun i =>
    recordedAttractionTermFin (Kinetic.finBlockEquiv (b,i))).sum

def recordedAttractionSumQ : ℚ :=
  ((List.finRange 99).map recordedAttractionChunk).sum

private theorem fin_sum_eq_finRange {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : Fin n → α) :
    (∑ i : Fin n, f i) = ((List.finRange n).map f).sum := by
  simp only [Finset.sum]
  show ((Finset.univ.val.map f).sum : α) = _
  change (((List.finRange n : Multiset (Fin n))).map f).sum = _
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem recordedAttractionSumQ_eq :
    recordedAttractionSumQ =
      ∑ a : Fin 4851, sourceCoefficientAt a *
        recordedAttraction (targetLeft a.val) (targetRight a.val) := by
  calc
    recordedAttractionSumQ =
        ∑ b : Fin 99, ∑ i : Fin 49,
          recordedAttractionTermFin (Kinetic.finBlockEquiv (b,i)) := by
      unfold recordedAttractionSumQ
      rw [← fin_sum_eq_finRange]
      apply Finset.sum_congr rfl
      intro b _
      exact (fin_sum_eq_finRange _).symm
    _ = ∑ a : Fin 4851, recordedAttractionTermFin a := by
      calc
        _ = ∑ p : Fin 99 × Fin 49,
            recordedAttractionTermFin (Kinetic.finBlockEquiv p) :=
          (Fintype.sum_prod_type _).symm
        _ = _ := Kinetic.finBlockEquiv.sum_comp _
    _ = ∑ a : Fin 4851, sourceCoefficientAt a *
          recordedAttraction (targetLeft a.val) (targetRight a.val) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [recordedAttractionTermFin, recorded_attraction_at_target]
      ring

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
