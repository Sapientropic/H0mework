import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.DominantMass.Sectors

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation
open Propagation.Interface
namespace NetContraction.Fixed


/-! The 36 canonical a < b addresses enumerate the original mid-sector in both orientations. -/

def midAnchor (a : Fin 2) : Basis := ⟨a.val, by omega⟩
def midPartner (b : Fin 18) : Basis := ⟨6+b.val, by omega⟩

theorem mid_address_ordered (a : Fin 2) (b : Fin 18) : midAnchor a < midPartner b := by
  change a.val < 6+b.val
  omega

theorem mid_ordered_sector (a b : Basis) (ordered : a < b) :
    midCond a b ↔ a.val < 2 ∧ 6 ≤ b.val ∧ b.val < 24 := by
  change a.val < b.val at ordered
  unfold midCond
  omega

theorem mid_ordered_covered (a b : Basis) (ordered : a < b) (sector : midCond a b) :
    ∃ (i : Fin 2) (j : Fin 18), a = midAnchor i ∧ b = midPartner j := by
  have bounds := (mid_ordered_sector a b ordered).mp sector
  refine ⟨⟨a.val,bounds.1⟩,⟨b.val-6,by omega⟩,?_,?_⟩
  · rfl
  · apply Fin.ext
    change b.val = 6+(b.val-6)
    omega

theorem mid_address_sector (a : Fin 2) (b : Fin 18) : midCond (midAnchor a) (midPartner b) := by
  apply (mid_ordered_sector _ _ (mid_address_ordered a b)).mpr
  change a.val < 2 ∧ 6 ≤ 6+b.val ∧ 6+b.val < 24
  omega

theorem mid_partner_energy_box (b : Basis) (lo : 6 ≤ b.val) (hi : b.val < 24) :
    (-(1 : ℚ) < Diagonal.energy b) ∧ (Diagonal.energy b < 0) := by
  interval_cases h : b.val <;> norm_num [Diagonal.energy, energies, h]

theorem mid_anchor_energy_box (a : Basis) (hi : a.val < 2) :
    (-(19 : ℚ) < Diagonal.energy a) ∧ (Diagonal.energy a < -18) := by
  interval_cases h : a.val <;> norm_num [Diagonal.energy, energies, h]

end NetContraction.Fixed
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
