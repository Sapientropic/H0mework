import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Sectors.Support

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
open Propagation.Interface Load.Source Collision
open scoped Matrix ComplexOrder BigOperators
noncomputable section

local instance : Fintype (Sym2 (Sym2 Basis)) := Fintype.ofFinite _
local instance : Fintype PointerIndex := Fintype.ofFinite _

attribute [local irreducible] nineAction elevenAction inputFour Weak.origin Weak.execution

private theorem sum_active (f : Sym2 (Sym2 Basis) → ℝ)
    (zero : ∀ k, k ∉ Set.range activeSector → f k = 0) :
    ∑ k, f k = ∑ k : Sym2 Basis, f (activeSector k) := by
  calc
    _ = ∑ k ∈ Finset.univ.image activeSector, f k := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ outside
      apply zero k
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using outside
    _ = _ := Finset.sum_image (fun _ _ _ _ same => activeSector_injective same)

theorem source_sector_energy (O rho : PointerJoint) (observable : Preserves pointerOrbit O)
    (support : ∀ i j, pointerOrbit i ∉ Set.range activeSector → rho i j = 0) :
    energy O rho = ∑ k : Sym2 Basis,
      energy (restrict pointerOrbit (activeSector k) O) (restrict pointerOrbit (activeSector k) rho) := by
  rw [energy_eq_sum_restrict observable]
  apply sum_active
  intro k outside
  have zero : restrict pointerOrbit k rho = 0 := by
    ext i j
    exact support i.val j.val (by simpa only [i.property] using outside)
  rw [zero]
  simp [energy]

theorem actual_nine_energy (O : PointerJoint) (observable : Preserves pointerOrbit O) :
    energy O Weak.origin.joint = ∑ k : Sym2 Basis,
      energy (restrict pointerOrbit (activeSector k) O)
        (restrict pointerOrbit (activeSector k) Weak.origin.joint) :=
  source_sector_energy O Weak.origin.joint observable actual_nine_support

theorem actual_eleven_energy (O : PointerJoint) (observable : Preserves pointerOrbit O) :
    energy O Weak.execution.joint = ∑ k : Sym2 Basis,
      energy (restrict pointerOrbit (activeSector k) O)
        (restrict pointerOrbit (activeSector k) Weak.execution.joint) :=
  source_sector_energy O Weak.execution.joint observable actual_eleven_support

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
