import H0mework.Chemistry.LAlanineBandInputs.Packed

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs

theorem calculated_projection {α : Type} [Inhabited α] (rows : Array CalculatedInput)
    (index : Nat) (inside : index < rows.size) (project : CalculatedInput → α)
    (original : Array α) (same : rows.map project = original) :
    project (rows[index]'inside) = original[index]! := by
  have target : index < original.size := by rw [← same, Array.size_map]; exact inside
  rw [getElem!_pos original index target]
  subst original
  exact (Array.getElem_map project (i := index) (by simpa using inside)).symm

end LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
