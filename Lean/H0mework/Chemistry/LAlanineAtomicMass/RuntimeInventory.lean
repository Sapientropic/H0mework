import H0mework.Chemistry.LAlanineAtomicMass.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The closed sixty-face inventory: all original fifty-eight faces and two mass faces. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass.Runtime

noncomputable section

def atomicMassFaceSumEquiv : AtomicMassFace ≃ Fin 2 ⊕ Fin 58 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (BasinRefinement.BandConservationRuntime.bandConservationFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (BasinRefinement.BandConservationRuntime.bandConservationFaceEquiv.symm i)
  left_inv := by
    intro face
    rcases face with face | face
    · cases face <;> rfl
    · simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro index
    rcases index with i | i
    · fin_cases i <;> rfl
    · simp only [Equiv.apply_symm_apply]

def atomicMassFaceEquiv : AtomicMassFace ≃ Fin 60 := atomicMassFaceSumEquiv.trans finSumFinEquiv

def atomicMassFaceAt (i : Fin 60) : AtomicMassFace := atomicMassFaceEquiv.symm i
def atomicMassFaceIndex (face : AtomicMassFace) : Fin 60 := atomicMassFaceEquiv face

theorem atomicMassFace_at_index (face : AtomicMassFace) : atomicMassFaceAt (atomicMassFaceIndex face) = face :=
  atomicMassFaceEquiv.symm_apply_apply face
theorem atomicMassFace_index_at (i : Fin 60) : atomicMassFaceIndex (atomicMassFaceAt i) = i :=
  atomicMassFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.AtomicMass.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
