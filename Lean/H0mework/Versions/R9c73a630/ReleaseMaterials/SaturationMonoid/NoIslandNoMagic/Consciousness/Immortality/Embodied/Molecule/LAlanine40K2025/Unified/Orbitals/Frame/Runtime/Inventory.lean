import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Runtime.Facade
import Mathlib.Logic.Equiv.Fin.Basic
/-! The complete Root72 faces and the actual original orbital frame material and certificate. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Runtime

noncomputable section

def faceSumEquiv : FrameFace ≃ Fin 2 ⊕ Fin 72 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (BasinRefinement.WholeBandBasin.Flux.Runtime.faceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (BasinRefinement.WholeBandBasin.Flux.Runtime.faceEquiv.symm i)
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

def faceEquiv : FrameFace ≃ Fin 74 := faceSumEquiv.trans finSumFinEquiv

def faceAt (i : Fin 74) : FrameFace := faceEquiv.symm i
def faceIndex (face : FrameFace) : Fin 74 := faceEquiv face

theorem face_at_index (face : FrameFace) : faceAt (faceIndex face) = face :=
  faceEquiv.symm_apply_apply face
theorem face_index_at (i : Fin 74) : faceIndex (faceAt i) = i :=
  faceEquiv.apply_symm_apply i

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
