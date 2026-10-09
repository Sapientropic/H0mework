import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Flux.Runtime.Facade
import Mathlib.Logic.Equiv.Fin.Basic
/-! The complete Root70 faces and the actual zero-flux material and certificate. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Flux.Runtime

noncomputable section

def faceSumEquiv : FluxFace ≃ Fin 2 ⊕ Fin 70 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandBasin.Runtime.faceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandBasin.Runtime.faceEquiv.symm i)
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

def faceEquiv : FluxFace ≃ Fin 72 := faceSumEquiv.trans finSumFinEquiv

def faceAt (i : Fin 72) : FluxFace := faceEquiv.symm i
def faceIndex (face : FluxFace) : Fin 72 := faceEquiv face

theorem face_at_index (face : FluxFace) : faceAt (faceIndex face) = face :=
  faceEquiv.symm_apply_apply face
theorem face_index_at (i : Fin 72) : faceIndex (faceAt i) = i :=
  faceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Flux.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
