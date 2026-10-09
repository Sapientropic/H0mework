import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFullCarrier.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic
/-! All64 original faces plus the complete band material and certificate. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Runtime

noncomputable section

def faceSumEquiv : BandFace ≃ Fin 2 ⊕ Fin 64 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandCell2.Runtime.initialFieldFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandCell2.Runtime.initialFieldFaceEquiv.symm i)
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

def faceEquiv : BandFace ≃ Fin 66 := faceSumEquiv.trans finSumFinEquiv

def faceAt (i : Fin 66) : BandFace := faceEquiv.symm i
def faceIndex (face : BandFace) : Fin 66 := faceEquiv face

theorem face_at_index (face : BandFace) : faceAt (faceIndex face) = face :=
  faceEquiv.symm_apply_apply face
theorem face_index_at (i : Fin 66) : faceIndex (faceAt i) = i :=
  faceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
