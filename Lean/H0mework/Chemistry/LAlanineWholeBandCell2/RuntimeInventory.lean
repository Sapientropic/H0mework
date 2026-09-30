import H0mework.Chemistry.LAlanineWholeBandCell2.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic
/-! The closed sixty-four-face inventory: all original sixty-two faces and two calculation faces. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime

noncomputable section

def initialFieldFaceSumEquiv : InitialFieldFace ≃ Fin 2 ⊕ Fin 62 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandSaturation.Runtime.saturationFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandSaturation.Runtime.saturationFaceEquiv.symm i)
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

def initialFieldFaceEquiv : InitialFieldFace ≃ Fin 64 := initialFieldFaceSumEquiv.trans finSumFinEquiv

def initialFieldFaceAt (i : Fin 64) : InitialFieldFace := initialFieldFaceEquiv.symm i
def initialFieldFaceIndex (face : InitialFieldFace) : Fin 64 := initialFieldFaceEquiv face

theorem initialFieldFace_at_index (face : InitialFieldFace) : initialFieldFaceAt (initialFieldFaceIndex face) = face :=
  initialFieldFaceEquiv.symm_apply_apply face
theorem initialFieldFace_index_at (i : Fin 64) : initialFieldFaceIndex (initialFieldFaceAt i) = i :=
  initialFieldFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
