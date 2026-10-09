import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Runtime

noncomputable section

def wholeBandCell0FaceSumEquiv : WholeBandCell0Face ≃ Fin 2 ⊕ Fin 46 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandFlowRuntime.wholeBandFlowFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandFlowRuntime.wholeBandFlowFaceEquiv.symm i)
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

def wholeBandCell0FaceEquiv : WholeBandCell0Face ≃ Fin 48 := wholeBandCell0FaceSumEquiv.trans finSumFinEquiv

def wholeBandCell0FaceAt (i : Fin 48) : WholeBandCell0Face := wholeBandCell0FaceEquiv.symm i
def wholeBandCell0FaceIndex (face : WholeBandCell0Face) : Fin 48 := wholeBandCell0FaceEquiv face

theorem wholeBandCell0Face_at_index (face : WholeBandCell0Face) : wholeBandCell0FaceAt (wholeBandCell0FaceIndex face) = face :=
  wholeBandCell0FaceEquiv.symm_apply_apply face
theorem wholeBandCell0Face_index_at (i : Fin 48) : wholeBandCell0FaceIndex (wholeBandCell0FaceAt i) = i :=
  wholeBandCell0FaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
