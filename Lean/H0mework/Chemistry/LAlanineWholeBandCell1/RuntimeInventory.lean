import H0mework.Chemistry.LAlanineWholeBandCell1.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell1Runtime

noncomputable section

def wholeBandCell1FaceSumEquiv : WholeBandCell1Face ≃ Fin 2 ⊕ Fin 52 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandCell0SpatialRuntime.wholeBandCell0SpatialFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandCell0SpatialRuntime.wholeBandCell0SpatialFaceEquiv.symm i)
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

def wholeBandCell1FaceEquiv : WholeBandCell1Face ≃ Fin 54 := wholeBandCell1FaceSumEquiv.trans finSumFinEquiv

def wholeBandCell1FaceAt (i : Fin 54) : WholeBandCell1Face := wholeBandCell1FaceEquiv.symm i
def wholeBandCell1FaceIndex (face : WholeBandCell1Face) : Fin 54 := wholeBandCell1FaceEquiv face

theorem wholeBandCell1Face_at_index (face : WholeBandCell1Face) : wholeBandCell1FaceAt (wholeBandCell1FaceIndex face) = face :=
  wholeBandCell1FaceEquiv.symm_apply_apply face
theorem wholeBandCell1Face_index_at (i : Fin 54) : wholeBandCell1FaceIndex (wholeBandCell1FaceAt i) = i :=
  wholeBandCell1FaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandCell1Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
