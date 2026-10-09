import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime

noncomputable section

def wholeBandCell0DifferentialFaceSumEquiv : WholeBandCell0DifferentialFace ≃ Fin 2 ⊕ Fin 48 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandCell0Runtime.wholeBandCell0FaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandCell0Runtime.wholeBandCell0FaceEquiv.symm i)
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

def wholeBandCell0DifferentialFaceEquiv : WholeBandCell0DifferentialFace ≃ Fin 50 := wholeBandCell0DifferentialFaceSumEquiv.trans finSumFinEquiv

def wholeBandCell0DifferentialFaceAt (i : Fin 50) : WholeBandCell0DifferentialFace := wholeBandCell0DifferentialFaceEquiv.symm i
def wholeBandCell0DifferentialFaceIndex (face : WholeBandCell0DifferentialFace) : Fin 50 := wholeBandCell0DifferentialFaceEquiv face

theorem wholeBandCell0DifferentialFace_at_index (face : WholeBandCell0DifferentialFace) : wholeBandCell0DifferentialFaceAt (wholeBandCell0DifferentialFaceIndex face) = face :=
  wholeBandCell0DifferentialFaceEquiv.symm_apply_apply face
theorem wholeBandCell0DifferentialFace_index_at (i : Fin 50) : wholeBandCell0DifferentialFaceIndex (wholeBandCell0DifferentialFaceAt i) = i :=
  wholeBandCell0DifferentialFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
