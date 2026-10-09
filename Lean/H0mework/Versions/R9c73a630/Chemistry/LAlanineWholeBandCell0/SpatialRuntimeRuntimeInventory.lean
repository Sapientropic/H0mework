import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.SpatialRuntimeRuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialRuntime

noncomputable section

def wholeBandCell0SpatialFaceSumEquiv : WholeBandCell0SpatialFace ≃ Fin 2 ⊕ Fin 50 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialFaceEquiv.symm i)
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

def wholeBandCell0SpatialFaceEquiv : WholeBandCell0SpatialFace ≃ Fin 52 := wholeBandCell0SpatialFaceSumEquiv.trans finSumFinEquiv

def wholeBandCell0SpatialFaceAt (i : Fin 52) : WholeBandCell0SpatialFace := wholeBandCell0SpatialFaceEquiv.symm i
def wholeBandCell0SpatialFaceIndex (face : WholeBandCell0SpatialFace) : Fin 52 := wholeBandCell0SpatialFaceEquiv face

theorem wholeBandCell0SpatialFace_at_index (face : WholeBandCell0SpatialFace) : wholeBandCell0SpatialFaceAt (wholeBandCell0SpatialFaceIndex face) = face :=
  wholeBandCell0SpatialFaceEquiv.symm_apply_apply face
theorem wholeBandCell0SpatialFace_index_at (i : Fin 52) : wholeBandCell0SpatialFaceIndex (wholeBandCell0SpatialFaceAt i) = i :=
  wholeBandCell0SpatialFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
