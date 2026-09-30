import H0mework.Chemistry.LAlanineSpatialRuntime.Facade
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.SpatialRuntime

noncomputable section

def spatialFaceSumEquiv : SpatialFace ≃ Fin 2 ⊕ Fin 22 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (ContinuousRuntime.bandFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (ContinuousRuntime.bandFaceEquiv.symm i)
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

def spatialFaceEquiv : SpatialFace ≃ Fin 24 := spatialFaceSumEquiv.trans finSumFinEquiv

def spatialFaceAt (i : Fin 24) : SpatialFace := spatialFaceEquiv.symm i
def spatialFaceIndex (face : SpatialFace) : Fin 24 := spatialFaceEquiv face

theorem spatialFace_at_index (face : SpatialFace) : spatialFaceAt (spatialFaceIndex face) = face :=
  spatialFaceEquiv.symm_apply_apply face
theorem spatialFace_index_at (i : Fin 24) : spatialFaceIndex (spatialFaceAt i) = i :=
  spatialFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.SpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
