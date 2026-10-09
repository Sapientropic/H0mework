import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationRuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BandConservationRuntime

noncomputable section

def bandConservationFaceSumEquiv : BandConservationFace ≃ Fin 2 ⊕ Fin 56 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (AdjacentSpatialRuntime.adjacentSpatialFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (AdjacentSpatialRuntime.adjacentSpatialFaceEquiv.symm i)
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

def bandConservationFaceEquiv : BandConservationFace ≃ Fin 58 := bandConservationFaceSumEquiv.trans finSumFinEquiv

def bandConservationFaceAt (i : Fin 58) : BandConservationFace := bandConservationFaceEquiv.symm i
def bandConservationFaceIndex (face : BandConservationFace) : Fin 58 := bandConservationFaceEquiv face

theorem bandConservationFace_at_index (face : BandConservationFace) : bandConservationFaceAt (bandConservationFaceIndex face) = face :=
  bandConservationFaceEquiv.symm_apply_apply face
theorem bandConservationFace_index_at (i : Fin 58) : bandConservationFaceIndex (bandConservationFaceAt i) = i :=
  bandConservationFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.BandConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
