import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime

noncomputable section

def adjacentSpatialFaceSumEquiv : AdjacentSpatialFace ≃ Fin 2 ⊕ Fin 54 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandCell1Runtime.wholeBandCell1FaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandCell1Runtime.wholeBandCell1FaceEquiv.symm i)
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

def adjacentSpatialFaceEquiv : AdjacentSpatialFace ≃ Fin 56 := adjacentSpatialFaceSumEquiv.trans finSumFinEquiv

def adjacentSpatialFaceAt (i : Fin 56) : AdjacentSpatialFace := adjacentSpatialFaceEquiv.symm i
def adjacentSpatialFaceIndex (face : AdjacentSpatialFace) : Fin 56 := adjacentSpatialFaceEquiv face

theorem adjacentSpatialFace_at_index (face : AdjacentSpatialFace) : adjacentSpatialFaceAt (adjacentSpatialFaceIndex face) = face :=
  adjacentSpatialFaceEquiv.symm_apply_apply face
theorem adjacentSpatialFace_index_at (i : Fin 56) : adjacentSpatialFaceIndex (adjacentSpatialFaceAt i) = i :=
  adjacentSpatialFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
