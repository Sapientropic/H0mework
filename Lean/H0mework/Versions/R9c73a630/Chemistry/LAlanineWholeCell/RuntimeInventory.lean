import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact finite inventory: two full-cell faces and the original twenty-four faces. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellRuntime

noncomputable section

def wholeFaceSumEquiv : WholeCellFace ≃ Fin 2 ⊕ Fin 24 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (SpatialRuntime.spatialFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (SpatialRuntime.spatialFaceEquiv.symm i)
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

def wholeFaceEquiv : WholeCellFace ≃ Fin 26 := wholeFaceSumEquiv.trans finSumFinEquiv

def wholeFaceAt (i : Fin 26) : WholeCellFace := wholeFaceEquiv.symm i
def wholeFaceIndex (face : WholeCellFace) : Fin 26 := wholeFaceEquiv face

theorem wholeFace_at_index (face : WholeCellFace) : wholeFaceAt (wholeFaceIndex face) = face :=
  wholeFaceEquiv.symm_apply_apply face
theorem wholeFace_index_at (i : Fin 26) : wholeFaceIndex (wholeFaceAt i) = i :=
  wholeFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeCellRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
