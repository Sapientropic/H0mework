import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! Same-root boundary authority and inherited source inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BoundaryRuntime

noncomputable section

def boundaryFaceSumEquiv : BoundaryFace ≃ Fin 2 ⊕ Fin 26 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeCellRuntime.wholeFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeCellRuntime.wholeFaceEquiv.symm i)
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

def boundaryFaceEquiv : BoundaryFace ≃ Fin 28 := boundaryFaceSumEquiv.trans finSumFinEquiv

def boundaryFaceAt (i : Fin 28) : BoundaryFace := boundaryFaceEquiv.symm i
def boundaryFaceIndex (face : BoundaryFace) : Fin 28 := boundaryFaceEquiv face

theorem boundaryFace_at_index (face : BoundaryFace) : boundaryFaceAt (boundaryFaceIndex face) = face :=
  boundaryFaceEquiv.symm_apply_apply face
theorem boundaryFace_index_at (i : Fin 28) : boundaryFaceIndex (boundaryFaceAt i) = i :=
  boundaryFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.BoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
