import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowBoundary.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The original occurrence installs its generated true-flow boundary. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime

noncomputable section

def trueBoundaryFaceSumEquiv : TrueBoundaryFace ≃ Fin 2 ⊕ Fin 36 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (TrueFlowGeometryRuntime.geometryFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (TrueFlowGeometryRuntime.geometryFaceEquiv.symm i)
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

def trueBoundaryFaceEquiv : TrueBoundaryFace ≃ Fin 38 := trueBoundaryFaceSumEquiv.trans finSumFinEquiv

def trueBoundaryFaceAt (i : Fin 38) : TrueBoundaryFace := trueBoundaryFaceEquiv.symm i
def trueBoundaryFaceIndex (face : TrueBoundaryFace) : Fin 38 := trueBoundaryFaceEquiv face

theorem trueBoundaryFace_at_index (face : TrueBoundaryFace) : trueBoundaryFaceAt (trueBoundaryFaceIndex face) = face :=
  trueBoundaryFaceEquiv.symm_apply_apply face
theorem trueBoundaryFace_index_at (i : Fin 38) : trueBoundaryFaceIndex (trueBoundaryFaceAt i) = i :=
  trueBoundaryFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
