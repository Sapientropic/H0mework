import H0mework.Chemistry.LAlanineTrueFlowGeometry.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The original occurrence installs its generated true-flow geometry. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime

noncomputable section

def geometryFaceSumEquiv : GeometryFace ≃ Fin 2 ⊕ Fin 34 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (TrueFlowDifferentialRuntime.differentialFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (TrueFlowDifferentialRuntime.differentialFaceEquiv.symm i)
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

def geometryFaceEquiv : GeometryFace ≃ Fin 36 := geometryFaceSumEquiv.trans finSumFinEquiv

def geometryFaceAt (i : Fin 36) : GeometryFace := geometryFaceEquiv.symm i
def geometryFaceIndex (face : GeometryFace) : Fin 36 := geometryFaceEquiv face

theorem geometryFace_at_index (face : GeometryFace) : geometryFaceAt (geometryFaceIndex face) = face :=
  geometryFaceEquiv.symm_apply_apply face
theorem geometryFace_index_at (i : Fin 36) : geometryFaceIndex (geometryFaceAt i) = i :=
  geometryFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
