import H0mework.Chemistry.LAlanineTrueFlowConservation.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The original occurrence installs its actual true-flow conservation. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime

noncomputable section

def conservationFaceSumEquiv : ConservationFace ≃ Fin 2 ⊕ Fin 38 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (TrueFlowBoundaryRuntime.trueBoundaryFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (TrueFlowBoundaryRuntime.trueBoundaryFaceEquiv.symm i)
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

def conservationFaceEquiv : ConservationFace ≃ Fin 40 := conservationFaceSumEquiv.trans finSumFinEquiv

def conservationFaceAt (i : Fin 40) : ConservationFace := conservationFaceEquiv.symm i
def conservationFaceIndex (face : ConservationFace) : Fin 40 := conservationFaceEquiv face

theorem conservationFace_at_index (face : ConservationFace) : conservationFaceAt (conservationFaceIndex face) = face :=
  conservationFaceEquiv.symm_apply_apply face
theorem conservationFace_index_at (i : Fin 40) : conservationFaceIndex (conservationFaceAt i) = i :=
  conservationFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
