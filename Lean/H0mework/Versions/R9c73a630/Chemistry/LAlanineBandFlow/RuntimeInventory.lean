import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlow.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The original occurrence installs the whole-band source and its paid dependent restrictions. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime

noncomputable section

def wholeBandFlowFaceSumEquiv : WholeBandFlowFace ≃ Fin 2 ⊕ Fin 44 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (WholeBandRuntime.wholeBandFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (WholeBandRuntime.wholeBandFaceEquiv.symm i)
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

def wholeBandFlowFaceEquiv : WholeBandFlowFace ≃ Fin 46 := wholeBandFlowFaceSumEquiv.trans finSumFinEquiv

def wholeBandFlowFaceAt (i : Fin 46) : WholeBandFlowFace := wholeBandFlowFaceEquiv.symm i
def wholeBandFlowFaceIndex (face : WholeBandFlowFace) : Fin 46 := wholeBandFlowFaceEquiv face

theorem wholeBandFlowFace_at_index (face : WholeBandFlowFace) : wholeBandFlowFaceAt (wholeBandFlowFaceIndex face) = face :=
  wholeBandFlowFaceEquiv.symm_apply_apply face
theorem wholeBandFlowFace_index_at (i : Fin 46) : wholeBandFlowFaceIndex (wholeBandFlowFaceAt i) = i :=
  wholeBandFlowFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
