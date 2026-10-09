import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandRuntime.Facade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The original occurrence installs the whole-band source and its paid dependent restrictions. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandRuntime

noncomputable section

def wholeBandFaceSumEquiv : WholeBandFace ≃ Fin 2 ⊕ Fin 42 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (TrueFlowQuantitativeRuntime.quantitativeFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (TrueFlowQuantitativeRuntime.quantitativeFaceEquiv.symm i)
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

def wholeBandFaceEquiv : WholeBandFace ≃ Fin 44 := wholeBandFaceSumEquiv.trans finSumFinEquiv

def wholeBandFaceAt (i : Fin 44) : WholeBandFace := wholeBandFaceEquiv.symm i
def wholeBandFaceIndex (face : WholeBandFace) : Fin 44 := wholeBandFaceEquiv face

theorem wholeBandFace_at_index (face : WholeBandFace) : wholeBandFaceAt (wholeBandFaceIndex face) = face :=
  wholeBandFaceEquiv.symm_apply_apply face
theorem wholeBandFace_index_at (i : Fin 44) : wholeBandFaceIndex (wholeBandFaceAt i) = i :=
  wholeBandFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
