import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The original occurrence installs its actual true-flow quantitative bounds. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime

noncomputable section

def quantitativeFaceSumEquiv : QuantitativeFace ≃ Fin 2 ⊕ Fin 40 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (TrueFlowConservationRuntime.conservationFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (TrueFlowConservationRuntime.conservationFaceEquiv.symm i)
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

def quantitativeFaceEquiv : QuantitativeFace ≃ Fin 42 := quantitativeFaceSumEquiv.trans finSumFinEquiv

def quantitativeFaceAt (i : Fin 42) : QuantitativeFace := quantitativeFaceEquiv.symm i
def quantitativeFaceIndex (face : QuantitativeFace) : Fin 42 := quantitativeFaceEquiv face

theorem quantitativeFace_at_index (face : QuantitativeFace) : quantitativeFaceAt (quantitativeFaceIndex face) = face :=
  quantitativeFaceEquiv.symm_apply_apply face
theorem quantitativeFace_index_at (i : Fin 42) : quantitativeFaceIndex (quantitativeFaceAt i) = i :=
  quantitativeFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
