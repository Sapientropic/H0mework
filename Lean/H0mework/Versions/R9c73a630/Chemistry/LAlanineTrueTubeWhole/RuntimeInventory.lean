import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The same occurrence installs its complete original signed-gradient window. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime

noncomputable section

def wholeTubeFaceSumEquiv : WholeTubeFace ≃ Fin 2 ⊕ Fin 30 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (TrueTubeRuntime.tubeFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (TrueTubeRuntime.tubeFaceEquiv.symm i)
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

def wholeTubeFaceEquiv : WholeTubeFace ≃ Fin 32 := wholeTubeFaceSumEquiv.trans finSumFinEquiv

def wholeTubeFaceAt (i : Fin 32) : WholeTubeFace := wholeTubeFaceEquiv.symm i
def wholeTubeFaceIndex (face : WholeTubeFace) : Fin 32 := wholeTubeFaceEquiv face

theorem wholeTubeFace_at_index (face : WholeTubeFace) : wholeTubeFaceAt (wholeTubeFaceIndex face) = face :=
  wholeTubeFaceEquiv.symm_apply_apply face
theorem wholeTubeFace_index_at (i : Fin 32) : wholeTubeFaceIndex (wholeTubeFaceAt i) = i :=
  wholeTubeFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
