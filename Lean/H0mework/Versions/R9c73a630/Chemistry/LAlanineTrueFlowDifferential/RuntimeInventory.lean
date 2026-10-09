import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The original whole-flow occurrence installs its source-generated differential. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime

noncomputable section

def differentialFaceSumEquiv : DifferentialFace ≃ Fin 2 ⊕ Fin 32 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (TrueTubeWholeRuntime.wholeTubeFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (TrueTubeWholeRuntime.wholeTubeFaceEquiv.symm i)
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

def differentialFaceEquiv : DifferentialFace ≃ Fin 34 := differentialFaceSumEquiv.trans finSumFinEquiv

def differentialFaceAt (i : Fin 34) : DifferentialFace := differentialFaceEquiv.symm i
def differentialFaceIndex (face : DifferentialFace) : Fin 34 := differentialFaceEquiv face

theorem differentialFace_at_index (face : DifferentialFace) : differentialFaceAt (differentialFaceIndex face) = face :=
  differentialFaceEquiv.symm_apply_apply face
theorem differentialFace_index_at (i : Fin 34) : differentialFaceIndex (differentialFaceAt i) = i :=
  differentialFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
