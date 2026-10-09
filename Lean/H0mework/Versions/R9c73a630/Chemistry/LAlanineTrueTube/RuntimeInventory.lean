import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.RuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The same physical occurrence installs its actual true-ODE continuation face. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeRuntime

noncomputable section

def tubeFaceSumEquiv : TrueTubeFace ≃ Fin 2 ⊕ Fin 28 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (BoundaryRuntime.boundaryFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (BoundaryRuntime.boundaryFaceEquiv.symm i)
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

def tubeFaceEquiv : TrueTubeFace ≃ Fin 30 := tubeFaceSumEquiv.trans finSumFinEquiv

def tubeFaceAt (i : Fin 30) : TrueTubeFace := tubeFaceEquiv.symm i
def tubeFaceIndex (face : TrueTubeFace) : Fin 30 := tubeFaceEquiv face

theorem tubeFace_at_index (face : TrueTubeFace) : tubeFaceAt (tubeFaceIndex face) = face :=
  tubeFaceEquiv.symm_apply_apply face
theorem tubeFace_index_at (i : Fin 30) : tubeFaceIndex (tubeFaceAt i) = i :=
  tubeFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.TrueTubeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
