import H0mework.Chemistry.LAlanineBandCache.SaturationRuntimeFacade
import Mathlib.Logic.Equiv.Fin.Basic

/-! The closed sixty-two-face inventory: all original sixty faces and two calculation faces. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime

noncomputable section

def saturationFaceSumEquiv : SaturationFace ≃ Fin 2 ⊕ Fin 60 where
  toFun := fun face => match face with
    | .component .material => .inl 0
    | .component .certificate => .inl 1
    | .inherited face => .inr (LAlanine40K2025.AtomicMass.Runtime.atomicMassFaceEquiv face)
  invFun := fun index => match index with
    | .inl i => if i = 0 then .component .material else .component .certificate
    | .inr i => .inherited (LAlanine40K2025.AtomicMass.Runtime.atomicMassFaceEquiv.symm i)
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

def saturationFaceEquiv : SaturationFace ≃ Fin 62 := saturationFaceSumEquiv.trans finSumFinEquiv

def saturationFaceAt (i : Fin 62) : SaturationFace := saturationFaceEquiv.symm i
def saturationFaceIndex (face : SaturationFace) : Fin 62 := saturationFaceEquiv face

theorem saturationFace_at_index (face : SaturationFace) : saturationFaceAt (saturationFaceIndex face) = face :=
  saturationFaceEquiv.symm_apply_apply face
theorem saturationFace_index_at (i : Fin 62) : saturationFaceIndex (saturationFaceAt i) = i :=
  saturationFaceEquiv.apply_symm_apply i

end
end LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule