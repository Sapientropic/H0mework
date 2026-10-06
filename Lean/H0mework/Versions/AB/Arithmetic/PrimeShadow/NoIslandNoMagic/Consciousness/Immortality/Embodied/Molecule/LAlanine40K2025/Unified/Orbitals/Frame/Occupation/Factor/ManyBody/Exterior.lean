import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Spin
import Mathlib.LinearAlgebra.ExteriorPower.Basis

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open scoped Matrix
noncomputable section

abbrev OneBody := SpinBasis → ℂ

def orbital (s : SpinSlot) : OneBody := spinFactor.col s

def orbitalDual (s : SpinSlot) : Module.Dual ℂ OneBody :=
  (LinearMap.proj s).comp spinFactor.conjTranspose.mulVecLin

theorem orbital_dual_pair (s t : SpinSlot) :
    orbitalDual s (orbital t) = if s = t then 1 else 0 := by
  have h := congrArg (fun A : Matrix SpinSlot SpinSlot ℂ => A s t) spin_isometry
  simpa only [orbitalDual,orbital,LinearMap.comp_apply,LinearMap.proj_apply,
    Matrix.mulVecLin_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.col_apply,
    Matrix.one_apply] using h

def spinIndex : Fin 48 ≃ SpinSlot :=
  Fintype.equivOfCardEq (by decide)

def orbitalFamily (k : Fin 48) : OneBody := orbital (spinIndex k)
def dualFamily (k : Fin 48) : Module.Dual ℂ OneBody := orbitalDual (spinIndex k)

def slaterState : ⋀[ℂ]^48 OneBody :=
  exteriorPower.ιMulti ℂ 48 orbitalFamily

def slaterDual : Module.Dual ℂ (⋀[ℂ]^48 OneBody) :=
  exteriorPower.pairingDual ℂ OneBody 48
    (exteriorPower.ιMulti ℂ 48 dualFamily)

theorem slater_pairing : slaterDual slaterState = 1 := by
  change exteriorPower.pairingDual ℂ OneBody 48
    (exteriorPower.ιMulti ℂ 48 dualFamily)
    (exteriorPower.ιMulti ℂ 48 orbitalFamily) = 1
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  have gram : Matrix.of (fun i j : Fin 48 => dualFamily j (orbitalFamily i)) = 1 := by
    ext i j
    rw [Matrix.of_apply,dualFamily,orbitalFamily,orbital_dual_pair]
    by_cases h : i = j
    · subst h
      simp
    · simp [spinIndex.injective.eq_iff, h,eq_comm]
  simpa only [Matrix.det_one] using congrArg Matrix.det gram

theorem slater_nonzero : slaterState ≠ 0 := by
  intro zero
  have h := slater_pairing
  rw [zero,map_zero] at h
  norm_num at h

theorem slater_exchange (σ : Equiv.Perm (Fin 48)) :
    exteriorPower.ιMulti ℂ 48 (orbitalFamily ∘ σ) =
      Equiv.Perm.sign σ • slaterState :=
  (exteriorPower.ιMulti ℂ 48).map_perm orbitalFamily σ

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
