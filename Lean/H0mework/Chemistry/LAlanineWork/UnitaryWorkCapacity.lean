import H0mework.Chemistry.LAlanineWork.GeneratedPassiveState

/-!
# The source-generated optimum is an operational work capacity

The control class is all unitaries at the same final Hamiltonian. The optimal
unitary is generated from the two source spectra; it is not supplied as a premise.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Capacity

open Quantum Collision Unitary
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

theorem conjugatedHermitian (rho : Matrix ι ι ℂ) (hRho : rho.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) : (conjStarAlgAut ℂ _ U rho).IsHermitian := by
  change IsSelfAdjoint (conjStarAlgAut ℂ _ U rho)
  exact hRho.isSelfAdjoint.map (conjStarAlgAut ℂ _ U)

theorem conjugated_charpoly (rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    (conjStarAlgAut ℂ _ U rho).charpoly = rho.charpoly := by
  rw [conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul]

theorem passiveEnergy_eq_of_charpoly (H rho sigma : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hRho : rho.IsHermitian) (hSigma : sigma.IsHermitian)
    (same : rho.charpoly = sigma.charpoly) :
    passiveEnergy H rho hH hRho = passiveEnergy H sigma hH hSigma := by
  have spectrum := (hRho.eigenvalues_eq_eigenvalues_iff hSigma).mpr same
  simp only [passiveEnergy, passivePopulations, spectrum]

def ergotropy (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) : ℝ :=
  energy H rho - passiveEnergy H rho hH hRho

theorem ergotropy_nonnegative (H rho : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hRho : rho.IsHermitian) : 0 ≤ ergotropy H rho hH hRho := by
  apply sub_nonneg.mpr
  simpa using passiveEnergy_minimal H rho hH hRho 1

theorem extractedWork_le_ergotropy (H rho : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hRho : rho.IsHermitian) (U : Matrix.unitaryGroup ι ℂ) :
    energy H rho - energy H (conjStarAlgAut ℂ _ U rho) ≤ ergotropy H rho hH hRho :=
  sub_le_sub_left (passiveEnergy_minimal H rho hH hRho U) _

theorem ergotropy_attained (H rho : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    energy H rho - energy H (conjStarAlgAut ℂ _ (passiveUnitary H rho hH hRho) rho) =
      ergotropy H rho hH hRho := by
  rw [passiveUnitary_generates, passiveEnergy_attained]
  rfl

/-- Spectral invariance pays the capacity balance; it is not inferred from entropy alone. -/
theorem ergotropy_unitary_change (H rho : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hRho : rho.IsHermitian) (U : Matrix.unitaryGroup ι ℂ) :
    ergotropy H (conjStarAlgAut ℂ _ U rho) hH (conjugatedHermitian rho hRho U) -
      ergotropy H rho hH hRho = energy H (conjStarAlgAut ℂ _ U rho) - energy H rho := by
  have same := passiveEnergy_eq_of_charpoly H (conjStarAlgAut ℂ _ U rho) rho
    hH (conjugatedHermitian rho hRho U) hRho (conjugated_charpoly rho U)
  unfold ergotropy
  rw [same]
  ring

theorem passiveState_zero_capacity (H rho : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    ergotropy H (conjStarAlgAut ℂ _ (passiveUnitary H rho hH hRho) rho) hH
      (conjugatedHermitian rho hRho (passiveUnitary H rho hH hRho)) = 0 := by
  have balance := ergotropy_unitary_change H rho hH hRho (passiveUnitary H rho hH hRho)
  have attained := ergotropy_attained H rho hH hRho
  linarith

end

end LAlanine40K2025.Thermal.Work.Capacity
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
