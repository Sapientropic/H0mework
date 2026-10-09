import H0mework.Chemistry.LAlanineWork.UnitaryWorkCapacity
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Maximum

open Collision Work.Capacity Quantum Unitary
open scoped Matrix ComplexOrder
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def chargeUnitary (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    Matrix.unitaryGroup ι ℂ := passiveUnitary (-H) rho hH.neg hRho

def chargedState (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) : Matrix ι ι ℂ :=
  conjStarAlgAut ℂ (Matrix ι ι ℂ) (chargeUnitary H rho hH hRho) rho

omit [DecidableEq ι] in
theorem negative_energy (H rho : Matrix ι ι ℂ) : energy (-H) rho = -energy H rho := by
  simp [energy]

theorem charge_maximal (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian)
    (V : Matrix.unitaryGroup ι ℂ) :
    energy H (conjStarAlgAut ℂ (Matrix ι ι ℂ) V rho) ≤ energy H (chargedState H rho hH hRho) := by
  have bound := passiveEnergy_minimal (-H) rho hH.neg hRho V
  rw [← passiveEnergy_attained, ← passiveUnitary_generates] at bound
  rw [negative_energy, negative_energy] at bound
  exact neg_le_neg_iff.mp bound

theorem passive_mean_bound (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    Fintype.card ι * passiveEnergy H rho hH positive.isHermitian ≤ H.trace.re := by
  have chebyshev := (passivePopulations_antivary H rho hH positive.isHermitian).card_mul_sum_le_sum_mul_sum
  have populations : ∑ i, passivePopulations rho positive.isHermitian i = 1 := by
    change (∑ i, positive.isHermitian.eigenvalues (spectralReverse i)) = 1
    exact (Equiv.sum_comp spectralReverse _).trans (eigenvalues_normalized rho positive normalized)
  have spectrum : (∑ i, hH.eigenvalues i) = H.trace.re := by
    rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
    rfl
  rw [populations, mul_one, spectrum] at chebyshev
  exact chebyshev

theorem charge_mean_lower (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    H.trace.re ≤ Fintype.card ι * energy H (chargedState H rho hH positive.isHermitian) := by
  have upper := passive_mean_bound (-H) rho hH.neg positive normalized
  rw [← passiveEnergy_attained, ← passiveUnitary_generates, negative_energy,
    Matrix.trace_neg, Complex.neg_re] at upper
  dsimp only [chargedState, chargeUnitary]
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Charging.Maximum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
