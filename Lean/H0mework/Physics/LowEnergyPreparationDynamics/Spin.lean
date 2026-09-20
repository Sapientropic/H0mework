import H0mework.Physics.LowEnergyQuantum.Preparation
import Mathlib.Tactic.NoncommRing

/-! Native spin exchange and the principal sign of the independent-dual equation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PreparationDynamics
open DiracCliffordRepresentation StageNineFullDiracAdjointMaterial
open scoped Matrix
noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem exchange_eq_gamma_product : diracAdjointSpinSwap = diracGamma 0 * diracGammaFive := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracAdjointSpinSwap, diracGamma, diracGammaZero, diracGammaFive,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

theorem exchange_sq : diracAdjointSpinSwap * diracAdjointSpinSwap = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diracAdjointSpinSwap, Matrix.mul_apply, Fin.sum_univ_four]

theorem exchange_hermitian : diracAdjointSpinSwap.conjTranspose = diracAdjointSpinSwap := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [diracAdjointSpinSwap, Matrix.conjTranspose_apply]

theorem principal_sign (mu : Fin 4) :
    diracAdjointSpinSwap * (Complex.I • diracGamma mu) =
      -(Complex.I • diracGamma mu).conjTranspose * diracAdjointSpinSwap := by
  ext row column
  fin_cases mu <;> fin_cases row <;> fin_cases column <;>
    norm_num [diracAdjointSpinSwap, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose_apply]

/-- The square is unchanged even though the original one-way insertion is retained. -/
theorem nilpotent_anticommuting_square {R : Type*} [Ring R]
    (free insertion : R) (nilpotent : insertion*insertion=0)
    (anticommutes : free*insertion+insertion*free=0) :
    (free+insertion)*(free+insertion)=free*free := by
  calc
    _ = free*free+(free*insertion+insertion*free)+insertion*insertion := by noncomm_ring
    _ = _ := by rw [nilpotent,anticommutes]; simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.PreparationDynamics
