import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.SpectralReservoir
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Exchange

open Collision Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem unitary_observable_error (O rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) (U V : Matrix.unitaryGroup ι ℂ) :
    |energy O (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U rho) -
      energy O (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) V rho)| ≤
      2 * ‖O‖ * ‖(U : Matrix ι ι ℂ) - V‖ := by
  have read (W : Matrix.unitaryGroup ι ℂ) :
      energy O (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) W rho) =
        energy ((star W : Matrix ι ι ℂ) * O * (W : Matrix ι ι ℂ)) rho := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] using
      Load.Producer.StrictThermal.energy_pullback O rho W
  rw [read U, read V]
  unfold energy
  rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
  apply (energy_abs_le_norm _ rho positive normalized).trans
  have factor :
      (star U : Matrix ι ι ℂ) * O * (U : Matrix ι ι ℂ) - (star V : Matrix ι ι ℂ) * O * (V : Matrix ι ι ℂ) =
        ((star U : Matrix ι ι ℂ) - (star V : Matrix ι ι ℂ)) * O * (U : Matrix ι ι ℂ) +
          (star V : Matrix ι ι ℂ) * O * ((U : Matrix ι ι ℂ) - V) := by
    noncomm_ring
  rw [factor]
  calc
    _ ≤ ‖((star U : Matrix ι ι ℂ) - (star V : Matrix ι ι ℂ)) * O * (U : Matrix ι ι ℂ)‖ +
      ‖(star V : Matrix ι ι ℂ) * O * ((U : Matrix ι ι ℂ) - V)‖ := norm_add_le _ _
    _ = ‖((star U : Matrix ι ι ℂ) - (star V : Matrix ι ι ℂ)) * O‖ +
      ‖O * ((U : Matrix ι ι ℂ) - V)‖ := by
      rw [CStarRing.norm_mul_coe_unitary, Matrix.mul_assoc]
      congr 1
      exact CStarRing.norm_coe_unitary_mul (star V) _
    _ ≤ ‖(star U : Matrix ι ι ℂ) - (star V : Matrix ι ι ℂ)‖ * ‖O‖ +
      ‖O‖ * ‖(U : Matrix ι ι ℂ) - V‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by
      simp only [← star_sub, norm_star]
      ring

def exchangeUnitary (angle : ℝ) : Matrix.unitaryGroup (ι × ι) ℂ :=
  ⟨partialSwap (Real.cos angle) (Real.sin angle), partialSwap_unitary _ _ (Real.cos_sq_add_sin_sq angle)⟩

def nearTransfer (epsilon : ℝ) : Matrix.unitaryGroup (ι × ι) ℂ := exchangeUnitary (Real.pi / 2 - epsilon)
def fullTransfer : Matrix.unitaryGroup (ι × ι) ℂ := exchangeUnitary (Real.pi / 2)

theorem nearTransfer_error (epsilon : ℝ) :
    ‖(nearTransfer (ι := ι) epsilon : JointMatrix ι) - (fullTransfer (ι := ι) : JointMatrix ι)‖ ≤ 2 * |epsilon| := by
  have difference : (nearTransfer (ι := ι) epsilon : JointMatrix ι) - (fullTransfer (ι := ι) : JointMatrix ι) =
      (Real.sin epsilon : ℂ) • 1 -
        (Complex.I * ((Real.cos epsilon : ℂ) - 1)) • swapOperator := by
    change partialSwap (Real.cos (Real.pi / 2 - epsilon)) (Real.sin (Real.pi / 2 - epsilon)) -
      partialSwap (Real.cos (Real.pi / 2)) (Real.sin (Real.pi / 2)) = _
    simp only [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp only [partialSwap, Complex.ofReal_zero, Complex.ofReal_one, zero_smul, mul_one, sub_eq_add_neg]
    module
  rw [difference]
  calc
    _ ≤ ‖(Real.sin epsilon : ℂ) • (1 : JointMatrix ι)‖ +
      ‖(Complex.I * ((Real.cos epsilon : ℂ) - 1)) • (swapOperator : JointMatrix ι)‖ := norm_sub_le _ _
    _ = |Real.sin epsilon| + |Real.cos epsilon - 1| := by
      rw [norm_smul, norm_smul, norm_one, swap_norm, mul_one, mul_one,
        Complex.norm_real, norm_mul, Complex.norm_I, one_mul]
      congr 1
      norm_cast
    _ ≤ |epsilon| + |epsilon| := add_le_add Real.abs_sin_le_abs
      (by simpa only [Real.cos_zero, sub_zero] using Real.abs_cos_sub_cos_le epsilon 0)
    _ = _ := by ring

omit [Nonempty ι] in
theorem fullTransfer_system (rho tau : Matrix ι ι ℂ) (normalized : rho.trace = 1) :
    systemReduce (Unitary.conjStarAlgAut ℂ (JointMatrix ι) (fullTransfer (ι := ι)) (Matrix.kronecker rho tau)) = tau := by
  change systemNext rho tau (Real.cos (Real.pi / 2)) (Real.sin (Real.pi / 2)) = _
  rw [systemNext]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [jointNext_expansion]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_pow (by decide : 2 ≠ 0), one_pow,
    zero_smul, zero_add, one_smul, mul_zero, zero_mul, add_zero]
  rw [systemReduce_tensor, normalized, one_smul]

omit [Nonempty ι] in
theorem left_energy (O : Matrix ι ι ℂ) (joint : JointMatrix ι) :
    energy (Matrix.kronecker O 1) joint = energy O (systemReduce joint) := by
  simpa [energy, Matrix.kronecker, Powered.Dynamics.systemReduce, systemReduce] using
    Powered.Dynamics.jointEnergy_real_eq_reduced O (0 : Matrix ι ι ℂ) joint

theorem nearTransfer_read_error (O rho tau : Matrix ι ι ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1)
    (tauPositive : tau.PosSemidef) (tauNormalized : tau.trace = 1) (epsilon : ℝ) :
    |energy O (systemReduce (Unitary.conjStarAlgAut ℂ (JointMatrix ι) (nearTransfer epsilon)
      (Matrix.kronecker rho tau))) - energy O tau| ≤ 4 * ‖O‖ * |epsilon| := by
  have trace : (Matrix.kronecker rho tau).trace = 1 := by
    rw [Matrix.kronecker, Matrix.trace_kronecker, normalized, tauNormalized, mul_one]
  have error := unitary_observable_error (Matrix.kronecker O 1) (Matrix.kronecker rho tau)
    (positive.kronecker tauPositive) trace (nearTransfer epsilon) fullTransfer
  rw [left_energy, left_energy, fullTransfer_system rho tau normalized] at error
  apply error.trans
  have normO := NonUnitalStarAlgHom.norm_apply_le (tensorLeft (κ := ι)) O
  change ‖Matrix.kronecker O 1‖ ≤ ‖O‖ at normO
  have near := nearTransfer_error (ι := ι) epsilon
  calc
    _ ≤ (2 * ‖O‖) * (2 * |epsilon|) := by gcongr
    _ = _ := by ring

omit [Nonempty ι] in
theorem native_energy_balance (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (g time : ℝ) (rho : JointMatrix ι) :
    energy H (systemReduce (Quantum.conjugation (Dynamics.pairUnitary H hH g time) rho)) +
      energy H (bathReduce (Quantum.conjugation (Dynamics.pairUnitary H hH g time) rho)) =
      energy H (systemReduce rho) + energy H (bathReduce rho) := by
  have raw := Dynamics.pairAdvance_bareEnergy H hH g time rho
  rw [Dynamics.pairAdvance_eq_unitary H hH] at raw
  have balance : energy (Dynamics.freePairH H) (Quantum.conjugation (Dynamics.pairUnitary H hH g time) rho) =
      energy (Dynamics.freePairH H) rho := by
    simpa only [energy, Quantum.conjugation_apply] using congrArg Complex.re raw
  have split (state : JointMatrix ι) : energy (Dynamics.freePairH H) state =
      energy H (systemReduce state) + energy H (bathReduce state) := by
    simpa [Dynamics.freePairH, jointHamiltonian, energy, Powered.Dynamics.systemReduce,
      Powered.Dynamics.controllerReduce, systemReduce, bathReduce] using
      Powered.Dynamics.jointEnergy_real_eq_reduced H H state
  rwa [split, split] at balance

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Exchange
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
