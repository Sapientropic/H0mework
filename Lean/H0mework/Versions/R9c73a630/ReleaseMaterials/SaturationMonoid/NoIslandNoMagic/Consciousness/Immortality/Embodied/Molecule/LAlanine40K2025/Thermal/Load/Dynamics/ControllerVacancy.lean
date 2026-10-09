import H0mework.Chemistry.LAlanineThermalLoad.OperatorNorm
import H0mework.Chemistry.LAlanineThermalLoad.EnergyNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.EnvironmentAlgebra

/-! # Controller vacancy is paid by the actual unitary displacement -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace StrictThermal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def emptyHamiltonian : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![2, 0]

def emptyObservable : ControllerJoint ι := Matrix.kronecker 1 emptyHamiltonian

theorem emptyObservable_norm_le : ‖(emptyObservable : ControllerJoint ι)‖ ≤ 2 := by
  apply (NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := ι)) emptyHamiltonian).trans
  rw [emptyHamiltonian, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by intro i; fin_cases i <;> norm_num)

theorem controller_complement (joint : ControllerJoint ι) (normalized : joint.trace = 1) :
    Collision.energy emptyObservable joint + controllerEnergy 2 joint = 2 := by
  have total : (emptyObservable : ControllerJoint ι) + Matrix.kronecker 1 (controllerHamiltonian 2) =
      (2 : ℂ) • 1 := by
    ext ⟨i, c⟩ ⟨j, d⟩
    fin_cases c <;> fin_cases d <;>
      simp [emptyObservable, emptyHamiltonian, controllerHamiltonian, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  rw [← environmentObservable_energy]
  have energy : Collision.energy
      (emptyObservable + Matrix.kronecker (1 : Matrix ι ι ℂ) (controllerHamiltonian 2)) joint = 2 := by
    rw [total]
    simp [Collision.energy, normalized]
  simpa only [Collision.energy, Matrix.add_mul, Matrix.trace_add, Complex.add_re] using energy

theorem chargedInput_empty_support (rho : Matrix ι ι ℂ) :
    (emptyObservable : ControllerJoint ι) * chargedInput rho = 0 ∧
      chargedInput rho * emptyObservable = 0 := by
  have zero : emptyHamiltonian * excitedController = 0 ∧
      excitedController * emptyHamiltonian = 0 := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [emptyHamiltonian, excitedController, Matrix.mul_apply, Fin.sum_univ_two]
  constructor <;>
    simp [emptyObservable, chargedInput, Matrix.kronecker, ← Matrix.mul_kronecker_mul,
      zero.1, zero.2]

theorem energy_pullback (O rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    Collision.energy O (Unitary.conjStarAlgAut ℂ _ U rho) =
      Collision.energy (Unitary.conjStarAlgAut ℂ _ (star U) O) rho := by
  have both := Work.Capacity.energy_unitary_conjugation
    (Unitary.conjStarAlgAut ℂ _ (star U) O) rho U
  have cancel : Unitary.conjStarAlgAut ℂ _ U
      (Unitary.conjStarAlgAut ℂ _ (star U) O) = O := by
    rw [← Unitary.conjStarAlgAut_mul_apply]
    simp
  rw [cancel] at both
  exact both

theorem empty_support_energy_shift (O rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ)
    (leftZero : O * rho = 0) (rightZero : rho * O = 0) :
    Collision.energy O (Unitary.conjStarAlgAut ℂ _ U rho) =
      Collision.energy (((star U : Matrix ι ι ℂ) - 1) * O * ((U : Matrix ι ι ℂ) - 1)) rho := by
  rw [energy_pullback]
  have leftTrace : ((star U : Matrix ι ι ℂ) * O * rho).trace = 0 := by
    rw [mul_assoc, leftZero, mul_zero, Matrix.trace_zero]
  have rightTrace : (O * (U : Matrix ι ι ℂ) * rho).trace = 0 := by
    rw [Matrix.trace_mul_cycle, rightZero, zero_mul, Matrix.trace_zero]
  simp only [Collision.energy, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star, mul_sub, sub_mul,
    one_mul, mul_one, Matrix.trace_sub, leftTrace, rightTrace, leftZero,
    sub_zero]

theorem chargedInput_controller_lower_bound (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) (U : Matrix.unitaryGroup (ι × Fin 2) ℂ) :
    2 - 2 * ‖(U : ControllerJoint ι) - 1‖ ^ 2 ≤
      controllerEnergy 2 (Unitary.conjStarAlgAut ℂ _ U (chargedInput rho)) := by
  have support := chargedInput_empty_support rho
  have vacancy : Collision.energy emptyObservable
      (Unitary.conjStarAlgAut ℂ _ U (chargedInput rho)) ≤ 2 * ‖(U : ControllerJoint ι) - 1‖ ^ 2 := by
    rw [empty_support_energy_shift _ _ _ support.1 support.2]
    apply (le_abs_self _).trans
    apply (energy_abs_le_norm _ _ (chargedInput_positive rho positive)
      (chargedInput_trace rho normalized)).trans
    have adjoint : ‖(star U : ControllerJoint ι) - 1‖ = ‖(U : ControllerJoint ι) - 1‖ := by
      simpa only [Unitary.coe_star, star_sub, star_one] using norm_star ((U : ControllerJoint ι) - 1)
    calc
      _ ≤ ‖(star U : ControllerJoint ι) - 1‖ * ‖(emptyObservable : ControllerJoint ι)‖ *
          ‖(U : ControllerJoint ι) - 1‖ := (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖(U : ControllerJoint ι) - 1‖ * 2 * ‖(U : ControllerJoint ι) - 1‖ := by
        rw [adjoint]
        gcongr
        exact emptyObservable_norm_le
      _ = _ := by ring
  have total := controller_complement (Unitary.conjStarAlgAut ℂ _ U (chargedInput rho))
    ((Thermal.Quantum.unitary_conjugate_trace (chargedInput rho) U).trans
      (chargedInput_trace rho normalized))
  linarith

end StrictThermal

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
