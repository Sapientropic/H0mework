import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.InteractionSource

/-! # A same-history refocusing calculation and an independently read output capacity -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Recovery

open Powered.Dynamics Load.Source Load.Producer Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

/-- The first pulse reverses the source's complete bare Hamiltonian, not its actual load history. -/
def reverseBareUnitary (time : ℝ) : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  flowUnitary (-Powered.Producer.poweredTotalHamiltonian) (-2) 0
    Powered.Producer.poweredTotalHamiltonian_hermitian.neg Matrix.isHermitian_zero time

theorem reverseBareUnitary_actual (time : ℝ) :
    reverseBareUnitary time =
      flowUnitary Powered.Producer.poweredTotalHamiltonian 2 0
        Powered.Producer.poweredTotalHamiltonian_hermitian Matrix.isHermitian_zero (-time) := by
  apply Subtype.ext
  simp only [reverseBareUnitary, flowUnitary_matrix_exp]
  congr 1
  have negative : totalHamiltonian (-Powered.Producer.poweredTotalHamiltonian) (-2) 0 =
      -totalHamiltonian Powered.Producer.poweredTotalHamiltonian 2 0 := by
    have diagonal : controllerHamiltonian (-2) = -controllerHamiltonian 2 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [controllerHamiltonian]
    ext i j
    simp [totalHamiltonian, bareHamiltonian, diagonal, Matrix.kronecker,
      Matrix.kroneckerMap_apply, add_comm]
  rw [negative]
  simp

def parentLift : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  Load.Quantum.localUnitary loadParentUnitary 1

/-- A fixed echo of the two already consumed PC ticks, after a one-q reverse-bare pulse. -/
def recoveryUnitary : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  star parentLift * reverseBareUnitary (Propagation.Producer.nativeClockStep : ℝ)

def recoveryCurrent : LoadState := loadStateNext loadInitialState

def recoveryNext : LoadState :=
  ⟨recoveryCurrent.localClock + 3 * Propagation.Producer.nativeClockStep,
    recoveryUnitary * recoveryCurrent.action⟩

def preparationJoint : LoadedJoint :=
  Matrix.kronecker (chargedInput Powered.Producer.sourceReceivedPair) environmentState

theorem initial_from_preparation : loadInitialJoint =
    Unitary.conjStarAlgAut ℂ _ parentLift preparationJoint := by
  rw [loadInitialJoint, loadParent_joint_from_preparation]
  change _ = Load.Quantum.localConjugation loadParentUnitary 1 preparationJoint
  rw [preparationJoint, Load.Quantum.localConjugation_tensor]
  have identity (B : Matrix (Fin 2) (Fin 2) ℂ) : Thermal.Quantum.conjugation 1 B = B := by
    change Unitary.conjStarAlgAut ℂ _ 1 B = B
    simp
  rw [identity]
  rfl

def recoveryErrorUnitary : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  star parentLift * loadInteractionPicture (Propagation.Producer.nativeClockStep : ℝ) * parentLift

theorem recoveryNext_actual : recoveryNext.joint =
    Unitary.conjStarAlgAut ℂ _ recoveryUnitary recoveryCurrent.joint := by
  exact Unitary.conjStarAlgAut_mul_apply _ _ _

theorem recoveryNext_from_preparation : recoveryNext.joint =
    Unitary.conjStarAlgAut ℂ _ recoveryErrorUnitary preparationJoint := by
  rw [recoveryNext_actual]
  have received : recoveryCurrent.joint = Unitary.conjStarAlgAut ℂ _
      (loadUnitary (Propagation.Producer.nativeClockStep : ℝ)) loadInitialJoint := by
    rw [recoveryCurrent, loadStateNext_joint, loadInitialState_received]
    rfl
  rw [received]
  rw [initial_from_preparation]
  simp only [recoveryErrorUnitary, recoveryUnitary, reverseBareUnitary_actual,
    loadInteractionPicture, Unitary.conjStarAlgAut_mul_apply]

theorem unitary_displacement_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) :
    ‖((star U * V * U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) - 1‖ =
      ‖(V : Matrix ι ι ℂ) - 1‖ := by
  have factor : ((star U * V * U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) - 1 =
      ((star U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *
        ((V : Matrix ι ι ℂ) - 1) * (U : Matrix ι ι ℂ) := by
    simp only [MulMemClass.coe_mul, mul_sub, sub_mul, mul_one,
      Unitary.coe_star, Unitary.coe_star_mul_self]
  rw [factor, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem recoveryError_norm : ‖(recoveryErrorUnitary : LoadedJoint) - 1‖ ≤
    5 * (Propagation.Producer.nativeClockStep : ℝ) / 4 := by
  rw [recoveryErrorUnitary, unitary_displacement_conjugation]
  have estimate := norm_sub_le ((loadInteractionPicture (Propagation.Producer.nativeClockStep : ℝ) : LoadedJoint) - 1 -
    (Propagation.Producer.nativeClockStep : ℝ) • (-Complex.I • loadInteraction))
    (-(Propagation.Producer.nativeClockStep : ℝ) • (-Complex.I • loadInteraction))
  have normLinear : ‖(Propagation.Producer.nativeClockStep : ℝ) • (-Complex.I • loadInteraction)‖ ≤
      (Propagation.Producer.nativeClockStep : ℝ) := by
    simp only [norm_smul, norm_neg, Complex.norm_I, one_mul, Real.norm_eq_abs,
      abs_of_nonneg nativeClock_small.1.le]
    simpa using mul_le_mul_of_nonneg_left loadInteraction_norm_le_one nativeClock_small.1.le
  have triangle : ‖(loadInteractionPicture (Propagation.Producer.nativeClockStep : ℝ) : LoadedJoint) - 1‖ ≤
      ‖(loadInteractionPicture (Propagation.Producer.nativeClockStep : ℝ) : LoadedJoint) - 1 -
        (Propagation.Producer.nativeClockStep : ℝ) • (-Complex.I • loadInteraction)‖ +
      ‖(Propagation.Producer.nativeClockStep : ℝ) • (-Complex.I • loadInteraction)‖ := by
    simpa only [neg_smul, sub_neg_eq_add, sub_add_cancel, norm_neg] using estimate
  linarith [loadInteractionPicture_actual_error]

section Vacancy

variable {P E : Type*} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]

theorem left_energy (H : Matrix (P × Fin 2) (P × Fin 2) ℂ)
    (joint : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) :
    Collision.energy (Matrix.kronecker H 1) joint = Collision.energy H (systemReduce joint) := by
  have split := jointEnergy_real_eq_reduced H (0 : Matrix E E ℂ) joint
  simpa [Matrix.kronecker, Collision.energy] using split

theorem remembered_vacancy_bound (rho : Matrix P P ℂ) (tau : Matrix E E ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1)
    (tauPositive : tau.PosSemidef) (tauNormalized : tau.trace = 1)
    (U : Matrix.unitaryGroup ((P × Fin 2) × E) ℂ) :
    2 - 2 * ‖(U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1‖ ^ 2 ≤
      controllerEnergy 2 (systemReduce
        (Unitary.conjStarAlgAut ℂ _ U (Matrix.kronecker (chargedInput rho) tau))) := by
  let O : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ :=
    Matrix.kronecker emptyObservable 1
  let origin := Matrix.kronecker (chargedInput rho) tau
  have hpos : origin.PosSemidef := (chargedInput_positive rho positive).kronecker tauPositive
  have htrace : origin.trace = 1 := by
    simp only [origin, Matrix.kronecker, Matrix.trace_kronecker,
      chargedInput_trace rho normalized, tauNormalized, mul_one]
  have support : O * origin = 0 ∧ origin * O = 0 := by
    have zero := chargedInput_empty_support rho
    constructor <;> simp [O, origin, Matrix.kronecker, ← Matrix.mul_kronecker_mul, zero.1, zero.2]
  have normO : ‖O‖ ≤ 2 :=
    (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := P × Fin 2) (κ := E))
      (emptyObservable : ControllerJoint P)).trans emptyObservable_norm_le
  have vacancy : Collision.energy O (Unitary.conjStarAlgAut ℂ _ U origin) ≤
      2 * ‖(U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1‖ ^ 2 := by
    rw [empty_support_energy_shift O origin U support.1 support.2]
    apply (le_abs_self _).trans ((energy_abs_le_norm _ _ hpos htrace).trans _)
    have adjoint : ‖(star U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1‖ =
        ‖(U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1‖ := by
      simpa only [Unitary.coe_star, star_sub, star_one] using norm_star
        ((U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1)
    calc
      _ ≤ ‖(star U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1‖ * ‖O‖ *
          ‖(U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖(U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1‖ * 2 *
          ‖(U : Matrix ((P × Fin 2) × E) ((P × Fin 2) × E) ℂ) - 1‖ := by
        rw [adjoint]
        gcongr
      _ = _ := by ring
  have total := controller_complement (systemReduce (Unitary.conjStarAlgAut ℂ _ U origin))
    ((systemReduce_trace _).trans ((Thermal.Quantum.unitary_conjugate_trace origin U).trans htrace))
  change Collision.energy (Matrix.kronecker emptyObservable 1) _ ≤ _ at vacancy
  rw [left_energy] at vacancy
  linarith

end Vacancy

theorem recoveryNext_controller_bound :
    2 - 25 * (Propagation.Producer.nativeClockStep : ℝ) ^ 2 / 8 ≤
      controllerEnergy 2 (systemReduce recoveryNext.joint) := by
  rw [recoveryNext_from_preparation]
  have bound := remembered_vacancy_bound Powered.Producer.sourceReceivedPair environmentState
    Powered.Producer.sourceParentState.positive Powered.Producer.sourceParentState.normalized
    environmentState_positive environmentState_trace recoveryErrorUnitary
  change 2 - 2 * ‖(recoveryErrorUnitary : LoadedJoint) - 1‖ ^ 2 ≤
    controllerEnergy 2 (systemReduce (Unitary.conjStarAlgAut ℂ _ recoveryErrorUnitary preparationJoint)) at bound
  nlinarith [recoveryError_norm, norm_nonneg ((recoveryErrorUnitary : LoadedJoint) - 1)]

def qubitFlip : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]⟩

theorem qubitFlip_work (rho : Matrix (Fin 2) (Fin 2) ℂ) (normalized : rho.trace = 1) :
    Collision.energy (controllerHamiltonian 2) rho -
      Collision.energy (controllerHamiltonian 2) (Unitary.conjStarAlgAut ℂ _ qubitFlip rho) =
        2 * Collision.energy (controllerHamiltonian 2) rho - 2 := by
  have sum := congrArg Complex.re normalized
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.add_re, Complex.one_re] at sum
  simp only [Collision.energy, controllerHamiltonian, Unitary.conjStarAlgAut_apply]
  norm_num [qubitFlip, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.star_apply, Matrix.vecMul, dotProduct]
  linarith

theorem qubitFlip_capacity (rho : Matrix (Fin 2) (Fin 2) ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    2 * Collision.energy (controllerHamiltonian 2) rho - 2 ≤
      Work.Capacity.ergotropy (controllerHamiltonian 2) rho
        (controllerHamiltonian_hermitian 2) positive.isHermitian := by
  rw [← qubitFlip_work rho normalized]
  exact Work.Capacity.extractedWork_le_ergotropy _ _ _ _ _

def recoveryController : Matrix (Fin 2) (Fin 2) ℂ :=
  controllerReduce (systemReduce recoveryNext.joint)

theorem recoveryController_positive : recoveryController.PosSemidef :=
  controllerReduce_posSemidef _ (systemReduce_posSemidef _ recoveryNext.positive)

theorem recoveryController_normalized : recoveryController.trace = 1 :=
  (controllerReduce_trace _).trans ((systemReduce_trace _).trans recoveryNext.normalized)

theorem recoveryNext_capacity_bound :
    2 - 25 * (Propagation.Producer.nativeClockStep : ℝ) ^ 2 / 4 ≤
      Work.Capacity.ergotropy (controllerHamiltonian 2) recoveryController
        (controllerHamiltonian_hermitian 2) recoveryController_positive.isHermitian := by
  have capacity := qubitFlip_capacity recoveryController recoveryController_positive recoveryController_normalized
  have energyBound := recoveryNext_controller_bound
  change 2 - _ ≤ Collision.energy (controllerHamiltonian 2) recoveryController at energyBound
  linarith

end
end LAlanine40K2025.Thermal.Load.Recovery
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
