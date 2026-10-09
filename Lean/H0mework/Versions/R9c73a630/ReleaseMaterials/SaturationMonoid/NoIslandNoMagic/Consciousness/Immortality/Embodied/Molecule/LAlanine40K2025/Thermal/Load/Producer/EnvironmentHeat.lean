import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.TransitionProbability
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.InteractionSource

/-! # Actual Gibbs-weighted flip probabilities generate finite-clock heat -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.HeatProbability

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weight (e : Fin 2) : ℝ := (environmentPMF e).toReal

theorem weight_nonnegative (e : Fin 2) : 0 ≤ weight e := ENNReal.toReal_nonneg

theorem weights_sum : weight 0 + weight 1 = 1 := by
  simpa only [weight, Fin.sum_univ_two] using Population.pmf_sum_toReal environmentPMF

omit [Fintype ι] [DecidableEq ι] in
theorem product_decompose (rho : Matrix ι ι ℂ) :
    Matrix.kronecker rho environmentState =
      (weight 0 : ℂ) • tagged rho 0 + (weight 1 : ℂ) • tagged rho 1 := by
  ext ⟨i, e⟩ ⟨j, f⟩
  fin_cases e <;> fin_cases f <;>
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, environmentState, weight,
      tagged, Matrix.smul_apply, mul_comm]

theorem environment_energy_Q (sigma : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) :
    controllerEnergy 2 sigma = 2 * Collision.energy (Q 1) sigma := by
  rw [controllerEnergy_eq_probability]
  simp [Collision.energy, Q, Matrix.trace, Matrix.diag, Matrix.diagonal_mul,
    Fintype.sum_prod_type, excitedProbability]

omit [DecidableEq ι] in
theorem environment_initial_energy (rho : Matrix ι ι ℂ) (normalized : rho.trace = 1) :
    controllerEnergy 2 (Matrix.kronecker rho environmentState) = 2 * weight 1 := by
  unfold controllerEnergy
  rw [controllerReduce_tensor, normalized, one_smul]
  simp [Collision.energy, controllerHamiltonian, environmentState, weight,
    Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem unitary_probabilities_sum (rho : Matrix ι ι ℂ) (normalized : rho.trace = 1)
    (U : Matrix.unitaryGroup (ι × Fin 2) ℂ) (e : Fin 2) :
    Collision.energy (Q 0) ((U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) * tagged rho e * star (U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ)) +
      Collision.energy (Q 1) ((U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) * tagged rho e * star (U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ)) = 1 := by
  have read : ∀ T : Matrix (ι × Fin 2) (ι × Fin 2) ℂ,
      Collision.energy (Q 0) T + Collision.energy (Q 1) T = T.trace.re := by
    intro T
    rw [Collision.energy, Collision.energy, ← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, Q_sum, Matrix.one_mul]
  rw [read, Thermal.Quantum.unitary_conjugate_trace, tagged_trace rho normalized e]
  rfl

theorem net_environment_heat (rho : Matrix ι ι ℂ) (normalized : rho.trace = 1)
    (U : Matrix.unitaryGroup (ι × Fin 2) ℂ) :
    controllerEnergy 2 (Unitary.conjStarAlgAut ℂ _ U (Matrix.kronecker rho environmentState)) -
      controllerEnergy 2 (Matrix.kronecker rho environmentState) =
      2 * (weight 0 * Collision.energy (Q 1) ((U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) * tagged rho 0 * star (U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ)) -
        weight 1 * Collision.energy (Q 0) ((U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) * tagged rho 1 * star (U : Matrix (ι × Fin 2) (ι × Fin 2) ℂ))) := by
  have normalizedOutput := unitary_probabilities_sum rho normalized U 1
  rw [environment_initial_energy rho normalized, environment_energy_Q, Unitary.conjStarAlgAut_apply,
    product_decompose, Matrix.mul_add, Matrix.add_mul]
  simp only [mul_smul_comm, smul_mul_assoc, energy_add_right, energy_smul_right]
  nlinarith [congrArg (fun x : ℝ => weight 1 * x) normalizedOutput]

def smallQ (e : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun x => if x.2 = e then 1 else 0)

theorem Q_as_ceLift (e : Fin 2) : Q (ι := PairController) e = StrictThermal.ceLift (P := Pair) (smallQ e) := by
  rw [smallQ, StrictThermal.ceLift_diagonal]
  rfl

theorem ceLift_star (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    star (StrictThermal.ceLift (P := Pair) A) = StrictThermal.ceLift (star A) := by
  simp only [StrictThermal.ceLift, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem flip_exchange_square (e f : Fin 2) :
    star (flip f loadInteraction e) * flip f loadInteraction e =
      StrictThermal.ceLift (P := Pair)
        (star (smallQ f * controllerEnvironmentExchange * smallQ e) *
          (smallQ f * controllerEnvironmentExchange * smallQ e)) := by
  have transfer : flip f loadInteraction e = StrictThermal.ceLift (P := Pair)
      (smallQ f * controllerEnvironmentExchange * smallQ e) := by
    rw [StrictThermal.ceLift_mul, StrictThermal.ceLift_mul, ← Q_as_ceLift, ← Q_as_ceLift]
    rfl
  rw [transfer, ceLift_star, ← StrictThermal.ceLift_mul]

theorem flip_exchange_square_up :
    star (flip 1 loadInteraction 0) * flip 1 loadInteraction 0 =
      Matrix.diagonal (fun x : PairController × Fin 2 => if x.1.2 = 1 ∧ x.2 = 0 then 1 else 0) := by
  have small : star (smallQ 1 * controllerEnvironmentExchange * smallQ 0) *
      (smallQ 1 * controllerEnvironmentExchange * smallQ 0) =
      Matrix.diagonal (fun x : Fin 2 × Fin 2 => if x.1 = 1 ∧ x.2 = 0 then (1 : ℂ) else 0) := by
    ext ⟨c, e⟩ ⟨d, f⟩
    fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
      norm_num [smallQ, controllerEnvironmentExchange, Matrix.mul_apply, Matrix.star_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single_apply, Matrix.diagonal_apply]
  rw [flip_exchange_square, small, StrictThermal.ceLift_diagonal]

theorem flip_exchange_square_down :
    star (flip 0 loadInteraction 1) * flip 0 loadInteraction 1 =
      Matrix.diagonal (fun x : PairController × Fin 2 => if x.1.2 = 0 ∧ x.2 = 1 then 1 else 0) := by
  have small : star (smallQ 0 * controllerEnvironmentExchange * smallQ 1) *
      (smallQ 0 * controllerEnvironmentExchange * smallQ 1) =
      Matrix.diagonal (fun x : Fin 2 × Fin 2 => if x.1 = 0 ∧ x.2 = 1 then (1 : ℂ) else 0) := by
    ext ⟨c, e⟩ ⟨d, f⟩
    fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
      norm_num [smallQ, controllerEnvironmentExchange, Matrix.mul_apply, Matrix.star_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single_apply, Matrix.diagonal_apply]
  rw [flip_exchange_square, small, StrictThermal.ceLift_diagonal]

theorem leading_up (rho : Matrix PairController PairController ℂ) :
    Collision.energy (star (flip 1 loadInteraction 0) * flip 1 loadInteraction 0) (tagged rho 0) =
      ∑ p : Pair, (rho (p, 1) (p, 1)).re := by
  rw [flip_exchange_square_up]
  simp [Collision.energy, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, tagged,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Complex.re_sum]

theorem leading_down (rho : Matrix PairController PairController ℂ) :
    Collision.energy (star (flip 0 loadInteraction 1) * flip 0 loadInteraction 1) (tagged rho 1) =
      ∑ p : Pair, (rho (p, 0) (p, 0)).re := by
  rw [flip_exchange_square_down]
  simp [Collision.energy, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, tagged,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Complex.re_sum]

theorem leading_heat (rho : Matrix PairController PairController ℂ) (normalized : rho.trace = 1) :
    2 * (weight 0 * Collision.energy (star (flip 1 loadInteraction 0) * flip 1 loadInteraction 0) (tagged rho 0) -
      weight 1 * Collision.energy (star (flip 0 loadInteraction 1) * flip 0 loadInteraction 1) (tagged rho 1)) =
      controllerEnergy 2 rho - controllerEnergy 2 (Matrix.kronecker rho environmentState) := by
  have total := congrArg Complex.re normalized
  change (∑ i : Pair × Fin 2, rho i i).re = 1 at total
  rw [Fintype.sum_prod_type] at total
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib, Complex.add_re, Complex.re_sum] at total
  rw [leading_up, leading_down, environment_initial_energy rho normalized,
    controllerEnergy_eq_probability]
  unfold excitedProbability
  rw [show weight 0 = 1 - weight 1 by linarith [weights_sum]]
  rw [show (∑ p : Pair, (rho (p, 0) (p, 0)).re) =
      1 - ∑ p : Pair, (rho (p, 1) (p, 1)).re by linarith [total]]
  ring

/-- A local consumer: the actual source supplies the unitary approximation and incoming energy gap. -/
theorem environment_heat_lower_of_quarter_error
    (rho : Matrix PairController PairController ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) (U : Matrix.unitaryGroup (PairController × Fin 2) ℂ)
    (t : ℝ) (ht : 0 < t)
    (error : ‖(U : LoadedJoint) - 1 - t • (-Complex.I • loadInteraction)‖ ≤ t / 4)
    (imbalance : 11 / 8 < controllerEnergy 2 rho -
      controllerEnergy 2 (Matrix.kronecker rho environmentState)) :
    t ^ 2 / 4 < environmentEnergy
      (Unitary.conjStarAlgAut ℂ _ U (Matrix.kronecker rho environmentState)) -
        environmentEnergy (Matrix.kronecker rho environmentState) := by
  let pu := Collision.energy (star (flip 1 loadInteraction 0) * flip 1 loadInteraction 0) (tagged rho 0)
  let pd := Collision.energy (star (flip 0 loadInteraction 1) * flip 0 loadInteraction 1) (tagged rho 1)
  let xu := Collision.energy (Q 1) ((U : LoadedJoint) * tagged rho 0 * star (U : LoadedJoint))
  let xd := Collision.energy (Q 0) ((U : LoadedJoint) * tagged rho 1 * star (U : LoadedJoint))
  have upError := flip_probability_error rho positive normalized (U : LoadedJoint) loadInteraction t ht.le
    StrictThermal.loadInteraction_norm_le_one error 0 1 (by decide)
  have downError := flip_probability_error rho positive normalized (U : LoadedJoint) loadInteraction t ht.le
    StrictThermal.loadInteraction_norm_le_one error 1 0 (by decide)
  change |xu - t ^ 2 * pu| ≤ 9 * t ^ 2 / 16 at upError
  change |xd - t ^ 2 * pd| ≤ 9 * t ^ 2 / 16 at downError
  have up : t ^ 2 * pu - 9 * t ^ 2 / 16 ≤ xu := by linarith [(abs_le.mp upError).1]
  have down : xd ≤ t ^ 2 * pd + 9 * t ^ 2 / 16 := by linarith [(abs_le.mp downError).2]
  have weightedUp := mul_le_mul_of_nonneg_left up (weight_nonnegative 0)
  have weightedDown := mul_le_mul_of_nonneg_left down (weight_nonnegative 1)
  have leading : 2 * (weight 0 * pu - weight 1 * pd) =
      controllerEnergy 2 rho - controllerEnergy 2 (Matrix.kronecker rho environmentState) :=
    leading_heat rho normalized
  have lower : t ^ 2 * (controllerEnergy 2 rho - controllerEnergy 2 (Matrix.kronecker rho environmentState)) -
      9 * t ^ 2 / 8 ≤ environmentEnergy
        (Unitary.conjStarAlgAut ℂ _ U (Matrix.kronecker rho environmentState)) -
          environmentEnergy (Matrix.kronecker rho environmentState) := by
    change _ ≤ controllerEnergy 2 _ - controllerEnergy 2 _
    rw [net_environment_heat rho normalized U]
    change _ ≤ 2 * (weight 0 * xu - weight 1 * xd)
    calc
      _ = 2 * (weight 0 * (t ^ 2 * pu - 9 * t ^ 2 / 16) -
          weight 1 * (t ^ 2 * pd + 9 * t ^ 2 / 16)) := by
        rw [← leading, show weight 0 = 1 - weight 1 by linarith [weights_sum]]
        ring
      _ ≤ _ := by linarith
  have strict : t ^ 2 / 4 < t ^ 2 *
      (controllerEnergy 2 rho - controllerEnergy 2 (Matrix.kronecker rho environmentState)) - 9 * t ^ 2 / 8 := by
    have gap := mul_pos (sq_pos_of_pos ht) (sub_pos.mpr imbalance)
    nlinarith
  exact strict.trans_le lower

end

end LAlanine40K2025.Thermal.Load.Producer.HeatProbability
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
