import H0mework.Physics.GaugeSpectrum.Connected
import H0mework.Physics.QuantumDynamics.TimeJet
import H0mework.Physics.QuantumDynamics.Coherence

/-! The temporal action is exactly the original source phase flow. Curvature
alone is static; the original dual's exchange carries its nonzero frequency. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Kronecker

noncomputable section

def spinRate (spin : DiracSpinorIndex) : ℝ := Dynamics.rate (spin, 0)

def clockMatrix (point : BasePoint) : Matrix DiracSpinorIndex DiracSpinorIndex ℂ :=
  diagonal (fun spin => phase (spinRate spin) point)

theorem source_clock (point : BasePoint) :
    (Dynamics.unitary point : State.Observable) = clockMatrix point ⊗ₖ 1 := by
  ext ⟨spin, color⟩ ⟨other, input⟩
  simp [Dynamics.unitary_matrix, clockMatrix, Dynamics.phaseCoefficient, spinRate,
    Dynamics.rate, Matrix.diagonal_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem spinRate_flip (spin : DiracSpinorIndex) : spinRate (spinFlip spin) = -spinRate spin := by
  fin_cases spin <;> simp [spinRate, spinFlip, Dynamics.rate]

theorem phase_rate_add (first second : ℝ) (point : BasePoint) :
    phase (first + second) point = phase first point * phase second point := by
  simp [phase, add_mul, mul_add, Complex.exp_add]

def rotatedExchange (point : BasePoint) : Matrix DiracSpinorIndex DiracSpinorIndex ℂ :=
  diagonal (fun spin => phase (-2 * spinRate spin) point) * exchange

theorem rotatedExchange_eq (point : BasePoint) :
    rotatedExchange point = star (clockMatrix point) * exchange * clockMatrix point := by
  ext row column
  simp only [rotatedExchange, clockMatrix, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    exchange, Pi.star_apply, Source.phase_star]
  by_cases same : spinFlip row = column
  · subst column
    simp only [ite_true, mul_one, spinRate_flip]
    rw [← phase_rate_add]
    congr 2
    ring
  · simp [same]

def evolvedDualCurvature (point displacement : BasePoint) (axis : Fin 3) : State.Observable :=
  star (Dynamics.unitary displacement : State.Observable) * dualCurvature point axis *
    (Dynamics.unitary displacement : State.Observable)

theorem evolvedDualCurvature_normalForm (point displacement : BasePoint) (axis : Fin 3) :
    evolvedDualCurvature point displacement axis =
      (curvatureScale : ℂ) • (rotatedExchange displacement ⊗ₖ pauli axis) := by
  simp only [evolvedDualCurvature, dualCurvature_normalForm, source_clock,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, rotatedExchange_eq]

theorem curvature_commutes_clock (point displacement : BasePoint) (axis : Fin 3) :
    curvature point axis * (Dynamics.unitary displacement : State.Observable) =
      (Dynamics.unitary displacement : State.Observable) * curvature point axis := by
  simp only [curvature_normalForm, source_clock, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem curvature_stationary (point displacement : BasePoint) (axis : Fin 3) :
    star (Dynamics.unitary displacement : State.Observable) * curvature point axis *
      (Dynamics.unitary displacement : State.Observable) = curvature point axis := by
  rw [Matrix.mul_assoc, curvature_commutes_clock, ← Matrix.mul_assoc]
  rw [Matrix.mem_unitaryGroup_iff'.mp (Dynamics.unitary displacement).property, Matrix.one_mul]

theorem rotatedExchange_product (first second : BasePoint) :
    rotatedExchange first * rotatedExchange second =
      diagonal (fun spin => phase (2 * spinRate spin) (second - first)) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp +decide [rotatedExchange, exchange, spinFlip, spinRate, Dynamics.rate,
      Matrix.mul_apply, Fin.sum_univ_four]
  all_goals
    simp only [phase, PiLp.sub_apply, Complex.ofReal_sub, ← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem evolvedDualCurvature_product (point first second : BasePoint) (axis : Fin 3) :
    evolvedDualCurvature point first axis * evolvedDualCurvature point second axis =
      ((curvatureScale : ℂ) ^ 2) •
        (diagonal (fun spin => phase (2 * spinRate spin) (second - first)) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [evolvedDualCurvature_normalForm, evolvedDualCurvature_normalForm,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_kronecker_mul,
    rotatedExchange_product, pauli_square, ← pow_two]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
