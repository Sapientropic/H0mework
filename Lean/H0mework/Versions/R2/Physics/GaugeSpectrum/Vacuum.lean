import H0mework.Versions.R2.Physics.GaugeSpectrum.Cubic
import H0mework.Versions.R2.Physics.QuantumDynamics.Automorphism

/-! The trace-prepared bottom eigenspace and the source cubic composite
produce a positive-energy Wightman atom. This vacuum belongs to the finite
source phase Hamiltonian. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation MeasureTheory
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Kronecker

noncomputable section

def evolvedCubic (point displacement : BasePoint) : State.Observable :=
  star (Dynamics.unitary displacement : State.Observable) * cubic point *
    (Dynamics.unitary displacement : State.Observable)

theorem evolvedCubic_from_evolved_curvature (point displacement : BasePoint) :
    evolvedCubic point displacement = orientedCubic (evolvedDualCurvature point displacement) := by
  have action_eq (observable : State.Observable) :
      Dynamics.automorphism (-displacement) observable =
        star (Dynamics.unitary displacement : State.Observable) * observable *
          (Dynamics.unitary displacement : State.Observable) := by
    rw [Dynamics.automorphism_apply, Dynamics.unitary_neg]
    simp only [Unitary.coe_star, star_star]
  calc
    _ = Dynamics.automorphism (-displacement) (cubic point) := (action_eq _).symm
    _ = orientedCubic (fun axis => Dynamics.automorphism (-displacement) (dualCurvature point axis)) := by
      simp only [cubic, orientedCubic, map_smul, map_add, map_sub, map_mul]
    _ = _ := by
      congr 1
      funext axis
      exact action_eq (dualCurvature point axis)

theorem groundDensity_stationary (displacement : BasePoint) :
    star (Dynamics.unitary displacement : State.Observable) * groundDensity *
      (Dynamics.unitary displacement : State.Observable) = groundDensity := by
  have commute : groundProjector * (Dynamics.unitary displacement : State.Observable) =
      (Dynamics.unitary displacement : State.Observable) * groundProjector := by
    rw [groundProjector_normalForm, Dynamics.unitary_matrix,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext index
    exact mul_comm _ _
  rw [groundDensity_normalForm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    commute, ← Matrix.mul_assoc,
    Matrix.mem_unitaryGroup_iff'.mp (Dynamics.unitary displacement).property, Matrix.one_mul]

theorem evolvedCubic_normalForm (point displacement : BasePoint) :
    evolvedCubic point displacement =
      ((curvatureScale : ℂ) ^ 3) • (rotatedExchange displacement ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  simp only [evolvedCubic, cubic_normalForm, source_clock,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, rotatedExchange_eq]

theorem cubic_ground_excitation (point : BasePoint) :
    phaseHamiltonian * (cubic point * groundProjector) =
      (frequency : ℂ) • (cubic point * groundProjector) := by
  rw [cubic_normalForm, groundProjector_normalForm, phaseHamiltonian]
  ext ⟨spin, color⟩ ⟨other, input⟩
  fin_cases spin <;> fin_cases other <;>
    simp +decide [Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.kroneckerMap_apply, exchange, spinFlip, Dynamics.rate]

theorem cubic_positive_gap (point : BasePoint) :
    (phaseHamiltonian + (frequency : ℂ) • 1) * (cubic point * groundProjector) =
      (spectralFrequency : ℂ) • (cubic point * groundProjector) := by
  rw [Matrix.add_mul, cubic_ground_excitation, Matrix.smul_mul, Matrix.one_mul]
  simp only [spectralFrequency, Complex.ofReal_mul, Complex.ofReal_ofNat]
  module

theorem cubic_excitation_nonzero (point : BasePoint) : cubic point * groundProjector ≠ 0 := by
  intro zero
  have value := congrArg (fun matrix : State.Observable => matrix (2, 0) (0, 0)) zero
  simp [cubic_normalForm, groundProjector_normalForm, Matrix.mul_diagonal,
    exchange, spinFlip] at value
  exact (ne_of_gt curvatureScale_pos) value

theorem evolvedCubic_product (point first second : BasePoint) :
    evolvedCubic point first * evolvedCubic point second =
      ((curvatureScale : ℂ) ^ 6) •
        (diagonal (fun spin => phase (2 * spinRate spin) (second - first)) ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [evolvedCubic_normalForm, evolvedCubic_normalForm, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← Matrix.mul_kronecker_mul, rotatedExchange_product, Matrix.one_mul]
  congr 1
  ring

theorem evolvedCubic_hermitian (point displacement : BasePoint) :
    (evolvedCubic point displacement).IsHermitian := by
  change star (evolvedCubic point displacement) = _
  simp only [evolvedCubic, star_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, (cubic_hermitian point).eq, Matrix.mul_assoc]

theorem evolvedCubic_ground_mean (point displacement : BasePoint) :
    groundEvaluation (evolvedCubic point displacement) = 0 := by
  rw [groundEvaluation_diagonal, evolvedCubic_normalForm]
  simp [rotatedExchange, Matrix.diagonal_mul, exchange, spinFlip]

def vacuumConnected (first second : State.Observable) : ℂ :=
  groundEvaluation (star first * second) - star (groundEvaluation first) * groundEvaluation second

theorem vacuumConnected_phase (point first second : BasePoint) :
    vacuumConnected (evolvedCubic point first) (evolvedCubic point second) =
      (curvatureScale : ℂ) ^ 6 * phase spectralFrequency (second - first) := by
  simp only [vacuumConnected, Matrix.star_eq_conjTranspose,
    (evolvedCubic_hermitian point first).eq, evolvedCubic_ground_mean, star_zero, mul_zero,
    sub_zero, evolvedCubic_product, map_smul]
  rw [groundEvaluation_diagonal]
  simp [spinRate, Dynamics.rate, spectralFrequency]
  left
  ring

def vacuumSpectralMeasure : Measure ℝ :=
  ENNReal.ofReal (curvatureScale ^ 6) • Measure.dirac spectralFrequency

theorem vacuumConnected_spectralIntegral (point first second : BasePoint) :
    vacuumConnected (evolvedCubic point first) (evolvedCubic point second) =
      ∫ rate : ℝ, phase rate (second - first) ∂vacuumSpectralMeasure := by
  rw [vacuumConnected_phase, vacuumSpectralMeasure, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (le_of_lt (pow_pos curvatureScale_pos 6)), Complex.real_smul,
    Complex.ofReal_pow]

theorem vacuumSpectralMeasure_exact_atom :
    vacuumSpectralMeasure {spectralFrequency} = ENNReal.ofReal (curvatureScale ^ 6) := by
  simp [vacuumSpectralMeasure]

theorem vacuumSpectralMeasure_atom_nonzero : vacuumSpectralMeasure {spectralFrequency} ≠ 0 := by
  rw [vacuumSpectralMeasure_exact_atom]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos curvatureScale_pos 6))

theorem vacuumSpectralMeasure_outside : vacuumSpectralMeasure {spectralFrequency}ᶜ = 0 := by
  simp [vacuumSpectralMeasure]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
