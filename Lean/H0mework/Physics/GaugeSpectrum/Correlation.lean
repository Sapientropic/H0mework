import H0mework.Physics.GaugeSpectrum.Temporal

/-! The two-time connected response is calculated from the accepted actual,
its independent dual, and its exact source phase flow. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Kronecker

noncomputable section

theorem evaluation_spinDiagonal (point : BasePoint) (values : DiracSpinorIndex → ℂ) :
    State.evaluation point
      (diagonal values ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (values 0 + values 1 + values 2 + values 3) / 4 := by
  have up : star (upperPhase point) * upperPhase point = 1 :=
    Source.phase_star_mul frequency point
  have down : star (lowerPhase point) * lowerPhase point = 1 :=
    Source.phase_star_mul (-frequency) point
  calc
    _ = (star (upperPhase point) * upperPhase point) * (values 0 + values 1) / 4 +
        (star (lowerPhase point) * lowerPhase point) * (values 2 + values 3) / 4 := by
      simp [State.evaluation, State.vectorEvaluation, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two,
        Source.vector, Source.amplitude, spinPairCoefficients]
      ring
    _ = _ := by rw [up, down]; ring

theorem evolvedDualCurvature_mean (point displacement : BasePoint) (axis : Fin 3) :
    State.evaluation point (evolvedDualCurvature point displacement axis) = 0 := by
  rw [evolvedDualCurvature_normalForm, map_smul]
  suffices State.evaluation point (rotatedExchange displacement ⊗ₖ pauli axis) = 0 by simp [this]
  rw [pauli_explicit]
  fin_cases axis <;>
    simp +decide [State.evaluation, State.vectorEvaluation, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two,
      rotatedExchange, exchange, spinRate, Dynamics.rate,
      Source.vector, Source.amplitude, spinPairCoefficients]
  ring

theorem evolvedDualCurvature_hermitian (point displacement : BasePoint) (axis : Fin 3) :
    (evolvedDualCurvature point displacement axis).IsHermitian := by
  change star (evolvedDualCurvature point displacement axis) = _
  simp only [evolvedDualCurvature, star_mul,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    (dualCurvature_hermitian point axis).eq, Matrix.mul_assoc]

theorem temporal_connected_phase (point first second : BasePoint) (axis : Fin 3) :
    connected point (evolvedDualCurvature point first axis)
      (evolvedDualCurvature point second axis) =
      (curvatureScale : ℂ) ^ 2 *
        (phase (2 * frequency) (second - first) +
          phase (-(2 * frequency)) (second - first)) / 2 := by
  simp only [connected, Matrix.star_eq_conjTranspose,
    (evolvedDualCurvature_hermitian point first axis).eq, evolvedDualCurvature_mean,
    star_zero, mul_zero, sub_zero, evolvedDualCurvature_product, map_smul,
    evaluation_spinDiagonal, smul_eq_mul]
  simp only [spinRate, Dynamics.rate]
  norm_num
  ring

theorem phase_pair_cos (rate : ℝ) (point : BasePoint) :
    (phase rate point + phase (-rate) point) / 2 =
      (Real.cos (rate * point 0) : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  congr 2 <;> simp [phase] <;> congr 1 <;> ring

theorem temporal_connected_cos (point first second : BasePoint) (axis : Fin 3) :
    connected point (evolvedDualCurvature point first axis)
      (evolvedDualCurvature point second axis) =
      ((curvatureScale ^ 2 * Real.cos (2 * frequency * (second 0 - first 0)) : ℝ) : ℂ) := by
  rw [temporal_connected_phase, mul_div_assoc, phase_pair_cos]
  push_cast
  rw [PiLp.sub_apply]
  push_cast
  rfl

theorem temporal_connected_at_zero (point : BasePoint) (axis : Fin 3) :
    connected point (evolvedDualCurvature point 0 axis)
      (evolvedDualCurvature point 0 axis) = (curvatureScale : ℂ) ^ 2 := by
  rw [temporal_connected_phase]
  simp [phase_zero]
  ring

theorem temporal_connected_sign_reversal (point : BasePoint) (axis : Fin 3) :
    connected point (evolvedDualCurvature point 0 axis)
      (evolvedDualCurvature point (Dynamics.timeDisplacement (Real.pi / (2 * frequency))) axis) =
      -((curvatureScale : ℂ) ^ 2) := by
  rw [temporal_connected_cos]
  simp only [Dynamics.timeDisplacement_zero, PiLp.zero_apply, sub_zero]
  have nonzero : 2 * frequency ≠ 0 := ne_of_gt (mul_pos (by norm_num) Dynamics.frequency_positive)
  rw [mul_div_cancel₀ _ nonzero, Real.cos_pi]
  push_cast
  ring

theorem temporal_connected_nonconstant (point : BasePoint) (axis : Fin 3) :
    (fun displacement => connected point (evolvedDualCurvature point 0 axis)
        (evolvedDualCurvature point displacement axis)) ≠
      (fun _ => (curvatureScale : ℂ) ^ 2) := by
  intro same
  have reversed := congrFun same (Dynamics.timeDisplacement (Real.pi / (2 * frequency)))
  rw [temporal_connected_sign_reversal] at reversed
  have nonzero : (curvatureScale : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast ne_of_gt curvatureScale_pos)
  exact nonzero (by linear_combination -reversed / 2)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
