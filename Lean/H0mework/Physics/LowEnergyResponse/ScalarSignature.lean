import H0mework.Physics.LowEnergyResponse.ScalarGauge

/-! Native temporal sign and exact scalar kinetic normalization.
These statements read the ORIGINAL (-,+,+,+) metric and +kinetic-minus-potential
convention. No stable Klein--Gordon sign is substituted by convention. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Response.ScalarSignature
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
noncomputable section

theorem actual_metric (point : BasePoint) :
    lorentzianMetricOfCoframe (actual.coframe point) =
      Matrix.diagonal ![-lapse^2, 1, 1, 1] := by
  rw [actual_coframe]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [lorentzianMetricOfCoframe, homogeneousCoframe, minkowskiInternalMetric,
      Matrix.mul_apply, Matrix.diagonal_apply]
  ring

theorem actual_metric_inverse (point : BasePoint) :
    (lorentzianMetricOfCoframe (actual.coframe point))⁻¹ =
      Matrix.diagonal ![-(lapse^2)⁻¹, 1, 1, 1] := by
  apply Matrix.inv_eq_left_inv
  rw [actual_metric, Matrix.diagonal_mul_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [ne_of_gt lapse_pos]

/-- The temporal kinetic coefficient is NEGATIVE in the stored source action. -/
theorem temporal_kinetic (point : BasePoint) (value : ScalarCoordinateCarrier) :
    ScalarGauge.kineticPair point (fun direction => if direction = 0 then value else 0)
      (fun direction => if direction = 0 then value else 0) =
      -scalarCoordinateSquaredNorm value / (2 * lapse^2) := by
  have pairing : scalarCoordinatePairingRe value value = scalarCoordinateSquaredNorm value :=
    scalarCoordinateRealPairing_self value
  simp [ScalarGauge.kineticPair, actual_metric_inverse, Matrix.diagonal_apply,
    Fin.sum_univ_four, scalarCoordinatePairingRe, scalarCoordinateSquaredNorm,
    Complex.normSq_apply] at pairing ⊢
  ring

/-- The sign is nonvacuous on every nonzero scalar tangent. -/
theorem temporal_kinetic_negative (point : BasePoint) (value : ScalarCoordinateCarrier)
    (nonzero : value ≠ 0) :
    ScalarGauge.kineticPair point (fun direction => if direction = 0 then value else 0)
      (fun direction => if direction = 0 then value else 0) < 0 := by
  rw [temporal_kinetic]
  have normPositive : 0 < scalarCoordinateSquaredNorm value :=
    lt_of_le_of_ne (scalarCoordinateSquaredNorm_nonneg value)
      (fun zero => nonzero ((scalarCoordinateSquaredNorm_eq_zero_iff value).mp zero.symm))
  exact div_neg_of_neg_of_pos (neg_neg_of_pos normPositive) (mul_pos (by norm_num) (sq_pos_of_pos lapse_pos))

end
end SaturationMonoid.PhysicsCore.LowEnergy.Response.ScalarSignature
