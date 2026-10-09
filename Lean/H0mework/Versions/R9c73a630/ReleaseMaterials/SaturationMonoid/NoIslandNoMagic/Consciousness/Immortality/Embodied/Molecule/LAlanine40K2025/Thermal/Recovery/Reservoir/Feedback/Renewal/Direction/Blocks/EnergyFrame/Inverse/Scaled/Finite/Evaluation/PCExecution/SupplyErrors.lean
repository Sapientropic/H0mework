import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.BaseErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision Propagation.Producer
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem shared_pc_error : ‖Supply.sharedPCPolynomial-sharedPC‖ ≤ (2/10^23 : ℝ) :=
  (tensor_change Phase.pcPolynomial Primitive.computedPC Phase.pcPolynomial Primitive.computedPC).trans
    ((add_le_add (mul_le_mul Primitive.original_computed_PC original_pc_norm (norm_nonneg _) (by norm_num))
      (mul_le_mul computed_pc_norm Primitive.original_computed_PC (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem native_exchange_norm : ‖Supply.nativeExchangePolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm (Exchange.exchangeUnitary (Native.sourceCoupling*(nativeClockStep : ℝ)))
    Supply.nativeExchangePolynomial _ Supply.native_exchange_polynomial_error).trans (by norm_num)

theorem weak_exchange_norm : ‖Supply.weakExchangePolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm (Exchange.exchangeUnitary (nativeClockStep : ℝ))
    Supply.weakExchangePolynomial _ Supply.weak_exchange_polynomial_error).trans (by norm_num)

theorem supply_error : ‖Supply.fullSupplyPolynomial-supply‖ ≤ (8/10^23 : ℝ) := by
  have pair : ‖Supply.sharedPCPolynomial*Supply.nativeExchangePolynomial-sharedPC*Supply.nativeExchangePolynomial‖ ≤ (4/10^23 : ℝ) := by
    rw [← Matrix.sub_mul]
    exact (norm_mul_le (Supply.sharedPCPolynomial-sharedPC) Supply.nativeExchangePolynomial).trans ((mul_le_mul shared_pc_error native_exchange_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  exact (tensor_left_change _ _ Phase.environmentPolynomial).trans
    ((mul_le_mul pair original_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem weak_error : ‖Post.fullWeakPolynomial-weak‖ ≤ (8/10^23 : ℝ) := by
  have pair : ‖Supply.sharedPCPolynomial*Supply.weakExchangePolynomial-sharedPC*Supply.weakExchangePolynomial‖ ≤ (4/10^23 : ℝ) := by
    rw [← Matrix.sub_mul]
    exact (norm_mul_le (Supply.sharedPCPolynomial-sharedPC) Supply.weakExchangePolynomial).trans ((mul_le_mul shared_pc_error weak_exchange_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  exact (tensor_left_change _ _ Phase.environmentPolynomial).trans
    ((mul_le_mul pair original_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem supply_norm : ‖supply‖ ≤ 3 :=
  (close_norm _ _ _ _ Post.finite_full_supply_norm supply_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
