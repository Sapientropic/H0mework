import H0mework.Fock.CopyGraph.FibreDual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphFibreUpdate

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead)
open SourceGraphBirth (fresh)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem normal_loss_formula (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    SourceGraphGrowth.forgettingLoss depth index read value =
      (inner ℂ (normal depth index read supported) value / ((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)) • normal depth index read supported := by
  let c := SourceGraphLoss.coefficient depth index read (normal depth index read supported)
  have relation : normal depth index read supported = c • SourceGraphLoss.direction depth index read :=
    (normal_fixed_loss depth index read supported).symm.trans (SourceGraphLoss.loss_direction depth index read _)
  have nonzero : c ≠ 0 := by
    intro zero
    have vanished := relation
    rw [zero, zero_smul] at vanished
    exact normal_ne_zero depth index read supported vanished
  have restored : SourceGraphLoss.direction depth index read = c⁻¹ • normal depth index read supported := by
    have scaled := congrArg (fun vector : SourceJointClockGraph.Carrier => c⁻¹ • vector) relation
    rw [smul_smul, inv_mul_cancel₀ nonzero, one_smul] at scaled
    exact scaled.symm
  have expanded : SourceGraphGrowth.forgettingLoss depth index read value =
      (SourceGraphLoss.coefficient depth index read value * c⁻¹) • normal depth index read supported := by
    have original := SourceGraphLoss.loss_direction depth index read value
    rw [restored, smul_smul] at original
    exact original
  have generated := SourceConditionalGraphDecoder.reconstruction (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value
  have paired := congrArg (inner ℂ (normal depth index read supported)) generated
  rw [inner_add_right, normal_raw_orthogonal, zero_add] at paired
  change inner ℂ (normal depth index read supported) (SourceGraphGrowth.newResidual depth index read value) =
    inner ℂ (normal depth index read supported) value at paired
  rw [SourceGraphGrowth.forgetting_residual, inner_add_right, normal_tagged_orthogonal, zero_add,
    expanded, inner_smul_right, inner_self_eq_norm_sq_to_K] at paired
  rw [expanded]
  apply congrArg (fun scalar : ℂ => scalar • normal depth index read supported)
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (normal_ne_zero depth index read supported))))).mpr
  rw [Complex.ofReal_pow]
  with_unfolding_all exact paired

theorem direction_formula (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    SourceGraphLoss.direction depth index read =
      (((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)⁻¹) • normal depth index read supported := by
  have original := normal_loss_formula depth index read supported (fresh depth index)
  rw [SourceGraphLoss.fresh_loss, normal_fresh_pairing, one_div] at original
  exact original

theorem direction_cost (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    ‖SourceGraphLoss.direction depth index read‖ ^ 2 = 1 / ‖normal depth index read supported‖ ^ 2 := by
  rw [direction_formula depth index read supported, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow, inv_pow]
  field_simp [norm_ne_zero_iff.mpr (normal_ne_zero depth index read supported)]

end
end SourceGraphFibreUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
