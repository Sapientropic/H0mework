import H0mework.Fock.CopyGraph.FibreFibre

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphFibreUpdate

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead taggedRead oldAction taggedAction)
open SourceGraphBirth (fresh innovation)
open SourceConditionalGraphDecoder (decode residual)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem arrival_residual (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    arrival depth index read supported (residual depth depth index (oldRead depth read) value) = 0 := by
  change ((Real.sqrt (SourceHistoryGrowth.fraction depth (depth + 1)))⁻¹ : ℂ) •
    (SourceGeneratedAtomicObservation.evalAtContinuous (observed (historyPMF depth) (oldRead depth read)) (read (depth + 1)) supported)
      (decode depth depth index (oldRead depth read) (residual depth depth index (oldRead depth read) value)) = 0
  rw [SourceConditionalGraphDecoder.decode_residual, map_zero, smul_zero]

theorem dual_residual_zero (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    residual depth depth index (oldRead depth read) ((arrival depth index read supported).adjoint 1) = 0 := by
  let dual := (arrival depth index read supported).adjoint 1
  let remaining := residual depth depth index (oldRead depth read) dual
  have orthogonal : inner ℂ dual remaining = 0 := by
    rw [ContinuousLinearMap.adjoint_inner_left, arrival_residual, inner_zero_right]
  have source := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read) dual
  have paired := congrArg (fun value : SourceJointClockGraph.Carrier => inner ℂ value remaining) source
  rw [inner_add_left, SourceConditionalGraphDecoder.source_orthogonal, zero_add, orthogonal] at paired
  exact inner_self_eq_zero.mp paired

theorem dual_source (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    oldAction depth index read (decode depth depth index (oldRead depth read) ((arrival depth index read supported).adjoint 1)) =
      (arrival depth index read supported).adjoint 1 := by
  have original := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read) ((arrival depth index read supported).adjoint 1)
  rw [dual_residual_zero, add_zero] at original
  exact original

def normalObserved (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    Space (observed (historyPMF (depth + 1)) (taggedRead depth read)) :=
  (star (beta depth index read supported) / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • SourceGraphBirth.innovationObserved depth index read -
    SourceGraphGrowth.retainedLift depth read (decode depth depth index (oldRead depth read) ((arrival depth index read supported).adjoint 1))

theorem normal_observed_source (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    taggedAction depth index read (normalObserved depth index read supported) = normal depth index read supported := by
  rw [normalObserved, map_sub, map_smul, SourceGraphBirth.innovation_observed_source, SourceGraphGrowth.retained_action, dual_source]
  rfl

theorem normal_tagged_orthogonal (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    inner ℂ (normal depth index read supported) (SourceGraphGrowth.taggedResidual depth index read value) = 0 := by
  have original := SourceConditionalGraphDecoder.source_orthogonal (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (taggedRead depth read) value (normalObserved depth index read supported)
  rw [normal_observed_source] at original
  exact original

theorem normal_raw_residual (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    SourceGraphGrowth.newResidual depth index read (normal depth index read supported) = normal depth index read supported :=
  SourceConditionalGraphDecoder.residual_of_source_orthogonal (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (newRead depth read) (normal depth index read supported)
    (fun value => inner_eq_zero_symm.mp (normal_raw_orthogonal depth index read supported value))

theorem normal_fixed_loss (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    SourceGraphGrowth.forgettingLoss depth index read (normal depth index read supported) = normal depth index read supported := by
  have decoded := congrArg (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read))
    (normal_observed_source depth index read supported)
  rw [SourceConditionalGraphDecoder.decode_action] at decoded
  have original := SourceGraphLoss.loss_via_raw_residual depth index read (normal depth index read supported)
  rw [← decoded, normal_observed_source, normal_raw_residual] at original
  exact original

end
end SourceGraphFibreUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
