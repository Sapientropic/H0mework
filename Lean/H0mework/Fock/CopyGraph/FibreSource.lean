import H0mework.Fock.CopyGraph.LossObservation
import H0mework.Fock.CopyGraph.Projection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphFibreUpdate

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceGeneratedAtomicObservation SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead)
open SourceGraphBirth (fresh innovation)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
attribute [local instance] SourceConditionalGraphDecoder.imageComplete

def arrival (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) : SourceJointClockGraph.Carrier →L[ℂ] ℂ :=
  ((Real.sqrt (SourceHistoryGrowth.fraction depth (depth + 1)))⁻¹ : ℂ) •
    ((evalAtContinuous (observed (historyPMF depth) (oldRead depth read)) (read (depth + 1)) supported).comp
      (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read)))

def beta (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) : ℂ :=
  1 + arrival depth index read supported (fresh depth index)

def normal (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) : SourceJointClockGraph.Carrier :=
  (star (beta depth index read supported) / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovation depth index read -
    (arrival depth index read supported).adjoint 1

omit [MeasurableSingletonClass Observed] in
theorem old_decode_innovation (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) (innovation depth index read) = 0 :=
  SourceConditionalGraphDecoder.decode_residual depth depth index (oldRead depth read) (fresh depth index)

theorem arrival_innovation (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    arrival depth index read supported (innovation depth index read) = 0 := by
  change ((Real.sqrt (SourceHistoryGrowth.fraction depth (depth + 1)))⁻¹ : ℂ) •
    (evalAtContinuous (observed (historyPMF depth) (oldRead depth read)) (read (depth + 1)) supported)
      (SourceConditionalGraphDecoder.decode depth depth index (oldRead depth read) (innovation depth index read)) = 0
  rw [old_decode_innovation, map_zero, smul_zero]

omit [MeasurableSingletonClass Observed] in
theorem innovation_fresh_pairing (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    inner ℂ (innovation depth index read) (fresh depth index) = ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ) := by
  have original := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read) (fresh depth index)
  have paired := congrArg (inner ℂ (innovation depth index read)) original
  rw [inner_add_right, SourceGraphBirth.innovation_old_orthogonal, zero_add] at paired
  change inner ℂ (innovation depth index read) (innovation depth index read) =
    inner ℂ (innovation depth index read) (fresh depth index) at paired
  rw [inner_self_eq_norm_sq_to_K] at paired
  rw [Complex.ofReal_pow]
  with_unfolding_all exact paired.symm

theorem normal_pairing (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support)
    (value : SourceJointClockGraph.Carrier) :
    inner ℂ (normal depth index read supported) value =
      beta depth index read supported / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ) * inner ℂ (innovation depth index read) value -
        arrival depth index read supported value := by
  rw [normal, inner_sub_left, inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  simp only [map_div₀, Complex.conj_ofReal, RCLike.inner_apply, map_one, mul_one]
  change star (star (beta depth index read supported)) / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ) *
    inner ℂ (innovation depth index read) value - arrival depth index read supported value = _
  rw [star_star]

theorem normal_fresh_pairing (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    inner ℂ (normal depth index read supported) (fresh depth index) = 1 := by
  rw [normal_pairing, innovation_fresh_pairing, div_mul_cancel₀ _ (SourceGraphBirth.denominator_ne_zero depth index read), beta]
  ring

theorem normal_ne_zero (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support) :
    normal depth index read supported ≠ 0 := by
  intro zero
  have source := normal_fresh_pairing depth index read supported
  rw [zero, inner_zero_left] at source
  exact zero_ne_one source

end
end SourceGraphFibreUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
