import H0mework.Fock.CopyGraph.ConditionalClock
import H0mework.Fock.CopyGraph.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index scale)
open SourceGeneratedJointClock
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def copyRead (depth bound : Nat) (index : Index depth) : Space (historyPMF bound) →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (SourceCopyGraph.action depth index).toLinearMap.comp (SourceJointClockGraph.read.comp (SourceHistoryWord.word bound))

theorem copy_read_energy (depth bound : Nat) (index : Index depth) (value : Space (historyPMF bound)) :
    ‖copyRead depth bound index value‖ ^ 2 = ‖value‖ ^ 2 +
      ‖SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound value)‖ ^ 2 +
      (scale depth index : ℝ) ^ 2 * ‖SourceClockComplex.clock (SourceHistoryWord.word bound value)‖ ^ 2 := by
  change ‖SourceCopyGraph.action depth index (SourceJointClockGraph.read (SourceHistoryWord.word bound value))‖ ^ 2 = _
  rw [SourceCopyGraph.action_energy, SourceJointClockGraph.norm_sq,
    SourceJointClockGraph.joint_source, SourceJointClockGraph.clock_source,
    SourceMassCompletion.jointRead_apply, WithLp.prod_norm_sq_eq_of_L2]
  change (‖SourceSuccessorBoundary.readWord (SourceHistoryWord.word bound value)‖ ^ 2 +
    ‖SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound value)‖ ^ 2) + _ + _ = _
  rw [SourceHistoryWord.hilbert_norm_sq]
  ring

theorem residual_graph_energy (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖copyRead depth bound index (residual (historyPMF bound) observer value)‖ ^ 2 =
      ‖residual (historyPMF bound) observer value‖ ^ 2 +
        (scale depth index : ℝ) ^ 2 *
          ‖SourceClockComplex.clock (SourceHistoryWord.word bound (residual (historyPMF bound) observer value))‖ ^ 2 := by
  rw [copy_read_energy, residual_mass, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem residual_graph_bound (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖copyRead depth bound index (residual (historyPMF bound) observer value)‖ ^ 2 ≤
      (1 + (scale depth index : ℝ) ^ 2 * (bound + 1 : ℝ) *
        ‖residual (historyPMF bound) observer (taskValue (historyPMF bound) (signal bound))‖ ^ 2) *
          ‖residual (historyPMF bound) observer value‖ ^ 2 := by
  rw [residual_graph_energy]
  have paid := mul_le_mul_of_nonneg_left (residual_clock_bound bound observer value)
    (sq_nonneg (scale depth index : ℝ))
  nlinarith only [paid]

theorem compression_graph_error (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖copyRead depth bound index value - copyRead depth bound index
      (pullback (historyPMF bound) observer (transfer (historyPMF bound) observer value))‖ ^ 2 =
        ‖residual (historyPMF bound) observer value‖ ^ 2 + (scale depth index : ℝ) ^ 2 *
          ‖SourceClockComplex.clock (SourceHistoryWord.word bound (residual (historyPMF bound) observer value))‖ ^ 2 := by
  rw [← map_sub]
  exact residual_graph_energy depth bound index observer value

end
end SourceConditionalGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
