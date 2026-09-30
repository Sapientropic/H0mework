import H0mework.Versions.X.Fock.CopyGraph.RefinementRecovery
import H0mework.Versions.X.Fock.CopyGraph.CostObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyObservation (before after joint twoMaterial)
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
noncomputable section
local instance jointParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem joint_residual_update (depth bound : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    SourceConditionalGraphDecoder.residual depth bound index (before depth bound) value =
      SourceConditionalGraphDecoder.residual depth bound index (joint depth bound index) value +
        gain depth bound index (joint depth bound index) Prod.fst value := by
  simpa only [SourceCopyObservation.joint_before] using residual_update depth bound index (joint depth bound index) Prod.fst value

theorem joint_cost_gain (depth bound : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    ‖SourceConditionalGraphDecoder.residual depth bound index (before depth bound) value‖ ^ 2 =
      ‖SourceConditionalGraphDecoder.residual depth bound index (joint depth bound index) value‖ ^ 2 +
        ‖gain depth bound index (joint depth bound index) Prod.fst value‖ ^ 2 := by
  simpa only [SourceCopyObservation.joint_before] using residual_energy depth bound index (joint depth bound index) Prod.fst value

theorem actual_joint_residual_zero (value : Space (historyPMF 3)) :
    SourceConditionalGraphDecoder.residual 3 3 twoMaterial (joint 3 3 twoMaterial)
      (SourceConditionalGraph.copyRead 3 3 twoMaterial value) = 0 := by
  have paid := cost_decreases 3 3 twoMaterial (joint 3 3 twoMaterial) Prod.snd
    (SourceConditionalGraph.copyRead 3 3 twoMaterial value)
  rw [SourceCopyObservation.joint_after, SourceConditionalGraphDecoder.after_minimum_zero,
    norm_zero, zero_pow (by decide : 2 ≠ 0)] at paid
  apply norm_eq_zero.mp
  nlinarith only [paid, norm_nonneg (SourceConditionalGraphDecoder.residual 3 3 twoMaterial (joint 3 3 twoMaterial)
    (SourceConditionalGraph.copyRead 3 3 twoMaterial value))]

theorem actual_joint_gain (value : Space (historyPMF 3)) :
    ‖gain 3 3 twoMaterial (joint 3 3 twoMaterial) Prod.fst (SourceConditionalGraph.copyRead 3 3 twoMaterial value)‖ ^ 2 =
      ‖SourceConditionalGraphDecoder.residual 3 3 twoMaterial (before 3 3)
        (SourceConditionalGraph.copyRead 3 3 twoMaterial value)‖ ^ 2 := by
  have paid := joint_cost_gain 3 3 twoMaterial (SourceConditionalGraph.copyRead 3 3 twoMaterial value)
  rw [actual_joint_residual_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at paid
  exact paid.symm

theorem actual_clock_gain_positive :
    0 < ‖gain 3 3 twoMaterial (joint 3 3 twoMaterial) Prod.fst (SourceConditionalGraph.copyRead 3 3 twoMaterial
      (taskValue (historyPMF 3) (SourceGeneratedJointClock.signal 3)))‖ ^ 2 := by
  rw [actual_joint_gain]
  with_reducible exact SourceConditionalGraphDecoder.before_minimum_positive

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
