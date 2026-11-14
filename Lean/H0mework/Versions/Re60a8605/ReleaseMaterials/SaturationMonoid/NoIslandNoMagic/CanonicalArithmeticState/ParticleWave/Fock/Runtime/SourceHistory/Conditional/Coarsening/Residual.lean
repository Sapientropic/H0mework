import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Conditional.Coarsening.Field

/-! The exact coarsening cost is read by the original actor K and field T, with both residuals retained. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePulseCoarsening

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceConditionalTransfer
open SourceWeightedRecovery MeasureTheory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance : UniformSpace (Field (process := process) pulse) := fieldUniform pulse
local instance : MeasurableSpace (Field (process := process) pulse) := fieldBorel pulse
local instance : BorelSpace (Field (process := process) pulse) := ⟨rfl⟩
local instance : T2Space (Field (process := process) pulse) := field_t2 pulse

theorem actor_cost (bound : Nat) :
    ‖Runtime.Actor.actorResidual pulse runtimeSeed bound (taskValue (historyPMF bound) (clockTask bound))‖ ^ 2 =
      (bound : ℝ) * (bound - 1) / 12 := by
  rw [Runtime.Actor.source_actor_minimum]
  apply le_antisymm
  · have same :
        (fun atom => Runtime.Actor.actorTransfer pulse runtimeSeed bound
          (taskValue (historyPMF bound) (clockTask bound)) atom) =
        optimalDecoder (historyPMF bound) (fieldSample pulse runtimeSeed bound) (clockTask bound) :=
      funext (Runtime.Actor.actorTransfer_is_conditional pulse runtimeSeed bound (clockTask bound))
    rw [same]
    exact (optimal_lower_bound _ _ _ (currentFieldDecoder bound)).trans_eq (field_decoder_attains bound)
  · exact current_field_lower_bound bound _

theorem total_cost (bound : Nat) :
    ‖Runtime.Actor.actorResidual pulse runtimeSeed bound (taskValue (historyPMF bound) (clockTask bound))‖ ^ 2 +
      ‖SourceGeneratedEmpiricalHilbert.residual pulse runtimeSeed bound
        (Runtime.Actor.actorTransfer pulse runtimeSeed bound (taskValue (historyPMF bound) (clockTask bound)))‖ ^ 2 =
      (bound : ℝ) * (bound + 2) / 12 := by
  apply le_antisymm
  · have lower := Runtime.Actor.rawError_lower_bound pulse runtimeSeed bound (clockTask bound)
      (fun _ => (((bound : ℝ) / 2 : ℝ) : ℂ))
    rw [next_field_error] at lower
    simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] using lower
  · have attained := Runtime.Actor.rawError_attains pulse runtimeSeed bound (clockTask bound)
    dsimp only at attained
    rw [next_field_error] at attained
    rw [← attained]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem field_cost (bound : Nat) :
    ‖SourceGeneratedEmpiricalHilbert.residual pulse runtimeSeed bound
      (Runtime.Actor.actorTransfer pulse runtimeSeed bound (taskValue (historyPMF bound) (clockTask bound)))‖ ^ 2 =
      (bound : ℝ) / 4 := by
  have total := total_cost bound
  rw [actor_cost] at total
  nlinarith

theorem old_residuals_reconstruct (bound : Nat) :
    type_of% (Runtime.Actor.reconstruct_actor pulse runtimeSeed bound
      (taskValue (historyPMF bound) (clockTask bound))) :=
  Runtime.Actor.reconstruct_actor pulse runtimeSeed bound (taskValue (historyPMF bound) (clockTask bound))

end
end SourcePulseCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
