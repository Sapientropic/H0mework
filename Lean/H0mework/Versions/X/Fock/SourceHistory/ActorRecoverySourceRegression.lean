import H0mework.Probability.EmpiricalRecovery.ActorConditional
import H0mework.Versions.X.Checks.Probability.EmpiricalSource

/-! Three actual original actors retain different source clocks behind a shared current observation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.Pulse

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedEmpiricalHilbert.Controls SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def clockTask (index : Fin 3) : ℂ := (sample runtimeSeed 2 index : Nat)

theorem clockTask_source (index : Fin 3) : clockTask index = (index.val : ℂ) :=
  congrArg (fun state : Nat => (state : ℂ)) (runtimeAt_state index.val)

theorem current_sample (index : Fin 3) :
    fieldSample pulse runtimeSeed 2 index = fieldPoint pulse index.val :=
  congrArg (fieldPoint pulse) (runtimeAt_state index.val)

theorem current_fibre (index : Fin 3) :
    fieldSample pulse runtimeSeed 2 index = if index = 0 then fieldPoint pulse 0 else fieldPoint pulse 1 := by
  rw [current_sample]
  fin_cases index
  · rfl
  · rfl
  · exact point_successors_equal 1 0

theorem next_sample (index : Fin 3) : nextAtom pulse runtimeSeed 2 index = fieldPoint pulse 1 :=
  (fieldPoint_action pulse (sample runtimeSeed 2 index)).trans
    ((congrArg (fun state : Nat => fieldPoint pulse (state + 1)) (runtimeAt_state index.val)).trans
      (point_successors_equal index.val 0))

theorem clock_not_field_task :
    ¬ ∃ value : SourceGeneratedEmpiricalHilbert.Space pulse runtimeSeed 2,
      ∀ index : Fin 3, value (fieldSample pulse runtimeSeed 2 index) = clockTask index := by
  rintro ⟨value, expresses⟩
  have same : fieldSample pulse runtimeSeed 2 1 = fieldSample pulse runtimeSeed 2 2 :=
    (current_fibre 1).trans (current_fibre 2).symm
  have clocks := (expresses 1).symm.trans ((congrArg value same).trans (expresses 2))
  rw [clockTask_source, clockTask_source] at clocks
  norm_num at clocks

end
end SourceWeightedRecovery.Runtime.Actor.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
