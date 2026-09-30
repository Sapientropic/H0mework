import H0mework.Versions.X.Fock.CopyGraph.SharedNextSourceStepData

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeSharedUpdate

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead realize retained)
open SourceCopyTimeModel (time)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem step_realize (runtime : LivingRuntimeState process) (previous : Coordinates runtime (maximumIndex runtime) 0) :
    realize runtime.tick.next (maximumIndex runtime.tick.next) 0 (step runtime previous) =
      SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0 previous) := by
  have old : retained runtime (maximumIndex runtime) 0 (realize runtime (maximumIndex runtime) 0 previous) =
      realize runtime (maximumIndex runtime) 0 previous := by
    simp only [retained, LinearMap.comp_apply, SourceCopyCurrentCoordinates.realize_source]
  have tail := SourceCopySharedNext.old_time_retained_tail_zero runtime (realize runtime (maximumIndex runtime) 0 previous)
  rw [old] at tail
  have source := SourceCopyCurrentCoordinates.reconstruction runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0 previous))
  rw [tail, add_zero] at source
  exact source

theorem trajectory_zero (runtime : LivingRuntimeState process) (initial : Coordinates runtime (maximumIndex runtime) 0) :
    trajectory runtime initial 0 = initial :=
  SourceCopyCurrentCoordinates.realize_source runtime (maximumIndex runtime) 0 initial

theorem trajectory_realize (runtime : LivingRuntimeState process) (initial : Coordinates runtime (maximumIndex runtime) 0) (stage : Nat) :
    realize (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0 (trajectory runtime initial stage) =
      time stage (realize runtime (maximumIndex runtime) 0 initial) := by
  induction stage with
  | zero => rw [trajectory_zero]; rfl
  | succ stage previous =>
    simp only [trajectory]
    rw [SourceCopyTimeModel.time_succ, ← previous]
    exact step_realize (runtime.advance stage) (trajectory runtime initial stage)

theorem trajectory_step (runtime : LivingRuntimeState process) (initial : Coordinates runtime (maximumIndex runtime) 0) (stage : Nat) :
    trajectory runtime initial (stage + 1) = step (runtime.advance stage) (trajectory runtime initial stage) := by
  change sourceRead (runtime.advance (stage + 1)) (maximumIndex (runtime.advance (stage + 1))) 0
    (time (stage + 1) (realize runtime (maximumIndex runtime) 0 initial)) = _
  rw [SourceCopyTimeModel.time_succ, ← trajectory_realize runtime initial stage]
  rfl

theorem step_energy (runtime : LivingRuntimeState process) (previous : Coordinates runtime (maximumIndex runtime) 0) :
    ‖realize runtime.tick.next (maximumIndex runtime.tick.next) 0 (step runtime previous)‖ ^ 2 =
      ‖realize runtime (maximumIndex runtime) 0 previous‖ ^ 2 + ‖previous.2.1‖ ^ 2 +
        2 * (inner ℂ previous.2.2 previous.2.1).re := by
  rw [step_realize, SourceJointClockGraph.action_energy]
  rfl

end
end SourceCopyNativeSharedUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
