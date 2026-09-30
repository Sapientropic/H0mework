import H0mework.Fock.CopyGraph.Witness

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyPhaseRecovery

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead realize retained residual)
open SourceCopySharedNext (NextPacket update gain)
open SourceCopyTimeModel (finitePhases)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def remainingWithout (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.action target - realize runtime.tick.next (maximumIndex runtime.tick.next) 0
    (update runtime (sourceRead runtime (maximumIndex runtime) 0 target)
      (withoutPhase runtime (sourceRead runtime (maximumIndex runtime) 0 target)
        (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted))

theorem recovered_balance (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    realize runtime.tick.next (maximumIndex runtime.tick.next) 0
      (update runtime (sourceRead runtime (maximumIndex runtime) 0 target)
        (withoutPhase runtime (sourceRead runtime (maximumIndex runtime) 0 target)
          (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted)) +
      phaseGain runtime (sourceRead runtime (maximumIndex runtime) 0 target)
        (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted =
          retained runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) := by
  have generated := without_reconstruction runtime (sourceRead runtime (maximumIndex runtime) 0 target)
    (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted
  simp only [gain, SourceCopySharedNext.update_source] at generated
  have restored := congrArg (fun value => value + SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0
    (sourceRead runtime (maximumIndex runtime) 0 target))) generated
  convert restored using 1 <;> abel

theorem remaining_source (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    remainingWithout runtime target omitted =
      residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) +
        phaseGain runtime (sourceRead runtime (maximumIndex runtime) 0 target)
          (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted := by
  have source := SourceCopyCurrentCoordinates.reconstruction runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)
  have restored := recovered_balance runtime target omitted
  let recovered := realize runtime.tick.next (maximumIndex runtime.tick.next) 0
    (update runtime (sourceRead runtime (maximumIndex runtime) 0 target)
      (withoutPhase runtime (sourceRead runtime (maximumIndex runtime) 0 target)
        (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted))
  calc
    remainingWithout runtime target omitted =
        (retained runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) +
          residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) - recovered :=
      congrArg (fun value => value - recovered) source.symm
    _ = _ := by rw [← restored]; dsimp only [recovered]; abel

theorem remaining_energy (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    ‖remainingWithout runtime target omitted‖ ^ 2 =
      ‖residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)‖ ^ 2 +
        ‖phaseGain runtime (sourceRead runtime (maximumIndex runtime) 0 target)
          (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted‖ ^ 2 := by
  rw [remaining_source]
  dsimp only [phaseGain]
  with_reducible exact slice_tail_energy runtime.tick.next _ omitted (SourceJointClockGraph.action target)

theorem without_budget (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    ‖gain runtime (sourceRead runtime (maximumIndex runtime) 0 target)
      (withoutPhase runtime (sourceRead runtime (maximumIndex runtime) 0 target)
        (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted)‖ ^ 2 +
      ‖remainingWithout runtime target omitted‖ ^ 2 = ‖residual runtime (maximumIndex runtime) 0 target‖ ^ 2 := by
  have partition := without_energy runtime (sourceRead runtime (maximumIndex runtime) 0 target)
    (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) omitted
  have full := SourceCopySharedNext.gain_budget runtime target
  rw [remaining_energy]
  linarith only [partition, full]

theorem strict_loss (runtime : LivingRuntimeState process)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    ‖residual runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceJointClockGraph.action (witness runtime omitted))‖ ^ 2 <
        ‖remainingWithout runtime (witness runtime omitted) omitted‖ ^ 2 := by
  have positive := sq_pos_of_pos (norm_pos_iff.mpr (witness_recovery_nonzero runtime omitted))
  rw [remaining_energy]
  linarith only [positive]

end
end SourceCopyPhaseRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
