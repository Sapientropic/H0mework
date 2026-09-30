import H0mework.Fock.CopyGraph.Phase.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyPhaseRecovery

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead realize retained residual)
open SourceCopySharedNext (NextPacket update gain recoverCoordinate columnRead)
open SourceCopyTimeModel (phaseAt finitePhases hilbert)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem gain_coordinate (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime)
    (coordinate : Fin (cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 + 1)) :
    hilbert (gain runtime previous packet) coordinate.val = (update runtime previous packet).1 coordinate -
      hilbert (SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0 previous)) coordinate.val := by
  have pulled := congrArg (fun value : Coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0 => value.1 coordinate)
    (map_sub (sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0)
      (realize runtime.tick.next (maximumIndex runtime.tick.next) 0 (update runtime previous packet))
      (SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0 previous)))
  rw [SourceCopyCurrentCoordinates.realize_source] at pulled
  exact pulled

theorem coordinate_from_phase (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (left right : NextPacket runtime)
    (coordinate : Fin (cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 + 1))
    (same : left (phaseAt (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) coordinate.val) =
      right (phaseAt (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) coordinate.val)) :
    (update runtime previous left).1 coordinate = (update runtime previous right).1 coordinate := by
  dsimp only [update]
  split_ifs
  · rfl
  · rfl
  · simp only [recoverCoordinate, columnRead, same]

theorem phase_from_packet (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (left right : NextPacket runtime)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) (same : left phase = right phase) :
    phaseGain runtime previous left phase = phaseGain runtime previous right phase := by
  apply congrArg (realize runtime.tick.next (maximumIndex runtime.tick.next) 0)
  apply Prod.ext
  · funext coordinate
    change (if phaseAt (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) coordinate.val = phase
      then hilbert (gain runtime previous left) coordinate.val else 0) =
        (if phaseAt (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) coordinate.val = phase
          then hilbert (gain runtime previous right) coordinate.val else 0)
    split_ifs with selected
    · rw [gain_coordinate, gain_coordinate]
      rw [coordinate_from_phase runtime previous left right coordinate (by rwa [selected])]
    · rfl
  · rfl

def predictedPacket (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) : NextPacket runtime :=
  finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0 previous))

theorem predicted_gain (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) :
    gain runtime previous (predictedPacket runtime previous) = 0 := by
  have generated := SourceCopySharedNext.gain_source runtime (realize runtime (maximumIndex runtime) 0 previous)
  rw [SourceCopyCurrentCoordinates.realize_source] at generated
  have empty : residual runtime (maximumIndex runtime) 0 (realize runtime (maximumIndex runtime) 0 previous) = 0 := by
    change realize runtime (maximumIndex runtime) 0 previous -
      realize runtime (maximumIndex runtime) 0 (sourceRead runtime (maximumIndex runtime) 0 (realize runtime (maximumIndex runtime) 0 previous)) = 0
    rw [SourceCopyCurrentCoordinates.realize_source, sub_self]
  apply generated.trans
  change retained runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 (realize runtime (maximumIndex runtime) 0 previous))) = 0
  rw [empty, map_zero, map_zero]

theorem predicted_phase (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    phaseGain runtime previous (predictedPacket runtime previous) phase = 0 := by
  simp only [phaseGain, predicted_gain, map_zero, slice]
  convert map_zero (realize runtime.tick.next (maximumIndex runtime.tick.next) 0) using 1
  apply congrArg (realize runtime.tick.next (maximumIndex runtime.tick.next) 0)
  apply Prod.ext
  · funext coordinate
    simp
  · rfl

def withoutPhase (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) : NextPacket runtime :=
  Function.update packet omitted (predictedPacket runtime previous omitted)

theorem without_phase (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime)
    (omitted phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    phaseGain runtime previous (withoutPhase runtime previous packet omitted) phase =
      if phase = omitted then 0 else phaseGain runtime previous packet phase := by
  by_cases same : phase = omitted
  · subst phase
    rw [if_pos rfl]
    exact (phase_from_packet runtime previous _ (predictedPacket runtime previous) omitted (by simp [withoutPhase])).trans
      (predicted_phase runtime previous omitted)
  · rw [if_neg same]
    exact phase_from_packet runtime previous _ packet phase (by simp [withoutPhase, same])

theorem without_reconstruction (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    gain runtime previous (withoutPhase runtime previous packet omitted) + phaseGain runtime previous packet omitted =
      gain runtime previous packet := by
  rw [← phase_sum runtime previous (withoutPhase runtime previous packet omitted), ← phase_sum runtime previous packet]
  simp only [without_phase]
  have split : ∀ phase, phaseGain runtime previous packet phase =
      (if phase = omitted then 0 else phaseGain runtime previous packet phase) +
        (if phase = omitted then phaseGain runtime previous packet omitted else 0) := by
    intro phase
    split_ifs with same
    · subst phase
      exact (zero_add _).symm
    · exact (add_zero _).symm
  conv_rhs => rw [show (fun phase => phaseGain runtime previous packet phase) = _ from funext split]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem without_energy (runtime : LivingRuntimeState process)
    (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    ‖gain runtime previous (withoutPhase runtime previous packet omitted)‖ ^ 2 +
      ‖phaseGain runtime previous packet omitted‖ ^ 2 = ‖gain runtime previous packet‖ ^ 2 := by
  rw [← phase_energy runtime previous (withoutPhase runtime previous packet omitted), ← phase_energy runtime previous packet]
  simp only [without_phase]
  have split : ∀ phase, ‖phaseGain runtime previous packet phase‖ ^ 2 =
      ‖(if phase = omitted then 0 else phaseGain runtime previous packet phase)‖ ^ 2 +
        (if phase = omitted then ‖phaseGain runtime previous packet omitted‖ ^ 2 else 0) := by
    intro phase
    split_ifs with same
    · subst phase
      simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
    · exact (add_zero _).symm
  conv_rhs => rw [show (fun phase => ‖phaseGain runtime previous packet phase‖ ^ 2) = _ from funext split]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end
end SourceCopyPhaseRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
