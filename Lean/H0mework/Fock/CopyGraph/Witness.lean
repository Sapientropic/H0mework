import H0mework.Fock.CopyGraph.Phase.Recovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyPhaseRecovery

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead realize)
open SourceCopySharedNext (NextPacket update gain)
open SourceCopyTimeModel (phaseAt finitePhases hilbert mass time)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def witnessCoordinate (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    Fin (cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 + 1) :=
  ⟨cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 - phase.val, by omega⟩

theorem witness_fresh (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    cutoff runtime (maximumIndex runtime) 0 + 1 < (witnessCoordinate runtime phase).val := by
  have growth := SourceCopySharedNext.cutoff_growth runtime
  have count := SourceCopySharedNext.packet_count runtime
  rw [Fintype.card_fin] at count
  have bound := phase.isLt
  dsimp only [witnessCoordinate]
  omega

theorem witness_phase (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    phaseAt (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) (witnessCoordinate runtime phase).val = phase := by
  have fresh := witness_fresh runtime phase
  symm
  apply (SourceCopyTimeModel.phase_range _ _ _ phase).mp
  refine ⟨inventoryBound runtime.tick.next, ?_⟩
  change cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 =
    cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 - phase.val + phase.val
  dsimp only [witnessCoordinate] at fresh
  omega

def witnessWord (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) : Nat →₀ ℂ :=
  let address := (witnessCoordinate runtime phase).val - 1
  let stride := (maximumIndex runtime.tick.next).val + 1
  Finsupp.single address 1 - (2 : ℂ) • Finsupp.single (address + stride) 1 +
    Finsupp.single (address + 2 * stride) 1

def witness (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (witnessWord runtime phase)

theorem witness_mass (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) : mass (witness runtime phase) = 0 := by
  change SourceSuccessorBoundary.mass ℂ (witnessWord runtime phase) = 0
  simp only [witnessWord, map_add, map_sub, map_smul, mass_single, smul_eq_mul]
  ring

theorem witness_clock (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) : SourceJointClockGraph.clock (witness runtime phase) = 0 := by
  change SourceClockComplex.clock (witnessWord runtime phase) = 0
  simp only [witnessWord, map_add, map_sub, map_smul, SourceClockComplex.clock_single,
    SourceClockModel.rawClock, smul_eq_mul, one_mul]
  push_cast
  ring

theorem witness_hilbert (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) (coordinate : Nat) :
    hilbert (witness runtime phase) coordinate = witnessWord runtime phase coordinate :=
  readWord_coordinate (witnessWord runtime phase) coordinate

theorem witness_first (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    hilbert (witness runtime phase) ((witnessCoordinate runtime phase).val - 1) = 1 := by
  rw [witness_hilbert]
  simp only [witnessWord, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (show (witnessCoordinate runtime phase).val - 1 ≠
      (witnessCoordinate runtime phase).val - 1 + ((maximumIndex runtime.tick.next).val + 1) by omega),
    Finsupp.single_eq_of_ne (show (witnessCoordinate runtime phase).val - 1 ≠
      (witnessCoordinate runtime phase).val - 1 + 2 * ((maximumIndex runtime.tick.next).val + 1) by omega)]
  ring

theorem witness_previous (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    sourceRead runtime (maximumIndex runtime) 0 (witness runtime phase) = 0 := by
  apply Prod.ext
  · funext coordinate
    change hilbert (witness runtime phase) coordinate.val = 0
    rw [witness_hilbert]
    have fresh := witness_fresh runtime phase
    simp only [witnessWord, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_eq_of_ne (show coordinate.val ≠ (witnessCoordinate runtime phase).val - 1 by omega),
      Finsupp.single_eq_of_ne (show coordinate.val ≠ (witnessCoordinate runtime phase).val - 1 + ((maximumIndex runtime.tick.next).val + 1) by omega),
      Finsupp.single_eq_of_ne (show coordinate.val ≠ (witnessCoordinate runtime phase).val - 1 + 2 * ((maximumIndex runtime.tick.next).val + 1) by omega)]
    ring
  · exact Prod.ext (witness_mass runtime phase) (witness_clock runtime phase)

theorem witness_next (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    hilbert (SourceJointClockGraph.action (witness runtime phase)) (witnessCoordinate runtime phase).val = 1 := by
  have shifted := SourceCopyTimeModel.time_hilbert_add 1 (witness runtime phase) ((witnessCoordinate runtime phase).val - 1)
  have fresh := witness_fresh runtime phase
  rw [show (witnessCoordinate runtime phase).val - 1 + 1 = (witnessCoordinate runtime phase).val by omega] at shifted
  exact shifted.trans (witness_first runtime phase)

theorem witness_recovered (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    hilbert (phaseGain runtime (sourceRead runtime (maximumIndex runtime) 0 (witness runtime phase))
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action (witness runtime phase))) phase)
      (witnessCoordinate runtime phase).val = 1 := by
  rw [phaseGain, slice_coordinate]
  change (if phaseAt (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) (witnessCoordinate runtime phase).val = phase
    then hilbert (gain runtime (sourceRead runtime (maximumIndex runtime) 0 (witness runtime phase))
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action (witness runtime phase))))
      (witnessCoordinate runtime phase).val else 0) = 1
  rw [witness_phase, if_pos rfl, gain_coordinate, SourceCopySharedNext.update_source, witness_previous, map_zero, map_zero]
  change hilbert (SourceJointClockGraph.action (witness runtime phase)) (witnessCoordinate runtime phase).val - 0 = 1
  rw [sub_zero, witness_next]

theorem witness_recovery_nonzero (runtime : LivingRuntimeState process)
    (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    phaseGain runtime (sourceRead runtime (maximumIndex runtime) 0 (witness runtime phase))
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action (witness runtime phase))) phase ≠ 0 := by
  intro vanished
  have recovered := witness_recovered runtime phase
  rw [vanished] at recovered
  exact zero_ne_one recovered

end
end SourceCopyPhaseRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
