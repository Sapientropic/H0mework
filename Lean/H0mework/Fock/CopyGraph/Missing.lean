import H0mework.Fock.CopyGraph.Loss

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyPhaseRecovery

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead)
open SourceCopyProgram (Index indexAfter)
open SourceCopyTimeModel (phaseAt finitePhases hilbert mass time)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem observer_zero_of_columns (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier)
    (zeroColumns : ∀ actor : Fin (inventoryBound runtime + 1),
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, target⟫_ℂ = 0) :
    SourceCopyTemporalBoundary.observer runtime index 0 target = 0 := by
  have imageZero (source : SourceJointFiniteDecoder.Space (inventoryBound runtime)) :
      ⟪SourceCopyGraph.action (inventoryBound runtime) index (SourceJointFiniteDecoder.read (inventoryBound runtime) source), target⟫_ℂ = 0 := by
    rw [SourceJointFiniteDecoder.read, sum_apply, map_sum, sum_inner]
    apply Finset.sum_eq_zero
    intro actor _
    change ⟪SourceCopyGraph.action (inventoryBound runtime) index
      (((Real.sqrt (SourceGeneratedRuntimeHistoryProbability.historyPMF (inventoryBound runtime) actor).toReal : ℂ) * source actor) •
        SourceJointClockGraph.read (Finsupp.single actor.val (1 : ℂ))), target⟫_ℂ = 0
    rw [map_smul, inner_smul_left]
    change starRingEnd ℂ _ * ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, target⟫_ℂ = 0
    rw [zeroColumns, mul_zero]
  have projected : (SourceCopyCofinal.historyImages (inventoryBound runtime) index 0).starProjection target = 0 := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
      ((SourceCopyCofinal.historyImages (inventoryBound runtime) index 0).zero_mem)
    rw [sub_zero]
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro value ⟨source, rfl⟩
    exact imageZero source
  apply SourceCopyGraph.action_injective (inventoryBound runtime) index
  rw [map_zero]
  have actual := SourceCopyCofinal.actual_projection runtime index 0 target
  rw [SourceCopyCofinal.advanced_action] at actual
  exact actual.symm.trans projected

theorem witness_column_other (runtime : LivingRuntimeState process)
    (omitted phase : Fin ((maximumIndex runtime.tick.next).val + 1)) (different : phase ≠ omitted)
    (actor : Fin (inventoryBound runtime.tick.next + 1)) :
    ⟪SourceColumnForcing.column (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) actor.val,
      time phase.val (SourceJointClockGraph.action (witness runtime omitted))⟫_ℂ = 0 := by
  have timeStep : time phase.val (SourceJointClockGraph.action (witness runtime omitted)) =
      time (phase.val + 1) (witness runtime omitted) := SourceCopyRecordedRecurrence.time_add phase.val 1 _
  rw [timeStep, SourceCopyCurrentCoordinates.column_pairing, SourceCopyTimeModel.time_mass,
    SourceCopyTimeModel.time_clock, witness_mass, witness_clock, mul_zero, zero_add, mul_zero, add_zero, add_zero]
  let address := indexAfter (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) actor.val
  have capped : address ≤ cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 := by
    have old := SourceCopyProgram.index_exact (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) actor.val
    have cap := SourceCopyProgram.index_exact (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) (inventoryBound runtime.tick.next)
    have ordered := Nat.mul_le_mul_right (SourceCopyProgram.scale (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next))
      (Nat.succ_le_succ (Nat.le_of_lt_succ actor.isLt))
    change (actor.val + 1) * SourceCopyProgram.scale (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) ≤
      (inventoryBound runtime.tick.next + 1) * SourceCopyProgram.scale (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) at ordered
    change address + 1 = _ at old
    change cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 + 1 = _ at cap
    omega
  change hilbert (time (phase.val + 1) (witness runtime omitted)) address = 0
  by_cases early : address < phase.val + 1
  · exact SourceCopyTimeModel.time_hilbert_before _ _ _ early
  · have shifted := SourceCopyTimeModel.time_hilbert_add (phase.val + 1) (witness runtime omitted) (address - (phase.val + 1))
    rw [Nat.sub_add_cancel (Nat.le_of_not_gt early)] at shifted
    rw [shifted, witness_hilbert]
    have fresh := witness_fresh runtime omitted
    have offFirst : address - (phase.val + 1) ≠ (witnessCoordinate runtime omitted).val - 1 := by
      intro same
      have lands : (witnessCoordinate runtime omitted).val + phase.val ∈
          Set.range (indexAfter (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)) :=
        ⟨actor.val, by change address = _; omega⟩
      have recognized := (SourceCopyTimeModel.phase_range _ _ _ phase).mp lands
      rw [witness_phase] at recognized
      exact different recognized
    have high : cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 ≤
        (witnessCoordinate runtime omitted).val - 1 + ((maximumIndex runtime.tick.next).val + 1) := by
      have bound := omitted.isLt
      dsimp only [witnessCoordinate] at *
      omega
    simp only [witnessWord, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_eq_of_ne offFirst,
      Finsupp.single_eq_of_ne (show address - (phase.val + 1) ≠ (witnessCoordinate runtime omitted).val - 1 +
        ((maximumIndex runtime.tick.next).val + 1) by omega),
      Finsupp.single_eq_of_ne (show address - (phase.val + 1) ≠ (witnessCoordinate runtime omitted).val - 1 +
        2 * ((maximumIndex runtime.tick.next).val + 1) by omega)]
    ring

theorem witness_packet_other (runtime : LivingRuntimeState process)
    (omitted phase : Fin ((maximumIndex runtime.tick.next).val + 1)) (different : phase ≠ omitted) :
    finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action (witness runtime omitted)) phase = 0 := by
  change SourceCopyTemporalBoundary.observer runtime.tick.next (maximumIndex runtime.tick.next) 0
    (time phase.val (SourceJointClockGraph.action (witness runtime omitted))) = 0
  exact observer_zero_of_columns runtime.tick.next (maximumIndex runtime.tick.next)
    (time phase.val (SourceJointClockGraph.action (witness runtime omitted)))
    (witness_column_other runtime omitted phase different)

def observedWithout (runtime : LivingRuntimeState process)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) (packet : SourceCopySharedNext.NextPacket runtime) :
    { phase : Fin ((maximumIndex runtime.tick.next).val + 1) // phase ≠ omitted } → SourceJointClockGraph.Carrier :=
  fun phase => packet phase.val

theorem witness_missing_packet (runtime : LivingRuntimeState process)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    observedWithout runtime omitted
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action (witness runtime omitted))) =
        observedWithout runtime omitted
          (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action 0)) := by
  funext phase
  change finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action (witness runtime omitted)) phase.val = _
  rw [witness_packet_other runtime omitted phase.val phase.property, map_zero]
  change 0 = SourceCopyTemporalBoundary.observer runtime.tick.next (maximumIndex runtime.tick.next) 0 (time phase.val.val 0)
  simp only [time, map_zero]

theorem no_decoder_without_phase (runtime : LivingRuntimeState process)
    (omitted : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    ¬ ∃ decoder : Coordinates runtime (maximumIndex runtime) 0 →
      ({ phase : Fin ((maximumIndex runtime.tick.next).val + 1) // phase ≠ omitted } → SourceJointClockGraph.Carrier) →
        Coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0,
      ∀ target : SourceJointClockGraph.Carrier,
        decoder (sourceRead runtime (maximumIndex runtime) 0 target)
          (observedWithout runtime omitted (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target))) =
          sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) := by
  rintro ⟨decoder, recovers⟩
  have source := recovers (witness runtime omitted)
  have zero := recovers 0
  rw [witness_previous, witness_missing_packet] at source
  rw [map_zero, map_zero, map_zero] at zero
  rw [map_zero, zero] at source
  have contradiction := congrArg (fun value : Coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0 => value.1 (witnessCoordinate runtime omitted)) source
  change 0 = hilbert (SourceJointClockGraph.action (witness runtime omitted)) (witnessCoordinate runtime omitted).val at contradiction
  rw [witness_next] at contradiction
  exact zero_ne_one contradiction

end
end SourceCopyPhaseRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
