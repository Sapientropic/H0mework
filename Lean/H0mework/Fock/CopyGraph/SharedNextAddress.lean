import H0mework.Fock.CopyGraph.SharedNextSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedNext

open SourceCopyProgram (Index indexAfter)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTimeModel (phaseAt time hilbert mass finitePhases)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def columnAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index steps + 1)) : Fin (inventoryBound runtime + steps + 1) :=
  ⟨coordinate.val / (index.val + 1), by
    rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos index.val)]
    have endpoint := SourceCopyProgram.index_exact (inventoryBound runtime) index (inventoryBound runtime + steps)
    rw [SourceCopyProgram.scale_source] at endpoint
    exact coordinate.isLt.trans_eq endpoint⟩

theorem column_phase_address (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index steps + 1)) :
    coordinate.val + (phaseAt (inventoryBound runtime) index coordinate.val).val =
      indexAfter (inventoryBound runtime) index (columnAt runtime index steps coordinate).val := by
  let selected : Fin (index.val + 1) := ⟨index.val - coordinate.val % (index.val + 1), by omega⟩
  have modulus := Nat.mod_lt coordinate.val (Nat.succ_pos index.val)
  have divided := Nat.mod_add_div coordinate.val (index.val + 1)
  have endpoint := SourceCopyProgram.index_exact (inventoryBound runtime) index (coordinate.val / (index.val + 1))
  rw [SourceCopyProgram.scale_source, Nat.add_mul, one_mul] at endpoint
  rw [Nat.mul_comm (index.val + 1) (coordinate.val / (index.val + 1))] at divided
  change coordinate.val % (index.val + 1) < index.val + 1 at modulus
  change coordinate.val % (index.val + 1) + (coordinate.val / (index.val + 1)) * (index.val + 1) = coordinate.val at divided
  change indexAfter (inventoryBound runtime) index (coordinate.val / (index.val + 1)) + 1 =
    (coordinate.val / (index.val + 1)) * (index.val + 1) + (index.val + 1) at endpoint
  have lands : coordinate.val + selected.val = indexAfter (inventoryBound runtime) index (coordinate.val / (index.val + 1)) := by
    dsimp only [selected]
    omega
  have recognized : selected = phaseAt (inventoryBound runtime) index coordinate.val :=
    (SourceCopyTimeModel.phase_range (inventoryBound runtime) index coordinate.val selected).mp ⟨_, lands.symm⟩
  rw [← recognized]
  exact lands

def recoverCoordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (packet : SourceCopyTimeModel.Packet (inventoryBound runtime) index) (knownMass knownClock : ℂ)
    (coordinate : Fin (cutoff runtime index steps + 1)) : ℂ :=
  let actor := columnAt runtime index steps coordinate
  let phase := phaseAt (inventoryBound runtime) index coordinate.val
  columnRead runtime index steps packet actor phase - knownMass -
    ((indexAfter (inventoryBound runtime) index actor.val + 1 : Nat) : ℂ) * (knownClock + (phase.val : ℂ) * knownMass)

theorem recover_coordinate_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (coordinate : Fin (cutoff runtime index steps + 1)) :
    recoverCoordinate runtime index steps (finitePhases runtime index steps target) (mass target) (SourceJointClockGraph.clock target) coordinate =
      hilbert target coordinate.val := by
  have moved := SourceCopyTimeModel.time_hilbert_add (phaseAt (inventoryBound runtime) index coordinate.val).val target coordinate.val
  rw [column_phase_address] at moved
  simp only [recoverCoordinate, column_read_source, SourceCopyCurrentCoordinates.column_pairing,
    SourceCopyTimeModel.time_mass, SourceCopyTimeModel.time_clock]
  rw [moved]
  ring

end
end SourceCopySharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
