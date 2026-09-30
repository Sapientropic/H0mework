import H0mework.Versions.X.Fock.CopyGraph.TemporalAcquisitionObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecordedRecurrence

open SourceCopyProgram (Index indexAfter scale)
open SourceCopyTimeModel (time hilbert mass)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def cutoff (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) : Nat :=
  indexAfter (inventoryBound runtime) index (inventoryBound runtime + steps)

def difference (stage : Nat) (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  time (stage + 2) target - (2 : ℂ) • time (stage + 1) target + time stage target

theorem difference_mass (stage : Nat) (target : SourceJointClockGraph.Carrier) : mass (difference stage target) = 0 := by
  simp only [difference, mass, map_add, map_sub, map_smul]
  change mass (time (stage + 2) target) - (2 : ℂ) * mass (time (stage + 1) target) + mass (time stage target) = 0
  simp only [SourceCopyTimeModel.time_mass]
  ring

theorem difference_clock (stage : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (difference stage target) = 0 := by
  rw [difference, map_add, map_sub, map_smul]
  simp only [SourceCopyTimeModel.time_clock, smul_eq_mul]
  push_cast
  ring

theorem difference_before (stage : Nat) (target : SourceJointClockGraph.Carrier) (coordinate : Nat)
    (before : coordinate < stage) : hilbert (difference stage target) coordinate = 0 := by
  simp only [difference, hilbert, map_add, map_sub, map_smul]
  change ((hilbert (time (stage + 2) target) - (2 : ℂ) • hilbert (time (stage + 1) target)) +
    hilbert (time stage target)) coordinate = 0
  rw [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul]
  change hilbert (time (stage + 2) target) coordinate - (2 : ℂ) * hilbert (time (stage + 1) target) coordinate +
    hilbert (time stage target) coordinate = 0
  rw [SourceCopyTimeModel.time_hilbert_before _ _ _ (by omega),
    SourceCopyTimeModel.time_hilbert_before _ _ _ (by omega), SourceCopyTimeModel.time_hilbert_before _ _ _ before]
  ring

theorem address_mono (depth : Nat) (index : Index depth) : Monotone (indexAfter depth index) := by
  intro left right ordered
  have l := SourceCopyProgram.index_exact depth index left
  have r := SourceCopyProgram.index_exact depth index right
  have product := Nat.mul_le_mul_right (scale depth index) (Nat.add_le_add_right ordered 1)
  omega

theorem difference_captured (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) (actor : Fin (inventoryBound runtime + steps + 1)) :
    hilbert (difference (cutoff runtime index steps + 1) target) (indexAfter (inventoryBound runtime) index actor.val) = 0 := by
  apply difference_before
  have within := address_mono (inventoryBound runtime) index (show actor.val ≤ inventoryBound runtime + steps by omega)
  exact Nat.lt_succ_of_le within

end
end SourceCopyRecordedRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
