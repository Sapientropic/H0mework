import H0mework.Versions.X.Fock.CopyGraph.FutureUpdateSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureUpdate

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyFutureCoordinates (Coordinates sourceRead)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def newRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (previous : Coordinates runtime index steps) (observed : Samples runtime index)
    (coordinate : Fin (cutoff runtime index (steps + 2) + 1))
    (fresh : cutoff runtime index (steps + 1) < coordinate.val) : ℂ :=
  response runtime index steps (blockPhase runtime index steps coordinate fresh) observed - previous.2.1 -
    ((cutoff runtime index (steps + 2) + 1 : Nat) : ℂ) *
      (previous.2.2 + ((blockPhase runtime index steps coordinate fresh).val : ℂ) * previous.2.1)

theorem new_read_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index (steps + 2) + 1))
    (fresh : cutoff runtime index (steps + 1) < coordinate.val) (target : SourceJointClockGraph.Carrier) :
    newRead runtime index steps (sourceRead runtime index steps target) (samples runtime index steps target) coordinate fresh =
      hilbert target coordinate.val := by
  have moved := SourceCopyTimeModel.time_hilbert_add (blockPhase runtime index steps coordinate fresh).val target coordinate.val
  rw [block_address] at moved
  rw [newRead, response_source, SourceCopyFutureCoordinates.column_pairing,
    SourceCopyTimeModel.time_mass, SourceCopyTimeModel.time_clock]
  change hilbert (time (blockPhase runtime index steps coordinate fresh).val target) (cutoff runtime index (steps + 2)) +
    mass target + ((cutoff runtime index (steps + 2) + 1 : Nat) : ℂ) *
      (SourceJointClockGraph.clock target + ((blockPhase runtime index steps coordinate fresh).val : ℂ) * mass target) -
    mass target - ((cutoff runtime index (steps + 2) + 1 : Nat) : ℂ) *
      (SourceJointClockGraph.clock target + ((blockPhase runtime index steps coordinate fresh).val : ℂ) * mass target) = _
  rw [moved]
  ring

def update (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (previous : Coordinates runtime index steps) (observed : Samples runtime index) : Coordinates runtime index (steps + 1) :=
  (fun coordinate => if inside : coordinate.val < cutoff runtime index (steps + 1) + 1 then
      previous.1 ⟨coordinate.val, inside⟩
    else newRead runtime index steps previous observed coordinate (by omega), previous.2.1, previous.2.2)

theorem update_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    update runtime index steps (sourceRead runtime index steps target) (samples runtime index steps target) =
      sourceRead runtime index (steps + 1) target := by
  apply Prod.ext
  · funext coordinate
    change (if inside : coordinate.val < cutoff runtime index (steps + 1) + 1 then
      (sourceRead runtime index steps target).1 ⟨coordinate.val, inside⟩
      else newRead runtime index steps (sourceRead runtime index steps target) (samples runtime index steps target) coordinate (by omega)) = _
    split_ifs with inside
    · rfl
    · exact new_read_source runtime index steps coordinate (by omega) target
  · rfl

end
end SourceCopyFutureUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
