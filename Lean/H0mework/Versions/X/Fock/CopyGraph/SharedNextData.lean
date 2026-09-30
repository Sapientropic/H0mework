import H0mework.Versions.X.Fock.CopyGraph.SharedNextAddress
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesFamily
import H0mework.Versions.X.Fock.CopyGraph.NativeModelStepHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedNext

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTimeModel (finitePhases time hilbert mass)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev NextPacket (runtime : LivingRuntimeState process) :=
  SourceCopyTimeModel.Packet (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)

def update (runtime : LivingRuntimeState process) (previous : Coordinates runtime (maximumIndex runtime) 0)
    (packet : NextPacket runtime) : Coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0 :=
  ((fun coordinate => if coordinate.val = 0 then 0
    else if known : coordinate.val - 1 < cutoff runtime (maximumIndex runtime) 0 + 1 then previous.1 ⟨coordinate.val - 1, known⟩
    else recoverCoordinate runtime.tick.next (maximumIndex runtime.tick.next) 0 packet previous.2.1 (previous.2.2 + previous.2.1) coordinate),
    previous.2.1, previous.2.2 + previous.2.1)

theorem update_source (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    update runtime (sourceRead runtime (maximumIndex runtime) 0 target)
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) =
        sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) := by
  apply Prod.ext
  · funext coordinate
    change (if coordinate.val = 0 then 0
      else if known : coordinate.val - 1 < cutoff runtime (maximumIndex runtime) 0 + 1 then hilbert target (⟨coordinate.val - 1, known⟩ : Fin _).val
      else recoverCoordinate runtime.tick.next (maximumIndex runtime.tick.next) 0
        (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target))
        (mass target) (SourceJointClockGraph.clock target + mass target) coordinate) = hilbert (SourceJointClockGraph.action target) coordinate.val
    split_ifs with atOrigin known
    · symm
      exact SourceCopyTimeModel.time_hilbert_before 1 target coordinate.val (by omega)
    · have actual := SourceCopyTimeModel.time_hilbert_add 1 target (coordinate.val - 1)
      rw [show coordinate.val - 1 + 1 = coordinate.val by omega] at actual
      exact actual.symm
    · have recovered := recover_coordinate_source runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) coordinate
      rwa [SourceCopyTimeModel.mass_next, SourceCopyTimeModel.clock_next] at recovered
  · exact Prod.ext (SourceCopyTimeModel.mass_next target).symm (SourceCopyTimeModel.clock_next target).symm

theorem packet_count (runtime : LivingRuntimeState process) :
    Fintype.card (Fin ((maximumIndex runtime.tick.next).val + 1)) = inventoryBound runtime + 2 := by
  rw [Fintype.card_fin, SourceCopyCurrentCoordinates.maximum_index_val]
  have next := SourceGraphRecurrence.advance_depth runtime 1
  change inventoryBound runtime.tick.next = inventoryBound runtime + 1 at next
  omega

def nativePacket (runtime : LivingRuntimeState process) : NextPacket runtime :=
  finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (sourceValue runtime.tick.next)

end
end SourceCopySharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
