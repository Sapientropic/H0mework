import H0mework.Versions.X.Fock.CopyGraph.FutureCoordinatesObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureUpdate

open SourceCopyProgram (Index indexAfter scale)
open SourceCopyTimeModel (time)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem cutoff_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    cutoff runtime index (steps + 2) = cutoff runtime index (steps + 1) + scale (inventoryBound runtime) index := by
  change indexAfter (inventoryBound runtime) index ((inventoryBound runtime + steps + 1) + 1) =
    indexAfter (inventoryBound runtime) index (inventoryBound runtime + steps + 1) + scale (inventoryBound runtime) index
  exact SourceCopyTimeModel.index_successor _ _ _

abbrev Samples (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :=
  PrefixCarrier SourceJointClockGraph.Carrier index.val

def samples (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] Samples runtime index :=
  SourceCopyTemporalBoundary.recordedPrefix runtime index (steps + 2) index.val

def response (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (phase : Fin (index.val + 1)) : Samples runtime index →ₗ[ℂ] ℂ :=
  (((innerSL ℂ (SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 2))).comp
    (SourceCopyGraph.action (inventoryBound runtime) index)).toLinearMap).comp (LinearMap.proj phase)

theorem response_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (phase : Fin (index.val + 1)) (target : SourceJointClockGraph.Carrier) :
    response runtime index steps phase (samples runtime index steps target) =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 2), time phase.val target⟫_ℂ := by
  change ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 2),
    SourceCopyGraph.action (inventoryBound runtime) index
      (SourceCopyTemporalBoundary.recordedPrefix runtime index (steps + 2) index.val target phase)⟫_ℂ = _
  rw [SourceCopyTemporalBoundary.prefix_source]
  exact SourceCopyFutureCoordinates.observed_column runtime index (steps + 1) _

def blockPhase (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index (steps + 2) + 1))
    (fresh : cutoff runtime index (steps + 1) < coordinate.val) : Fin (index.val + 1) :=
  ⟨cutoff runtime index (steps + 2) - coordinate.val, by
    have address := cutoff_step runtime index steps
    have count := SourceCopyProgram.scale_source (inventoryBound runtime) index
    omega⟩

theorem block_address (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index (steps + 2) + 1))
    (fresh : cutoff runtime index (steps + 1) < coordinate.val) :
    coordinate.val + (blockPhase runtime index steps coordinate fresh).val = cutoff runtime index (steps + 2) := by
  change coordinate.val + (cutoff runtime index (steps + 2) - coordinate.val) = cutoff runtime index (steps + 2)
  omega

end
end SourceCopyFutureUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
