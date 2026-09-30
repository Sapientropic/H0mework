import H0mework.Fock.CopyGraph.SharedNextAddress
import H0mework.Fock.HistoryConditional.OperatorRecurrenceInstance

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationAcquisition

open SourceCopyProgram (Index indexAfter scale)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyTemporalBoundary (observer recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

abbrev Window (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :=
  PrefixCarrier SourceJointClockGraph.Carrier (index.val + 1)

def columns (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) :
    Window runtime index →ₗ[ℂ] ℂ :=
  (((innerSL ℂ (SourceColumnForcing.column (inventoryBound runtime) index actor.val)).comp
    (SourceCopyGraph.action (inventoryBound runtime) index)).toLinearMap).comp (LinearMap.proj phase)

theorem columns_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) (phase : Fin (index.val + 2)) (value : SourceJointClockGraph.Carrier) :
    columns runtime index steps actor phase (recordedPrefix runtime index steps (index.val + 1) value) =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, time phase.val value⟫_ℂ := by
  change ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
    SourceCopyGraph.action (inventoryBound runtime) index (recordedPrefix runtime index steps (index.val + 1) value phase)⟫_ℂ = _
  rw [SourceCopyTemporalBoundary.prefix_source, SourceCopySharedNext.observed_columns]

def secondColumn (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Fin (inventoryBound runtime + steps + 1) :=
  ⟨1, by
    have inside := index.isLt
    change index.val < SourceOwnedObservationHistory.NativeWindow.bound (runtimeAt (inventoryBound runtime)).current.visit.current + 1 at inside
    have limit := SourceOwnedObservationHistory.Installed.runtime_bound (inventoryBound runtime)
    omega⟩

theorem first_address (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    indexAfter (inventoryBound runtime) index 0 = index.val := by
  have paid := SourceCopyProgram.index_exact (inventoryBound runtime) index 0
  rw [SourceCopyProgram.scale_source] at paid
  simp only [Nat.zero_add, one_mul] at paid
  omega

theorem first_tail (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index 0, time (index.val + 1) value⟫_ℂ =
      mass value + ((index.val + 1 : Nat) : ℂ) *
        (SourceJointClockGraph.clock value + ((index.val + 1 : Nat) : ℂ) * mass value) := by
  rw [SourceCopyCurrentCoordinates.column_pairing, first_address, SourceCopyTimeModel.time_hilbert_before _ _ _ (Nat.lt_succ_self _),
    SourceCopyTimeModel.time_mass, SourceCopyTimeModel.time_clock, zero_add]

theorem overlap (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index 1, time (index.val + 1) value⟫_ℂ -
      ⟪SourceColumnForcing.column (inventoryBound runtime) index 0, value⟫_ℂ -
      ⟪SourceColumnForcing.column (inventoryBound runtime) index 0, time (index.val + 1) value⟫_ℂ =
        (((index.val + 1 : Nat) : ℂ) ^ 2 - 1) * mass value := by
  rw [first_tail, SourceCopyCurrentCoordinates.column_pairing, SourceCopyCurrentCoordinates.column_pairing,
    SourceCopyTimeModel.index_successor, first_address, SourceCopyProgram.scale_source,
    SourceCopyTimeModel.time_hilbert_add, SourceCopyTimeModel.time_mass, SourceCopyTimeModel.time_clock]
  push_cast
  ring

end
end SourceOperatorObservationAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
