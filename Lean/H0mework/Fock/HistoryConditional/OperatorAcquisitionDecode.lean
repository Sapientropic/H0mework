import H0mework.Fock.HistoryConditional.OperatorAcquisitionMoments
import H0mework.Fock.CopyGraph.CurrentCoordinatesModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationAcquisition

open SourceCopyProgram (Index indexAfter)
open SourceCopyTimeModel (time hilbert mass phaseAt finitePhases)
open SourceCopyTemporalBoundary (recordedPrefix observer)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def hilbertRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (coordinate : Fin (cutoff runtime index steps + 1)) :
    Window runtime index →ₗ[ℂ] ℂ :=
  let actor := SourceCopySharedNext.columnAt runtime index steps coordinate
  let phase := phaseAt (inventoryBound runtime) index coordinate.val
  columns runtime index steps actor phase.castSucc - massRead runtime index nonunit steps -
    ((indexAfter (inventoryBound runtime) index actor.val + 1 : Nat) : ℂ) •
      (clockRead runtime index nonunit steps + (phase.val : ℂ) • massRead runtime index nonunit steps)

theorem hilbert_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (value : SourceJointClockGraph.Carrier)
    (coordinate : Fin (cutoff runtime index steps + 1)) :
    hilbertRead runtime index nonunit steps coordinate (recordedPrefix runtime index steps (index.val + 1) value) =
      hilbert value coordinate.val := by
  simp only [hilbertRead, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, columns_source,
    mass_source, clock_source, smul_eq_mul, Fin.val_castSucc]
  have paid := SourceCopySharedNext.recover_coordinate_source runtime index steps value coordinate
  simp only [SourceCopySharedNext.recoverCoordinate, SourceCopySharedNext.column_read_source] at paid
  exact paid

def decode (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Window runtime index →ₗ[ℂ]
      SourceCopyCurrentCoordinates.Coordinates runtime index steps :=
  (LinearMap.pi (hilbertRead runtime index nonunit steps)).prod
    ((massRead runtime index nonunit steps).prod (clockRead runtime index nonunit steps))

theorem decode_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    decode runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) value) =
      SourceCopyCurrentCoordinates.sourceRead runtime index steps value := by
  apply Prod.ext
  · funext coordinate
    exact hilbert_source runtime index nonunit steps value coordinate
  · exact Prod.ext (mass_source runtime index nonunit steps value) (clock_source runtime index nonunit steps value)

theorem retained_window (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps bound : Nat)
    (value : SourceJointClockGraph.Carrier) :
    recordedPrefix runtime index steps bound (SourceCopyCurrentCoordinates.retained runtime index steps value) =
      recordedPrefix runtime index steps bound value := by
  have same := (SourceCopyCurrentCoordinates.model_coordinates runtime index steps _ value).mpr
    (SourceCopyCurrentCoordinates.realize_source runtime index steps (SourceCopyCurrentCoordinates.sourceRead runtime index steps value))
  funext phase
  exact (model_fibre_iff _ _ _ _).mp same phase.val

end
end SourceOperatorObservationAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
