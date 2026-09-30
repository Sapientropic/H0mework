import H0mework.Versions.X.Fock.HistoryConditional.OperatorAcquisitionDecode

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationAcquisition

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time)
open SourceCopyTemporalBoundary (recordedPrefix observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def forecast (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps ticks : Nat) : Window runtime index →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (observer runtime index steps).comp ((time ticks).toLinearMap.comp
    ((SourceCopyCurrentCoordinates.realize runtime index steps).comp (decode runtime index nonunit steps)))

theorem forecast_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps ticks : Nat) (value : SourceJointClockGraph.Carrier) :
    forecast runtime index nonunit steps ticks (recordedPrefix runtime index steps (index.val + 1) value) =
      observer runtime index steps (time ticks value) := by
  simp only [forecast, LinearMap.comp_apply, decode_source]
  have same := congrFun (retained_window runtime index steps ticks value) (Fin.last ticks)
  rw [SourceCopyTemporalBoundary.prefix_source, SourceCopyTemporalBoundary.prefix_source] at same
  exact same

def coefficients (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    Fin (index.val + 2) → SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  fun phase => (forecast runtime index nonunit steps (index.val + 2)).comp
    (LinearMap.single ℂ (fun _ : Fin (index.val + 2) => SourceJointClockGraph.Carrier) phase)

theorem coefficient_sum (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Window runtime index) :
    (∑ phase : Fin (index.val + 2), coefficients runtime index nonunit steps phase (samples phase)) =
      forecast runtime index nonunit steps (index.val + 2) samples := by
  simp only [coefficients, LinearMap.comp_apply, ← map_sum]
  exact congrArg (forecast runtime index nonunit steps (index.val + 2)) (LinearMap.sum_single_apply _ samples)

theorem source_law (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    (observer runtime index steps).comp (SourceJointClockGraph.action.toLinearMap ^ (index.val + 2)) =
      ∑ phase : Fin (index.val + 2), (coefficients runtime index nonunit steps phase).comp
        (stageEvaluator SourceJointClockGraph.action.toLinearMap (observer runtime index steps) phase.val) := by
  apply LinearMap.ext
  intro value
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  change observer runtime index steps ((SourceJointClockGraph.action.toLinearMap ^ (index.val + 2)) value) =
    ∑ phase, coefficients runtime index nonunit steps phase (recordedPrefix runtime index steps (index.val + 1) value phase)
  rw [coefficient_sum, forecast_source, ← ContinuousLinearMap.toLinearMap_pow]
  rfl

def next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Window runtime index →ₗ[ℂ] Window runtime index :=
  OperatorRecurrence.advance (index.val + 1) (coefficients runtime index nonunit steps)

theorem next_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    next runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) value) =
      recordedPrefix runtime index steps (index.val + 1) (SourceJointClockGraph.action value) :=
  LinearMap.congr_fun (OperatorRecurrence.advance_source SourceJointClockGraph.action.toLinearMap
    (observer runtime index steps) (index.val + 1) (coefficients runtime index nonunit steps)
    (source_law runtime index nonunit steps)) value

theorem model_fibre (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (left right : SourceJointClockGraph.Carrier) :
    recordedPrefix runtime index steps (index.val + 1) left = recordedPrefix runtime index steps (index.val + 1) right ↔
      projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) left =
        projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) right :=
  OperatorRecurrence.prefix_fibre_iff_model SourceJointClockGraph.action.toLinearMap (observer runtime index steps)
    (index.val + 1) (coefficients runtime index nonunit steps) (source_law runtime index nonunit steps) left right

end
end SourceOperatorObservationAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
