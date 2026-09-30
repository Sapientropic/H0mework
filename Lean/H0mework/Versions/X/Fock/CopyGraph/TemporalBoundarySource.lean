import H0mework.Versions.X.Fock.CopyGraph.TimeGramObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalBoundary

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (time finitePhases)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionObservationHistory (PrefixCarrier prefixEvaluator dropFirst)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def recoveryMap (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps) where
  toFun := SourceRecordedEvolution.recovery runtime index steps
  map_add' left right := by simp only [SourceRecordedEvolution.recovery_original 0, map_add]
  map_smul' scalar value := by simp only [SourceRecordedEvolution.recovery_original 0, map_smul, RingHom.id_apply]

def observer (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)).comp (recoveryMap runtime index steps)

theorem observer_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    observer runtime index steps target = fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
      (SourceRecordedEvolution.recovery runtime index steps target) := rfl

def recordedPrefix (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps bound : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] PrefixCarrier SourceJointClockGraph.Carrier bound :=
  prefixEvaluator SourceJointClockGraph.action.toLinearMap (observer runtime index steps) bound

theorem prefix_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps bound : Nat) (target : SourceJointClockGraph.Carrier) (phase : Fin (bound + 1)) :
    recordedPrefix runtime index steps bound target phase = observer runtime index steps (time phase.val target) := by
  change observer runtime index steps ((SourceJointClockGraph.action.toLinearMap ^ phase.val) target) = _
  rw [← ContinuousLinearMap.toLinearMap_pow]
  rfl

theorem prefix_packet (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    recordedPrefix runtime index steps index.val target = finitePhases runtime index steps target := by
  funext phase
  rw [prefix_source]
  rfl

theorem actual_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    dropFirst (R := ℂ) index.val (recordedPrefix runtime index steps (index.val + 1) target) =
      finitePhases runtime index steps (SourceJointClockGraph.action target) := by
  rw [← prefix_packet]
  exact LinearMap.congr_fun (SourceGeneratedActionObservationHistory.dropFirst_evaluator
    SourceJointClockGraph.action.toLinearMap (observer runtime index steps) index.val) target

theorem prefix_native (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps bound : Nat) (phase : Fin (bound + 1)) :
    recordedPrefix runtime index steps bound (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))) phase =
      observer runtime index steps (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance phase.val)))) := by
  rw [prefix_source, SourceCopyTimeModel.time_native]

theorem native_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    dropFirst (R := ℂ) index.val (recordedPrefix runtime index steps (index.val + 1)
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime)))) =
      finitePhases runtime index steps (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next))) := by
  rw [actual_next, SourceJointClockGraph.native_next]

def boundary (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  observer runtime index steps (time (scale (inventoryBound runtime) index) target) -
    SourceJointClockGraph.action (observer runtime index steps target)

end
end SourceCopyTemporalBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
