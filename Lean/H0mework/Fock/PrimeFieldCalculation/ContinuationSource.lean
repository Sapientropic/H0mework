import H0mework.Fock.HistoryCopy.InformationSource
import H0mework.Fock.HistoryModel.RecordedFrameConsumer
import H0mework.Fock.HistoryModel.Next

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionContinuation

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourcePrimeHistoryRecovery

noncomputable section

theorem runtime_eq (runtime : LivingRuntimeState process) :
    runtime = runtimeAt runtime.state :=
  LivingRuntimeState.ext (runtimeAt_state runtime.state).symm

def inventoryBound (runtime : LivingRuntimeState process) : Nat :=
  NativeWindow.bound runtime.current.visit.current

theorem inventory_bound (runtime : LivingRuntimeState process) :
    inventoryBound runtime = runtime.state :=
  (congrArg (fun current : LivingRuntimeState process =>
    NativeWindow.bound current.current.visit.current) (runtime_eq runtime)).trans
      (runtime_bound runtime.state)

theorem advance_original (runtime : LivingRuntimeState process) (steps : Nat) :
    runtime.advance steps = runtimeAt (runtime.state + steps) := by
  induction steps with
  | zero => exact runtime_eq runtime
  | succ steps previous =>
      exact congrArg (fun current : LivingRuntimeState process => current.tick.next) previous

def active (runtime : LivingRuntimeState process) :
    projectionLaw.ActiveAt PUnit.unit runtime.emittedOccurrence :=
  ⟨by
    have same := congrArg (fun current : LivingRuntimeState process =>
      scanIndex current.current.visit.current) (runtime_eq runtime)
    rw [runtimeAt_scanIndex] at same
    omega⟩

theorem classify_active (runtime : LivingRuntimeState process) :
    projectionLaw.classify PUnit.unit runtime.emittedOccurrence = .inl (active runtime) := by
  generalize classified : projectionLaw.classify PUnit.unit runtime.emittedOccurrence = result
  cases result with
  | inl found =>
      have same : found = active runtime := PLift.down_injective (Subsingleton.elim _ _)
      exact congrArg Sum.inl same
  | inr impossible =>
      have positive := (active runtime).down
      have zero := impossible.down
      omega

def frontier (runtime : LivingRuntimeState process) :
    SourceNativeRuntimeCalculationFrontierAt runtimeFacade runtime .particleWave :=
  .ofActive (active runtime) (classify_active runtime)
    (windowBound sourceOwner (inventoryBound runtime))
    (fun index sourcePayload material =>
      let current : CanonicalUnitArithmeticRoot.Current :=
        (runtime.advance index.val).current.visit.current
      HEq (SourceFactorizationAction.Fock.receipt sourcePayload) sourcePayload.operationDerivation ∧
        type_of% (SourceFactorizationAction.Fock.counts_next current) ∧
        sourceFieldAt material.next.current.visit.current =
          sourceFieldAt current + SourceFactorizationAction.Fock.birth current ∧
        SourceGeneratedConditionalInventory.snapshotCost material.next.state =
          SourceGeneratedConditionalInventory.snapshotCost (runtime.advance index.val).state +
            (if Nat.Prime (2 * (runtime.advance index.val).state + 5) then 0 else 1) ∧
        ∀ actor : Fin (NativeWindow.bound current + 1),
          SourceCopyInventory.inventoryCost (NativeWindow.point current actor) material.next.state =
            SourceCopyInventory.inventoryCost (NativeWindow.point current actor) (runtime.advance index.val).state +
              SourceCopyInventory.increment (NativeWindow.point current actor) (runtime.advance index.val).state)

theorem realization (runtime : LivingRuntimeState process) :
    SourceNativeRuntimeCalculationRealizationAt (frontier runtime) where
  operationAt index := ⟨SourceFactorizationAction.Fock.receipt_is_original _,
    SourceFactorizationAction.Fock.counts_next _, SourceFactorizationAction.Fock.field_next _,
    SourceGeneratedConditionalInventory.actual_cost_step (runtime.advance index.val).state,
    fun _actor => SourceCopyInventory.cost_step _ (runtime.advance index.val).state⟩

def normal (runtime : LivingRuntimeState process) :
    SourceGeneratedRuntimeCalculationNormalFormAt (realization runtime) :=
  .generate (realization runtime)

theorem target_is_original (runtime : LivingRuntimeState process) :
    (normal runtime).targetRuntime =
      (SourcePrimeCalculation.normal (inventoryBound runtime)).targetRuntime := by
  change runtime.advance (windowBound sourceOwner (inventoryBound runtime) + 1) = _
  rw [advance_original, ← inventory_bound runtime, SourcePrimeCalculation.target_is_original]
  rfl

def roundRuntime : Nat → LivingRuntimeState process
  | 0 => runtimeSeed
  | round + 1 => (normal (roundRuntime round)).targetRuntime.tick.next

theorem round_next (round : Nat) :
    roundRuntime (round + 1) = (normal (roundRuntime round)).targetRuntime.tick.next := rfl

end
end SourceGeneratedAcquisitionContinuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
