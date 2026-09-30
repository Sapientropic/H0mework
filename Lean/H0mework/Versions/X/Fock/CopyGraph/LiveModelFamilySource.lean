import H0mework.Versions.X.Fock.CopyGraph.NativeModelStepHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyLiveModelFamily

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open SourceGeneratedJointClockGraph SourceOwnedObservationHistory
open SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.Dynamic
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2

theorem advanced_index_val (depth : Nat) (index : Index depth) (steps : Nat) :
    (SourceGraphLoss.advancedIndex depth index steps).val = index.val := by
  induction steps with
  | zero => rfl
  | succ steps previous => exact previous

def currentIndex (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Index (inventoryBound (runtime.advance steps)) :=
  (SourceGraphRecurrence.advance_depth runtime steps).symm ▸
    SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps

theorem current_index_val (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    (currentIndex runtime index steps).val = index.val := by
  have transport : ∀ (a b : Nat) (same : a = b) (actor : Index a), (same ▸ actor).val = actor.val := by
    intro a b same actor
    cases same
    rfl
  exact (transport _ _ (SourceGraphRecurrence.advance_depth runtime steps).symm _).trans
    (advanced_index_val _ index steps)

theorem current_index_material (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    NativeCopy.Fock.material (inventoryBound (runtime.advance steps)) (currentIndex runtime index steps) =
      NativeCopy.Fock.material (inventoryBound runtime) index := by
  have transport : ∀ (a b : Nat) (same : a = b) (actor : Index a),
      NativeCopy.Fock.material b (same ▸ actor) = NativeCopy.Fock.material a actor := by
    intro a b same actor
    cases same
    rfl
  exact (transport _ _ (SourceGraphRecurrence.advance_depth runtime steps).symm _).trans
    (SourceGraphLoss.advanced_material _ index steps)

theorem observer_current (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    observer (runtime.advance steps) (currentIndex runtime index steps) 0 = observer runtime index steps := by
  ext target
  rw [SourceCopyTemporalBoundary.observer_source, SourceCopyTemporalBoundary.observer_source,
    SourceRecordedEvolution.recovery_original 0, SourceRecordedEvolution.recovery_original 0,
    SourceCompleteGraph.recovery_canonical, SourceCompleteGraph.recovery_canonical]
  have transport : ∀ (a b : Nat) (same : a = b) (actor : Index a),
      fieldRead b b (SourceConditionalGraphDecoder.fieldDecode b b (same ▸ actor) (Hilbert.read 0 b) target) =
        fieldRead a a (SourceConditionalGraphDecoder.fieldDecode a a actor (Hilbert.read 0 a) target) := by
    intro a b same actor
    cases same
    rfl
  simpa only [Nat.add_zero, SourceGraphLoss.advancedIndex, currentIndex] using
    transport _ _ (SourceGraphRecurrence.advance_depth runtime steps).symm
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)

def birthIndex (position : Nat) : Index (inventoryBound (runtimeAt position)) :=
  ⟨position, by rw [runtime_bound, inventory_bound, runtimeAt_state]; exact Nat.lt_succ_self position⟩

def age (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Nat :=
  inventoryBound runtime - index.val

theorem birth_reaches_current (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (runtimeAt index.val).advance (age runtime index) = runtime := by
  have inside := index.isLt
  have bound := runtime_bound (inventoryBound runtime)
  have before : index.val ≤ inventoryBound runtime := by omega
  rw [advance_original, runtimeAt_state, age, Nat.add_sub_of_le before, inventory_bound]
  exact (runtime_eq runtime).symm

theorem actor_birth (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    NativeCopy.Fock.material (inventoryBound runtime) index = (runtimeAt index.val).current.visit.current ∧
      type_of% (window_actor_factorizes (inventoryBound runtime) index) :=
  ⟨(window_actor_factorizes (inventoryBound runtime) index).1, window_actor_factorizes (inventoryBound runtime) index⟩

theorem observer_identified (origin current : LivingRuntimeState process)
    (actor : Index (inventoryBound origin)) (index : Index (inventoryBound current)) (steps : Nat)
    (reached : origin.advance steps = current) (retained : actor.val = index.val) :
    observer current index 0 = observer origin actor steps := by
  subst current
  have same : currentIndex origin actor steps = index := Fin.ext ((current_index_val origin actor steps).trans retained)
  rw [← same]
  exact observer_current origin actor steps

theorem observer_birth (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    observer runtime index 0 = observer (runtimeAt index.val) (birthIndex index.val) (age runtime index) :=
  observer_identified (runtimeAt index.val) runtime (birthIndex index.val) index (age runtime index)
    (birth_reaches_current runtime index) rfl

end
end SourceCopyLiveModelFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
