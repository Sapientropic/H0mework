import SaturationMonoid.GenericFoundation.Cofinal.Topology.Successor
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.Consumer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native

open Source CofinalAllPrimeTopology

local notation "fieldAt" => SourceOperationNative.Field.sourceValue
local notation "fieldStep" => SourceOperationRuntime.Character.successor

/-- The fixed-target actor's literal pulse supplies the native field action at every prime-power stage. -/
theorem actual_actor_topology_successor (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    let runtime := C.mathRuntime depth (count+1)
    let action := fieldStep (nativeRead depth) (nativeEnvironment depth) runtime
    let old := fieldAt runtime
    let next := fieldAt runtime.tick.next
    @UniformContinuous _ _ (topology depth (count+1)) (topology depth ((count+1)+1)) action ∧
      allStageSuccessor action (allStageMap old) = allStageMap next ∧
      allPrimeSuccessor action (allPrimeMap old) = allPrimeMap next ∧
      allPrimeCoimageSuccessor action ((AllPrimeKernel (L := NativeField depth (count+1))).mkQ old) =
        (AllPrimeKernel (L := NativeField depth ((count+1)+1))).mkQ next ∧
      type_of% (SourceOperationNative.Field.sourceValue_read runtime 0 ⟨0, by omega⟩) ∧
      type_of% (SourceOperationNative.Field.nextWitness_is_actual runtime 0 ⟨0, by omega⟩) ∧
      type_of% (Consumer.paid_actor_action_inverse depth count within) := by
  dsimp only
  let runtime := C.mathRuntime depth (count+1)
  let action := fieldStep (nativeRead depth) (nativeEnvironment depth) runtime
  have step : action (fieldAt runtime) = fieldAt runtime.tick.next :=
    SourceOperationRuntime.Character.successor_source (nativeRead depth) (nativeEnvironment depth) runtime
      (SourceOperationNative.Field.word (process depth))
  exact ⟨allStage_source_successor_uniformContinuous action,
    (allStage_successor_source action _).trans (congrArg allStageMap step),
    (allPrime_successor_source action _).trans (congrArg allPrimeMap step),
    (allPrime_coimage_successor_source action _).trans (congrArg ((AllPrimeKernel (L := NativeField depth ((count+1)+1))).mkQ) step),
    SourceOperationNative.Field.sourceValue_read runtime 0 ⟨0, by omega⟩,
    SourceOperationNative.Field.nextWitness_is_actual runtime 0 ⟨0, by omega⟩,
    Consumer.paid_actor_action_inverse depth count within⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
