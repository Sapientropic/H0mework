import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.SplitAction
import H0mework.Versions.R40942a5b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologySuccessor

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open CofinalAllPrimeTopology

namespace NativeRecovery
export RootGeneratedDebtActivationJointSource.OwnerFree.Native (backward backward_source previous_runtime successor_injective)
end NativeRecovery

local notation "A" => fun depth => SourceOperationNative.sourceAction (process depth)
local notation "B" => fun depth => NativeRecovery.backward (R.old depth) (R.origin depth) (R.reader depth)
private def initialState (depth : Nat) : (process depth).State :=
  (C.mathRuntime depth 0).state

def initialCoefficient (depth : Nat) : FullCarrier depth →ₗ[ℤ] ℤ :=
  Finsupp.lapply (initialState depth)

def initialInclusion (depth : Nat) : ℤ →ₗ[ℤ] FullCarrier depth :=
  Finsupp.lsingle (initialState depth)

theorem initial_coefficient_inclusion (depth : Nat) (value : ℤ) :
    initialCoefficient depth (initialInclusion depth value) = value :=
  Finsupp.single_eq_same

private theorem initial_outside_native_successor (depth : Nat) :
    initialState depth ∉ Set.range (process depth).successor := by
  rintro ⟨prior, same⟩
  have addresses := congrArg ULift.down same
  change prior.down+1 = 0 at addresses
  omega

theorem actual_native_action_initial_coefficient (depth : Nat) (word : FullCarrier depth) :
    initialCoefficient depth (A depth word) = 0 :=
  Finsupp.mapDomain_of_notMem_range word (initialState depth) (initial_outside_native_successor depth)

/-- The source shift and its native backward leave exactly the actual initial coordinate. -/
theorem actual_native_action_decomposition (depth : Nat) (word : FullCarrier depth) :
    A depth (B depth word)+initialInclusion depth (initialCoefficient depth word) = word := by
  apply Finsupp.ext
  intro state
  rw [Finsupp.add_apply]
  by_cases initial : state = initialState depth
  · rw [initial]
    have absent : (A depth (B depth word)) (initialState depth) = 0 :=
      actual_native_action_initial_coefficient depth (B depth word)
    rw [absent, zero_add]
    exact Finsupp.single_eq_same
  · have nonzero : state.down ≠ 0 := by
      intro zero
      apply initial
      exact ULift.ext _ _ zero
    let prior : (process depth).State := ULift.up (state.down-1)
    have comesFrom : (process depth).successor prior = state := by
      apply ULift.ext
      change state.down-1+1 = state.down
      omega
    have invisible : initialInclusion depth (initialCoefficient depth word) state = 0 :=
      Finsupp.single_eq_of_ne initial
    rw [invisible, add_zero, ← comesFrom]
    change Finsupp.mapDomain (process depth).successor (B depth word) ((process depth).successor prior) = _
    rw [Finsupp.mapDomain_apply (NativeRecovery.successor_injective (R.old depth) (R.origin depth) (R.reader depth))]
    unfold RootGeneratedDebtActivationJointSource.OwnerFree.Native.backward
    rw [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]

theorem actual_native_topology_left_inverse (depth : Nat) :
    Function.LeftInverse (allStageSuccessor (B depth)) (allStageSuccessor (A depth)) ∧
    Function.LeftInverse (allPrimeSuccessor (B depth)) (allPrimeSuccessor (A depth)) ∧
    Function.LeftInverse (allPrimeCoimageSuccessor (B depth)) (allPrimeCoimageSuccessor (A depth)) :=
  topology_successor_left_inverse (A depth) (B depth)
    (NativeRecovery.backward_source (R.old depth) (R.origin depth) (R.reader depth))

/-- The backward operation recovers the same full native source point of the paid pulse. -/
theorem actual_actor_topology_inverse (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    let runtime := C.mathRuntime depth (count+1)
    let current := SourceOperationNative.point runtime
    let next := SourceOperationNative.point runtime.tick.next
    allStageSuccessor (B depth) (allStageMap next) = allStageMap current ∧
    allPrimeSuccessor (B depth) (allPrimeMap next) = allPrimeMap current ∧
    allPrimeCoimageSuccessor (B depth) ((AllPrimeKernel (L := FullCarrier depth)).mkQ next) =
      (AllPrimeKernel (L := FullCarrier depth)).mkQ current ∧
    type_of% (actual_actor_topology_successor depth count within) ∧
    type_of% (SourceOperationNative.point_factorizes runtime) := by
  dsimp only
  let runtime := C.mathRuntime depth (count+1)
  have back := NativeRecovery.previous_runtime (R.old depth) (R.origin depth) (R.reader depth) runtime
  exact ⟨(allStage_successor_source (B depth) _).trans (congrArg allStageMap back),
    (allPrime_successor_source (B depth) _).trans (congrArg allPrimeMap back),
    (allPrime_coimage_successor_source (B depth) _).trans (congrArg (AllPrimeKernel (L := FullCarrier depth)).mkQ back),
    actual_actor_topology_successor depth count within, SourceOperationNative.point_factorizes runtime⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
