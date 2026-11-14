import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Native
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyTrace

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open SourceOperationExecution

namespace Paid
export RootGeneratedDebtActivationJointSource.OwnerFree
  (runtimeCurrent cofinal_tick_terminal_extension cofinal_tick_completion)
export RootGeneratedDebtActivationJointSource.OwnerFree.Relations (history)
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion (budget)
end Paid

private theorem actor_active (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) :
    0 < remaining (Paid.runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) (C.mathRuntime depth (count+1))).1 := by
  have budget := Paid.budget (R.old depth) (R.origin depth) (R.reader depth) (count+1)
  change remaining (Paid.runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) (C.mathRuntime depth (count+1))).1 =
    remaining (sourceProgramme (R.index depth) (R.active depth) (emitted depth)) - (count+1) at budget
  rw [sourceProgramme_budget] at budget
  change count < sourceFuel (sourceAt (R.index depth) (R.active depth) (emitted depth)) at within
  omega

/-- The actual fixed-target actor feeds the complete continuation square and its fresh payment. -/
theorem actual_actor_cofinal_continuation (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) (p : Nat.Primes) :
    let runtime := C.mathRuntime depth (count+1)
    type_of% (Paid.cofinal_tick_terminal_extension (R.old depth) (R.origin depth) (R.reader depth) runtime
      (actor_active depth count within)) ∧
      (∀ value : (Paid.history (R.old depth) (R.origin depth) (R.reader depth) runtime).CompletionCarrier,
        type_of% (Paid.cofinal_tick_completion (R.old depth) (R.origin depth) (R.reader depth) runtime p value)) ∧
      type_of% (Consumer.paid_actor_action_inverse depth count within) := by
  let runtime := C.mathRuntime depth (count+1)
  exact ⟨Paid.cofinal_tick_terminal_extension (R.old depth) (R.origin depth) (R.reader depth) runtime
    (actor_active depth count within),
    Paid.cofinal_tick_completion (R.old depth) (R.origin depth) (R.reader depth) runtime p,
    Consumer.paid_actor_action_inverse depth count within⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyContinuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
