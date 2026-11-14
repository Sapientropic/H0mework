import H0mework.Versions.R1db039f7.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Morphism
import H0mework.Versions.R1db039f7.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Native
import H0mework.Versions.R1db039f7.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Consumer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyTrace

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations SourceOperationScalarRelations
open SourceGeneratedPrimePowerCompletion

namespace Paid
export RootGeneratedDebtActivationJointSource.OwnerFree (raw runtimeCurrent cofinal_active_tick_words)
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion (budget)
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value_source)
end Paid

private abbrev calculation (depth : Nat) := Paid.raw (R.old depth) (R.origin depth) (R.reader depth)

/-- The original paid continuation appends exactly one original word and its coherent interpretation. -/
theorem actual_actor_cofinal_paid_tick (depth count : Nat)
    (within : count < sourceFuel (R.source depth (emitted depth))) (p : Nat.Primes) :
    let runtime := C.mathRuntime depth (count+1)
    let prior := (Paid.runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).2
    let next := (Paid.runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime.tick.next).2
    let old := (calculation depth).environment
    let increment := R.actualIncrement depth
    ∃ word, words next = words prior ++ [word] ∧
      words (SourceOperationCompletion.trace p next) = words (SourceOperationCompletion.trace p prior) ++
        [SourceOperationCompletion.wordMap p Unit.unit word] ∧
      updateInventory (R := ℤ) (SourceOperationCompletion.environment p old)
          (SourceOperationCompletion.environment p increment) (SourceOperationCompletion.wordMap p Unit.unit word) =
        (canonicalLinearMap p (evaluation (R := ℤ) old word),
          canonicalLinearMap p (effectEvaluator (R := ℤ) old increment word)) ∧
      type_of% (Consumer.paid_actor_action_inverse depth count within) := by
  let runtime := C.mathRuntime depth (count+1)
  have active : 0 < SourceOperationExecution.remaining (Paid.runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).1 := by
    have budget := Paid.budget (R.old depth) (R.origin depth) (R.reader depth) (count+1)
    change SourceOperationExecution.remaining (Paid.runtimeCurrent (R.old depth) (R.origin depth) (R.reader depth) runtime).1 =
      SourceOperationExecution.remaining (sourceProgramme (R.index depth) (R.active depth) (emitted depth)) - (count+1) at budget
    rw [sourceProgramme_budget] at budget
    change count < sourceFuel (sourceAt (R.index depth) (R.active depth) (emitted depth)) at within
    omega
  obtain ⟨word, actual, completed⟩ :=
    Paid.cofinal_active_tick_words (R.old depth) (R.origin depth) (R.reader depth) runtime p active
  exact ⟨word, actual, completed,
    SourceOperationCompletion.inventory_read p (calculation depth).environment (R.actualIncrement depth) word,
    Consumer.paid_actor_action_inverse depth count within⟩

/-- The completed original history keeps every paid step and reads the original independent outcome. -/
theorem actual_actor_cofinal_terminal (depth : Nat) (p : Nat.Primes) :
    let raw := calculation depth
    let paid := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace (R.old depth) (R.origin depth) (R.reader depth)
    (SourceOperationCompletion.trace p paid).length = sourceFuel (R.source depth (emitted depth)) + 1 ∧
      (SourceOperationCompletion.expression p raw.expression).eval (SourceOperationCompletion.environment p raw.environment) =
        canonicalLinearMap p (Registered.calculatedValue depth) ∧
      type_of% (Registered.consumes_original_disposition depth) := by
  let raw := calculation depth
  let paid := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace (R.old depth) (R.origin depth) (R.reader depth)
  exact ⟨(SourceOperationCompletion.trace_length p paid).trans (Registered.receipt depth).1,
    (SourceOperationCompletion.expression_eval p raw.expression raw.environment).trans
      (congrArg (canonicalLinearMap p) (Paid.value_source (R.old depth) (R.origin depth) (R.reader depth)).symm),
    Registered.consumes_original_disposition depth⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyTrace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
