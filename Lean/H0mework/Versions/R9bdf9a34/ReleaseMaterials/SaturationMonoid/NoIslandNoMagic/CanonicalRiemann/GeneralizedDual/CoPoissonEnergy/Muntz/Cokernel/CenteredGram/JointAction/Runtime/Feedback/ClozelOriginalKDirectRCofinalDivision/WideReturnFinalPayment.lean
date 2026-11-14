import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Derived
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Step
import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualReturnConsumer

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 170000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationPaidRelations RootGeneratedDebtActivationJointSource.OwnerFree

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "authority" => OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth ordinal
local notation "origin" => OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth ordinal
local notation "read" => reader observation nontrivial half depth ordinal

private theorem source_budget (n m : Nat) :
    remaining (raw authority origin (read n m)).expression = 4+m :=
  (Eval.paid_history authority origin (read n m)).symm.trans
    (paid_steps observation nontrivial half depth ordinal n m)

def beforeWrite (n m : Nat) : Runtime authority origin (read n m) :=
  Completion.runtime authority origin (read n m) (3+m)

local notation "prior" => beforeWrite observation nontrivial half depth ordinal

theorem final_credit (n m : Nat) :
    remaining (runtimeCurrent authority origin (read n m) (prior n m)).1 = 1 := by
  let input := read n m
  have budget := Completion.budget authority origin input (3+m)
  change remaining (runtimeCurrent authority origin input (prior n m)).1 =
    remaining (raw authority origin input).expression - (3+m) at budget
  exact budget.trans ((congrArg (· - (3+m))
    (source_budget observation nontrivial half depth ordinal n m)).trans (by omega))

theorem final_write_settles (n m : Nat) :
    runtimeCurrent authority origin (read n m) (prior n m).tick.next =
      Consumer.targetState authority origin (read n m) := by
  let input := read n m
  have emitted : (prior n m).tick.next = Completion.runtime authority origin input ((3+m)+1) := rfl
  have count : (3+m)+1 = remaining (raw authority origin input).expression :=
    (by omega : (3+m)+1 = 4+m).trans
      (source_budget observation nontrivial half depth ordinal n m).symm
  exact (congrArg (runtimeCurrent authority origin input) emitted).trans
    ((congrArg (Completion.state authority origin input) count).trans
      (Calculation.target_state authority origin input).symm)

/-- The literal final R write contributes its one new relation edge to the installed history. -/
theorem final_relation_word (n m : Nat) :
    let runtime := prior n m
    let old := runtimeCurrent authority origin (read n m) runtime
    let next := Consumer.targetState authority origin (read n m)
    words next.2 = words old.2 ++ [Finsupp.single old.1 1-Finsupp.single next.1 1] := by
  let runtime := prior n m
  let input := read n m
  let old := runtimeCurrent authority origin input runtime
  let next := runtimeCurrent authority origin input runtime.tick.next
  have active : 0 < remaining old.1 :=
    (final_credit observation nontrivial half depth ordinal n m).symm ▸ Nat.zero_lt_one
  have word := active_tick_terminal_relation authority origin input runtime active
  let claim := fun after : Current authority origin input =>
    words after.2 = words old.2 ++ [Finsupp.single old.1 1-Finsupp.single after.1 1]
  exact (congrArg claim (final_write_settles observation nontrivial half depth ordinal n m)).mp word

private def lastIndex (n m : Nat) : Fin (words (Eval.trace authority origin (read n m))).length :=
  ⟨3+m, by
    rw [complete_steps, paid_steps observation nontrivial half depth ordinal n m]
    omega⟩

/-- The final charge retains its address in the actual completed calculation. -/
def lastOccurrence (n m : Nat) :=
  stepOccurrence (Eval.trace authority origin (read n m))
    (lastIndex observation nontrivial half depth ordinal n m)

theorem last_occurrence_address (n m : Nat) :
    (lastOccurrence observation nontrivial half depth ordinal n m).before.length = 4+m :=
  (stepOccurrence_before_length _ _).trans (by
    change 1+(3+m) = 4+m
    omega)

def lastDebit (n m : Nat) :=
  Payment.activePayment authority origin (read n m)
    ⟨3+m, (source_budget observation nontrivial half depth ordinal n m).symm ▸
      (by omega : 3+m < 4+m)⟩

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_final_relation_and_payment"

/-- The same final occurrence generates its cofinal derived write and the strictly debited original row. -/
theorem actual_final_relation_and_payment (n m : Nat) :
    type_of% (final_relation_word observation nontrivial half depth ordinal n m) ∧
    type_of% (last_occurrence_address observation nontrivial half depth ordinal n m) ∧
    type_of% (cofinal_tick_derived_write authority origin (read n m) (prior n m)) ∧
    type_of% (cofinal_tick_terminal_extension authority origin (read n m) (prior n m)
      ((final_credit observation nontrivial half depth ordinal n m).symm ▸ Nat.zero_lt_one)) ∧
    type_of% ((lastDebit observation nontrivial half depth ordinal n m).strictDebit) ∧
    type_of% (Payment.wellFounded authority origin (read n m)) ∧
    type_of% (final_write_settles observation nontrivial half depth ordinal n m) :=
  ⟨final_relation_word observation nontrivial half depth ordinal n m,
    last_occurrence_address observation nontrivial half depth ordinal n m,
    cofinal_tick_derived_write authority origin (read n m) (prior n m),
    cofinal_tick_terminal_extension authority origin (read n m) (prior n m)
      ((final_credit observation nontrivial half depth ordinal n m).symm ▸ Nat.zero_lt_one),
    (lastDebit observation nontrivial half depth ordinal n m).strictDebit,
    Payment.wellFounded authority origin (read n m),
    final_write_settles observation nontrivial half depth ordinal n m⟩

end WideResidualReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
