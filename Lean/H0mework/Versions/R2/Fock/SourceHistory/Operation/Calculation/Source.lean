import H0mework.Realization.Operations.Execution.Debt.Source
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Context.Relations.Consumer

/-! The original complete paired Fock expression enters the existing executor
as raw syntax and environment; its first paid step retains the actual past. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculation

open SourceOperationEffects SourceOperationNative SourceOperationExecution
open SourceOperationInventoryLift DebtActivationWorld
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

noncomputable section

abbrev CalculationValue := Context.Value process (PairValue OperationValue)
abbrev CalculationVar := Context.Var OperationSort

def rawEnvironment (runtime : LivingRuntimeState process) : Env CalculationValue CalculationVar :=
  Context.environment (PhysicalValue := PairValue OperationValue) (point runtime)

def rawExpression : Expr CalculationValue CalculationVar (Sum.inl OperationSort.parent) :=
  Context.embed SourcePhysicalContextRelationConsumer.readPaired (liftExpr fockOperation)

def calculationLaw (runtime : LivingRuntimeState process) : DebtActivationLaw :=
  SourceOperationExecutionDebt.law (rawEnvironment runtime) rawExpression

def initial (runtime : LivingRuntimeState process) : (calculationLaw runtime).DebtState :=
  SourceOperationExecutionDebt.initial (rawEnvironment runtime) rawExpression

def disposition (runtime : LivingRuntimeState process) :=
  SourceOperationExecutionDebt.generate (rawEnvironment runtime) rawExpression (initial runtime)

theorem initial_budget (runtime : LivingRuntimeState process) :
    (calculationLaw runtime).budget (initial runtime) = 10 := rfl

private theorem initialNotSettled (runtime : LivingRuntimeState process)
    (settled : (calculationLaw runtime).SettlementAt (initial runtime)) : False := by
  have zero := (calculationLaw runtime).settlement_budget_zero settled
  rw [initial_budget] at zero
  omega

def firstStep (runtime : LivingRuntimeState process) :
    GeneratedStepAt (calculationLaw runtime) (initial runtime) :=
  match disposition runtime with
  | .inl settled => False.elim (initialNotSettled runtime settled)
  | .inr actual => actual

def paidState (runtime : LivingRuntimeState process) : (calculationLaw runtime).DebtState :=
  (firstStep runtime).1

theorem firstStep_generated (runtime : LivingRuntimeState process) :
    disposition runtime = .inr (firstStep runtime) := by
  cases generatedEq : disposition runtime with
  | inl settled => exact False.elim (initialNotSettled runtime settled)
  | inr actual => simp only [firstStep, generatedEq]

private theorem actualDebit (runtime : LivingRuntimeState process)
    {before after : (calculationLaw runtime).DebtState}
    (actual : (calculationLaw runtime).StepAt before after) :
    (calculationLaw runtime).budget before = (calculationLaw runtime).budget after + 1 := by
  change SourceOperationExecutionDebt.Advance (rawEnvironment runtime) rawExpression
    before after at actual
  cases actual with
  | paid primitive => exact SourceOperationExecution.Step.remaining_eq primitive

theorem firstStep_debit (runtime : LivingRuntimeState process) :
    (calculationLaw runtime).budget (initial runtime) =
      (calculationLaw runtime).budget (paidState runtime) + 1 :=
  actualDebit runtime (firstStep runtime).2

theorem paid_budget (runtime : LivingRuntimeState process) :
    (calculationLaw runtime).budget (paidState runtime) = 9 := by
  have debit := firstStep_debit runtime
  rw [initial_budget] at debit
  omega

end
end SourcePhysicalCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
