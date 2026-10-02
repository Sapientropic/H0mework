import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer
import H0mework.Foundation.Responsibility.JointSource.Compiler

/-! Raw input is read from the actual inquiry actor before observation.
The second request consumes this source at the completed depth nine. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation

open SourceOperationEffects SourceOperationNative SourceOperationExecution
open DebtActivationWorld DebtActivationLedger
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

noncomputable section
variable (runtime : LivingRuntimeState process) (depth : Nat)

abbrev lower := (targetRoot runtime).toAuthoritativeRoot.toLedgerRoot
def current := mathCurrent runtime depth
def occurrence := (lower runtime).emitted (current runtime depth)

def originalOccurrence
    (source : (lower runtime).source.source.toRootSource.actual.OccurrenceAt (current runtime depth)) :=
  Joint.originalOccurrence (SourcePhysicalCalculationAdmission.registered runtime) source

def physicalActive
    (source : (lower runtime).source.source.toRootSource.actual.OccurrenceAt (current runtime depth)) :
    projectionLaw.ActiveAt PUnit.unit (originalOccurrence runtime depth source) :=
  ⟨by
    change 1 ≤ scanIndex (mathCurrent runtime depth).1
    rw [Consumer.current_original]
    exact (activeAt (runtime.advance (depth + 1))).down⟩

def physicalPayload
    (source : (lower runtime).source.source.toRootSource.actual.OccurrenceAt (current runtime depth)) :=
  projectionLaw.project PUnit.unit (originalOccurrence runtime depth source) (physicalActive runtime depth source)

def physicalPair
    (source : (lower runtime).source.source.toRootSource.actual.OccurrenceAt (current runtime depth)) :
    ParentCarrier × ParentCarrier :=
  ((physicalPayload runtime depth source).sourceState, (physicalPayload runtime depth source).forcedTrace)

def rawEnvironment : Env SourcePhysicalCalculation.CalculationValue SourcePhysicalCalculation.CalculationVar :=
  Context.environment (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
    (statePoint process (scanIndex (current runtime depth).1 - 1))

private theorem actualScan (actual : LivingRuntimeState process) :
    scanIndex (SourcePhysicalCalculation.baseCurrent actual) = actual.state + 1 := by
  change scanIndex (NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.finiteVisit actual.state).current = _
  rw [finiteVisit_current]
  exact ArithmeticGeneration.UnitHistory.cardinalShadow_generate _

theorem rawEnvironment_actual : rawEnvironment runtime depth = Consumer.physicalEnvironment runtime depth := by
  change Context.environment (statePoint process (scanIndex (mathCurrent runtime depth).1 - 1)) =
    Context.environment (statePoint process (runtime.advance (depth + 1)).state)
  rw [Consumer.current_original, actualScan]
  rfl

theorem physicalPair_actual : physicalPair runtime depth (occurrence runtime depth) = Consumer.physicalPair runtime depth := rfl

theorem raw_value : SourcePhysicalCalculation.rawExpression.eval (rawEnvironment runtime depth) =
    physicalPair runtime depth (occurrence runtime depth) := by
  rw [rawEnvironment_actual, physicalPair_actual]
  exact Consumer.current_pair_read runtime depth

def reader
    (source : (lower runtime).source.source.toRootSource.actual.OccurrenceAt (current runtime depth)) :
    RootGeneratedDebtActivationJointSource.RawInputAt
      (Value := SourcePhysicalCalculation.CalculationValue) (Var := SourcePhysicalCalculation.CalculationVar)
      (sort := Sum.inl OperationSort.parent) (lower runtime) (current runtime depth) source := by
  rcases source with ⟨support, event⟩
  cases event
  exact { environment := rawEnvironment runtime depth
          expression := SourcePhysicalCalculation.rawExpression
          owner := mathEntry runtime depth }

def registered := RootGeneratedDebtActivationJointSource.register (reader runtime depth)
def initialEvent := RootGeneratedDebtActivationJointSource.initialEvent (registered runtime depth)

theorem registered_environment : (registered runtime depth).input.environment = rawEnvironment runtime depth := rfl
theorem registered_expression : (registered runtime depth).input.expression = SourcePhysicalCalculation.rawExpression := rfl
theorem registered_owner : (registered runtime depth).input.owner = mathEntry runtime depth := rfl

def oldHistory : (SourcePhysicalCalculation.calculationLaw runtime).DebtState := (current runtime depth).2.state

theorem oldHistory_actual : oldHistory runtime depth = Consumer.history runtime depth := rfl
theorem oldHistory_budget : remaining (oldHistory runtime depth).1 = 10 - (depth + 1) := Consumer.budget_eq runtime depth
theorem initial_budget : remaining (initialEvent runtime depth).state.1 = 10 := rfl

private theorem notSettled
    (settled : SourceOperationExecutionDebt.Settlement (initialEvent runtime depth).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.law (registered runtime depth)).settlement_budget_zero settled
  change remaining (initialEvent runtime depth).state.1 = 0 at zero
  rw [initial_budget] at zero
  omega

def firstStep : GeneratedStepAt (RootGeneratedDebtActivationJointSource.law (registered runtime depth))
    (initialEvent runtime depth).state :=
  match RootGeneratedDebtActivationJointSource.mathAction (initialEvent runtime depth) with
  | .inl settled => False.elim (notSettled runtime depth settled)
  | .inr actual => actual

theorem firstStep_generated : RootGeneratedDebtActivationJointSource.mathAction (initialEvent runtime depth) =
    .inr (firstStep runtime depth) := by
  cases equation : RootGeneratedDebtActivationJointSource.mathAction (initialEvent runtime depth) with
  | inl settled => exact False.elim (notSettled runtime depth settled)
  | inr actual => simp only [firstStep, equation]

private theorem stepDebit {environment : Env SourcePhysicalCalculation.CalculationValue
    SourcePhysicalCalculation.CalculationVar}
    {expression : Expr SourcePhysicalCalculation.CalculationValue SourcePhysicalCalculation.CalculationVar
      (Sum.inl OperationSort.parent)}
    {before after : SourceOperationExecutionDebt.State environment expression}
    (actual : SourceOperationExecutionDebt.Advance environment expression before after) :
    remaining before.1 = remaining after.1 + 1 := by
  cases actual with
  | paid primitive => exact SourceOperationExecution.Step.remaining_eq primitive

theorem firstStep_debit : remaining (initialEvent runtime depth).state.1 =
    remaining (firstStep runtime depth).1.1 + 1 := stepDebit (firstStep runtime depth).2

theorem firstStep_budget : remaining (firstStep runtime depth).1.1 = 9 := by
  have debit := firstStep_debit runtime depth
  rw [initial_budget] at debit
  omega

theorem firstStep_value : (firstStep runtime depth).1.1.eval (registered runtime depth).input.environment =
    physicalPair runtime depth (occurrence runtime depth) :=
  (firstStep runtime depth).1.2.sound.symm.trans (raw_value runtime depth)

end
end SourcePhysicalCalculationAdmission.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
