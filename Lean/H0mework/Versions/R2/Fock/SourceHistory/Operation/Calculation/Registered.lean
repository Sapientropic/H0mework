import H0mework.Foundation.Responsibility.JointSource.Compiler
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Consumer

/-! Raw source input is registered before the event. The original compiler
then generates the native successor, mathematical first step and joint payer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationRegistered

open SourceOperationEffects SourceOperationNative SourcePhysicalCalculation
open DebtActivationWorld DebtActivationLedger
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

noncomputable section

abbrev lower := livingRoot.toAuthoritativeRoot.toLedgerRoot

def reader (runtime : LivingRuntimeState process)
    (occurrence : lower.source.source.toRootSource.actual.OccurrenceAt (baseCurrent runtime)) :
    RootGeneratedDebtActivationJointSource.RawInputAt
      (Value := CalculationValue) (Var := CalculationVar) (sort := Sum.inl OperationSort.parent)
      lower (baseCurrent runtime) occurrence where
  environment := rawEnvironment runtime
  expression := rawExpression
  owner := CanonicalUnitArithmeticRoot.occurrenceLedgerEntry occurrence

def registered (runtime : LivingRuntimeState process) :=
  RootGeneratedDebtActivationJointSource.register (reader runtime)

def initialEvent (runtime : LivingRuntimeState process) :=
  RootGeneratedDebtActivationJointSource.initialEvent (registered runtime)

theorem registered_environment (runtime : LivingRuntimeState process) :
    (registered runtime).input.environment = rawEnvironment runtime := rfl

theorem registered_expression (runtime : LivingRuntimeState process) :
    (registered runtime).input.expression = rawExpression := rfl

theorem registered_owner (runtime : LivingRuntimeState process) :
    (registered runtime).input.owner = CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime) := rfl

theorem registered_occurrence (runtime : LivingRuntimeState process) :
    lower.emitted (baseCurrent runtime) = runtime.emittedOccurrence :=
  (original_occurrence runtime).symm

theorem initial_state (runtime : LivingRuntimeState process) :
    (initialEvent runtime).state = initial runtime := rfl

theorem initial_mathAction (runtime : LivingRuntimeState process) :
    RootGeneratedDebtActivationJointSource.mathAction (initialEvent runtime) = .inr (firstStep runtime) :=
  firstStep_generated runtime

def native (runtime : LivingRuntimeState process) :
    RootGeneratedDebtActivationJointSource.NativeAt (initialEvent runtime) :=
  (RootGeneratedDebtActivationJointSource.compileNative? (initialEvent runtime)).get (by rfl)

theorem native_generated (runtime : LivingRuntimeState process) :
    RootGeneratedDebtActivationJointSource.compileNative? (initialEvent runtime) = some (native runtime) := rfl

theorem native_next (runtime : LivingRuntimeState process) :
    CanonicalUnitArithmeticRoot.V.nativeTarget (native runtime).write = baseCurrent runtime.tick.next := rfl

theorem native_next_state (runtime : LivingRuntimeState process) :
    (native runtime).nextEvent.state = paidState runtime := rfl

theorem native_next_owner (runtime : LivingRuntimeState process) :
    (native runtime).nextEvent.owner =
      CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime.tick.next) := rfl

def worldLaw (runtime : LivingRuntimeState process) : DebtActivationLaw :=
  RootGeneratedDebtActivationJointSource.Idle.law (rawEnvironment runtime) rawExpression

def payer (runtime : LivingRuntimeState process) :
    LedgerWriteEvolutionAt (ExtendedNetwork CanonicalUnitArithmeticRoot.N (worldLaw runtime))
      (activeLedger (baseCurrent runtime) (initial runtime))
      (activeLedger (baseCurrent runtime.tick.next) (paidState runtime)) :=
  RootGeneratedDebtActivationJointSource.payment (native runtime)

theorem native_base (runtime : LivingRuntimeState process) :
    (native runtime).baseLedger = wholeBase runtime := rfl

theorem payer_generated (runtime : LivingRuntimeState process) :
    payer runtime = jointStepLedgerEvolution
      (law := worldLaw runtime) (wholeBase runtime)
      (CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime)) (firstStep runtime).2 := rfl

theorem payer_math_destination (runtime : LivingRuntimeState process) :
    ((payer runtime).destination
      (debtEntry (N := CanonicalUnitArithmeticRoot.N) (law := worldLaw runtime)
        (baseCurrent runtime) (initial runtime))).1 =
      debtEntry (N := CanonicalUnitArithmeticRoot.N) (law := worldLaw runtime)
        (baseCurrent runtime.tick.next) (paidState runtime) := rfl

theorem payer_math_strict (runtime : LivingRuntimeState process) :
    ((payer runtime).destination
      (debtEntry (N := CanonicalUnitArithmeticRoot.N) (law := worldLaw runtime)
        (baseCurrent runtime) (initial runtime))).1.progressBudget <
      (debtEntry (N := CanonicalUnitArithmeticRoot.N) (law := worldLaw runtime)
        (baseCurrent runtime) (initial runtime)).progressBudget :=
  jointStepLedgerEvolution_debt_strict (law := worldLaw runtime) (wholeBase runtime)
    (CanonicalUnitArithmeticRoot.rootLedgerEntry (baseCurrent runtime)) (firstStep runtime).2

theorem payer_old_destination (runtime : LivingRuntimeState process)
    (entry : OpenResponsibilityAt CanonicalUnitArithmeticRoot.N (baseCurrent runtime)) :
    ((payer runtime).destination
      (oldEntry (law := worldLaw runtime) (state? := some (initial runtime)) entry)).1 =
      oldEntry (law := worldLaw runtime) (state? := some (paidState runtime))
        (wholeBase runtime |>.destination entry).1 := rfl

theorem native_next_budget (runtime : LivingRuntimeState process) :
    (worldLaw runtime).budget (initialEvent runtime).state = 10 ∧
      (worldLaw runtime).budget (native runtime).nextEvent.state = 9 :=
  ⟨initial_budget runtime, paid_budget runtime⟩

end
end SourcePhysicalCalculationRegistered
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
