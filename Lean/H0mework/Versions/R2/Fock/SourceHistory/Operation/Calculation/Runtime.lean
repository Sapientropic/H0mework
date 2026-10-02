import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Completion
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Registered

/-! The complete original Fock pair is consumed after actual canonical ticks of its registered source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationRootConsumer

open SourceOperationEffects SourceOperationExecution
open RootGeneratedDebtActivationJointSource
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

noncomputable section

def initial (runtime : LivingRuntimeState process) :=
  Unit.initialRuntime (SourcePhysicalCalculationRegistered.registered runtime)

theorem initial_budget (runtime : LivingRuntimeState process) :
    Unit.runtimeBudget (SourcePhysicalCalculationRegistered.registered runtime) (initial runtime) = 10 := rfl

theorem first_tick_budget (runtime : LivingRuntimeState process) :
    Unit.runtimeBudget (SourcePhysicalCalculationRegistered.registered runtime) (initial runtime).tick.next = 9 := by
  rw [Unit.runtimeBudget_tick (SourcePhysicalCalculationRegistered.registered runtime) (initial runtime),
    initial_budget runtime]

theorem first_tick_original (runtime : LivingRuntimeState process) :
    (Unit.runtimeCurrent (SourcePhysicalCalculationRegistered.registered runtime) (initial runtime).tick.next).1 =
      SourcePhysicalCalculation.baseCurrent runtime.tick.next := rfl

def completed (runtime : LivingRuntimeState process) :=
  Unit.completed (SourcePhysicalCalculationRegistered.registered runtime) (initial runtime)

theorem completed_pair (runtime : LivingRuntimeState process) :
    (completed runtime).1 = ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
  (Unit.completed_source_value (SourcePhysicalCalculationRegistered.registered runtime)
    (initial runtime)).trans (SourcePhysicalCalculation.raw_value runtime)

theorem completion_is_ten_ticks (runtime : LivingRuntimeState process) :
    Unit.completionRuntime (SourcePhysicalCalculationRegistered.registered runtime) (initial runtime) =
      (initial runtime).advance 10 := by
  change (initial runtime).advance
      (Unit.runtimeBudget (SourcePhysicalCalculationRegistered.registered runtime) (initial runtime)) =
    (initial runtime).advance 10
  rw [initial_budget runtime]

theorem ten_ticks_budget_zero (runtime : LivingRuntimeState process) :
    Unit.runtimeBudget (SourcePhysicalCalculationRegistered.registered runtime) ((initial runtime).advance 10) = 0 := by
  rw [Unit.runtimeBudget_advance (SourcePhysicalCalculationRegistered.registered runtime) (initial runtime) 10,
    initial_budget runtime]

theorem completed_next_keeps_paid_state (runtime : LivingRuntimeState process) :
    (Unit.runtimeCurrent (SourcePhysicalCalculationRegistered.registered runtime)
      ((initial runtime).advance 10).tick.next).2.state =
    (Unit.runtimeCurrent (SourcePhysicalCalculationRegistered.registered runtime)
      ((initial runtime).advance 10)).2.state := by
  rw [← completion_is_ten_ticks]
  exact Unit.completed_next_state _ _

end
end SourcePhysicalCalculationRootConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
