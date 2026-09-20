import H0mework.Foundation.Inquiry.EmptyObstruction
import H0mework.Foundation.Responsibility.DebtCompiler
import H0mework.Foundation.Responsibility.DebtPositiveRoot
import H0mework.Arithmetic.FockResponsibility.TargetSixProcessAction

/-!
# Target-six action-owned actuality debt

Only the closed target-six action receives a one-step actuality debt.  The
step constructor has no caller field: it denotes the fixed compiled `2+4 →
3+3` action.  Its target terminal readout then generates the additive fibre,
nonzero occupation, settlement, and support terminal.

No generic action is declared paid or terminal by this file, and the old
runtime successor is not consumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityTargetSixActionDebt

open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open DebtActivationLedger
open DebtActivationWorld
open ParticleWaveFockOccurrenceResponsibilityRuntime
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDirect
open ParticleWaveFockPrimePairActualityProcessAction
open ParticleWaveFockPrimePairActualityTargetSixProcessAction
open RootGeneratedDebtActivationDirect
open RootGeneratedDebtActivationDirectPositive
open RootGeneratedEmptyObstructionU7

noncomputable section

abbrev action : GeneratedActionReceiptAt 1 := targetSixActionReceipt

abbrev terminalReadout : TerminalReadoutAt action :=
  targetSixTerminalReadout

inductive State
  | open
  | paid
  deriving DecidableEq

def budget : State → Nat
  | .open => 1
  | .paid => 0

/-- The sole strict step is the fixed source-generated target-six action. -/
inductive StepAt : State → State → Type
  | generated : StepAt .open .paid

namespace StepAt

def actionReceipt {source target : State} (_step : StepAt source target) :
    GeneratedActionReceiptAt 1 :=
  action

def targetTerminalReadout {source target : State}
    (_step : StepAt source target) : TerminalReadoutAt action :=
  terminalReadout

def effectiveFibre {source target : State} (step : StepAt source target) :=
  step.targetTerminalReadout.effectiveFibre

def actualitySettlement {source target : State} (step : StepAt source target) :
    PrimePairActualitySettlementAt (directRuntimeActuality 1) :=
  step.targetTerminalReadout.actualitySettlement

theorem occupation_ne_zero {source target : State}
    (step : StepAt source target) :
    (directRuntimeActuality 1).occupation ≠ 0 :=
  step.targetTerminalReadout.occupation_ne_zero

theorem source_eq_open {source target : State}
    (step : StepAt source target) : source = .open := by
  cases step
  rfl

theorem target_eq_paid {source target : State}
    (step : StepAt source target) : target = .paid := by
  cases step
  rfl

theorem budget_lt {source target : State}
    (step : StepAt source target) : budget target < budget source := by
  cases step
  exact Nat.zero_lt_one

end StepAt

/-- Terminality is downstream of the fixed action step. -/
inductive SettlementAt : State → Type
  | generated : SettlementAt .paid

namespace SettlementAt

def terminalReadout {state : State} (_settled : SettlementAt state) :
    TerminalReadoutAt action :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.terminalReadout

def actualitySettlement {state : State} (settled : SettlementAt state) :
    PrimePairActualitySettlementAt (directRuntimeActuality 1) :=
  settled.terminalReadout.actualitySettlement

theorem occupation_ne_zero {state : State} (settled : SettlementAt state) :
    (directRuntimeActuality 1).occupation ≠ 0 :=
  settled.terminalReadout.occupation_ne_zero

theorem budget_zero {state : State}
    (settled : SettlementAt state) : budget state = 0 := by
  cases settled
  rfl

end SettlementAt

inductive DebtId
  | primePairActionActuality

def law : DebtActivationLaw where
  DebtState := State
  DebtId := DebtId
  DebtClaim := PrimePairActualityClaimAt
    (directRuntimeActuality 1).exactEvenOccurrence
  debtId := .primePairActionActuality
  debtClaim := (directRuntimeActuality 1).claim
  budget := budget
  StepAt := StepAt
  step_budget_lt := StepAt.budget_lt
  transportLaw? := none
  SettlementAt := SettlementAt
  settlement_budget_zero := SettlementAt.budget_zero
  supportTerminalLaw? := some
    { EventAt := SettlementAt
      settles := id }
  ObstructionAt := fun _ => PEmpty

theorem transportAt_isEmpty (source target : law.DebtState) :
    IsEmpty (law.TransportAt source target) :=
  ⟨fun transport => nomatch transport⟩

abbrev LowerRoot :=
  ParticleWaveFockOccurrenceResponsibilityRuntime.authoritativeRoot.toLedgerRoot

abbrev LowerCurrent :=
  (ParticleWaveFockOccurrenceResponsibilityRuntime.runtimeAt 1
    ).current.visit.current

/-- Singleton source event exposing exactly the fixed target-six action. -/
abbrev ActionEvent := {generated : GeneratedActionReceiptAt 1 // generated = action}

def source : OccurrenceIndexedSourceAt LowerRoot LowerCurrent where
  Event := ActionEvent
  generate := ⟨action, rfl⟩
  lawAt := fun _ => law
  stateAt := fun _ => State.open
  dispositionAt := fun _ => .step StepAt.generated

abbrev Activation := source
abbrev Law := law
abbrev targetState : Law.DebtState := State.paid
abbrev payment : Law.StepAt State.open targetState := StepAt.generated
abbrev terminal : Law.SupportTerminalAt targetState := SettlementAt.generated

@[simp] theorem sourceDisposition_is_step :
    Activation.generatedDisposition = .step payment :=
  rfl

def oldU7 : U7ProducerCalculus CanonicalUnitArithmeticRoot.N :=
  RootGeneratedEmptyObstructionU7.producer _ rootObstructionAt_isEmpty

def oldU7Calculus : U7ObstructionEvolutionCalculus
    CanonicalUnitArithmeticRoot.N oldU7 :=
  RootGeneratedEmptyObstructionU7.calculus _ rootObstructionAt_isEmpty

def compiled :=
  RootGeneratedDebtActivationDirect.compile source oldU7 oldU7Calculus

def wholeLedgerStep :
    LedgerWriteEvolutionAt Activation.World Activation.liveLedger
      (activeLedger Activation.lowerSupport targetState) := by
  have result := compiled.result
  rw [compiled.generated_eq, sourceDisposition_is_step] at result
  exact result

def targetSixWholeLedgerTerminal :
    LedgerTerminalEvolutionAt Activation.World
      (activeLedger Activation.lowerSupport targetState) :=
  supportTerminalLedgerEvolution Activation.lowerSupport terminal

theorem liveDebtEntry_claim :
    Activation.liveDebtEntry.claim =
      .inr (directRuntimeActuality 1).claim :=
  rfl

theorem liveDebtEntry_budget :
    Activation.liveDebtEntry.progressBudget = 1 :=
  rfl

/-- The action-owned source is attached to the exact occurrence that emitted
the target-six actuality face, not merely to the same structural target. -/
theorem lowerOccurrence_eq_actualitySource :
    Activation.lowerOccurrence =
      (directRuntimeActuality 1).sourceOccurrence :=
  (directRuntimeActuality 1).sourceOccurrence_eq.symm

theorem targetSixStrictDebit :
    (debtEntry (N := CanonicalUnitArithmeticRoot.N)
        Activation.lowerSupport targetState).progressBudget <
      Activation.liveDebtEntry.progressBudget :=
  debtStep_budget_lt Activation.lowerSupport payment

/-- The generic positive root consumes the action-owned debt step. -/
def positive : GeneratedPositiveAt Activation :=
  GeneratedPositiveAt.ofGenerated payment sourceDisposition_is_step terminal

/-- Hostile: the paid state cannot mint another action step. -/
theorem paidState_has_no_step (target : State) :
    IsEmpty (StepAt .paid target) :=
  ⟨fun step => nomatch step⟩

/-- Direct target-six chain with no settlement premise. -/
theorem actionStep_terminalReadout_fibre_settlement :
    payment.actionReceipt = action ∧
      Nonempty (EffectiveAdditiveFibreAt
        (ParticleWaveFockAtomicDebtRuntime.RuntimeIndex 1)) ∧
      Nonempty (PrimePairActualitySettlementAt (directRuntimeActuality 1)) ∧
      (directRuntimeActuality 1).occupation ≠ 0 :=
  ⟨rfl, ⟨payment.effectiveFibre⟩,
    ⟨payment.actualitySettlement⟩, payment.occupation_ne_zero⟩

/-- The exact Fourier sibling reads nonvanishing from the action step's
generated settlement; the coefficient is not stored in the step. -/
theorem actionStep_fourierCoefficient_ne_zero :
    ParticleWaveFockRuntimeExactPrimeFourierSibling.runtimePrimeOnlyFourierCoefficient
      1 ≠ 0 :=
  (ParticleWaveFockPrimePairActualityDirect.directRuntimeSettlement_nonempty_iff_fourier_nonzero
    1).mp ⟨payment.actualitySettlement⟩

end


end ParticleWaveFockPrimePairActualityTargetSixActionDebt
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
