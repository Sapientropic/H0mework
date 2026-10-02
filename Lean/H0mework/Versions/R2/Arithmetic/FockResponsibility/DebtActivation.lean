import H0mework.Foundation.Responsibility.DebtWorldReadback
import H0mework.Versions.R2.Arithmetic.FockResponsibility.OccurrenceSector

/-!
# Occurrence-sensitive Goldbach debt activation law

The complete factor-process occurrence, remaining finite observer inventory,
strict payment, actual phase terminal and projection recurrence are installed
in one generic debt law.  A key-absent event remains the exact U7 obstruction.
It is not reclassified as a same-debt transport: this law therefore leaves the
optional transport fibre empty.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockOccurrenceDebtActivation

open DebtActivationWorld
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open ParticleWaveFockAtomicProcess
open ParticleWaveFockOccurrenceResponsibility

noncomputable section

noncomputable local instance structuralKeyDecidableEq (index : Nat) :
    DecidableEq (FactorDecayStructuralChannelKeyAt index) :=
  Classical.decEq _

def budget {index : Nat}
    (state : ParticleWaveFockOccurrenceResponsibility.State index) : Nat :=
  match generateDynamics state.1.physicalCurrent with
  | .terminal _generated _species => 0
  | .step _generated _effect => state.2.card

theorem strictPayment_budget_lt {index : Nat}
    {source target : ParticleWaveFockOccurrenceResponsibility.State index}
    (payment : StrictPaymentAt source target) :
    budget target < budget source := by
  unfold budget
  rw [payment.actual.dynamics_eq]
  cases target_dynamics :
      generateDynamics target.1.physicalCurrent with
  | terminal generated species =>
      exact Finset.card_pos.mpr
        ⟨payment.structuralKey, payment.present⟩
  | step generated effect =>
      have target_inventory_eq :
          target.2 = source.2.erase payment.structuralKey :=
        congrArg Prod.snd payment.target_eq
      rw [target_inventory_eq]
      exact Finset.card_erase_lt_of_mem payment.present

theorem terminal_budget_zero {index : Nat}
    {state : ParticleWaveFockOccurrenceResponsibility.State index}
    (terminal : TerminalAt state) : budget state = 0 := by
  unfold budget
  rw [terminal.dynamics_eq]

inductive DebtId
  | occurrenceFactorProcess

inductive DebtClaim
  | accountOccurrenceFactorProcess

/-- Complete occurrence-sensitive debt law. -/
def activationLaw (index : Nat) : DebtActivationLaw where
  DebtState := ParticleWaveFockOccurrenceResponsibility.State index
  DebtId := DebtId
  DebtClaim := DebtClaim
  debtId := .occurrenceFactorProcess
  debtClaim := .accountOccurrenceFactorProcess
  budget := budget
  StepAt := StrictPaymentAt
  step_budget_lt := strictPayment_budget_lt
  SettlementAt := TerminalAt
  settlement_budget_zero := terminal_budget_zero
  supportTerminalLaw? := some
    { EventAt := TerminalAt
      settles := id }
  ObstructionAt := ProjectionRecurrenceResidualAt

/-- Goldbach recurrence remains a U7 obstruction.  The optional generic
transport family is deliberately absent, so no target state can be minted from
this residual by an equal-budget transport receipt. -/
theorem transportAt_isEmpty (index : Nat)
    (source target : (activationLaw index).DebtState) :
    IsEmpty ((activationLaw index).TransportAt source target) :=
  ⟨fun transport => nomatch transport⟩

abbrev ActivatedNetwork (index : Nat)
    (BaseN : WorldRelationNetwork) :=
  DebtActivationWorld.ExtendedNetwork BaseN (activationLaw index)

/-- Debt-law view of the occurrence compiler's three branches. -/
def toDebtDisposition {index : Nat}
    {state : (activationLaw index).DebtState} :
    ParticleWaveFockOccurrenceResponsibility.GeneratedDispositionAt state →
    (activationLaw index).SettlementAt state ⊕
      (DebtActivationWorld.GeneratedStepAt (activationLaw index) state ⊕
        (activationLaw index).ObstructionAt state)
  | .terminal settled => .inl settled
  | .payment paid => .inr (.inl ⟨_, paid⟩)
  | .projectionRecurrence residual => .inr (.inr residual)

/-- The occurrence compiler and debt law consume the same generated value. -/
def generatedDisposition {index : Nat}
    (state : (activationLaw index).DebtState) :
    (activationLaw index).SettlementAt state ⊕
      (DebtActivationWorld.GeneratedStepAt (activationLaw index) state ⊕
        (activationLaw index).ObstructionAt state) :=
  toDebtDisposition
    (ParticleWaveFockOccurrenceResponsibility.generateDisposition state)

theorem generatedDisposition_eq_obstruction_of_eq {index : Nat}
    {state : (activationLaw index).DebtState}
    {residual : ProjectionRecurrenceResidualAt state}
    (disposition_eq :
      ParticleWaveFockOccurrenceResponsibility.generateDisposition state =
        .projectionRecurrence residual) :
    generatedDisposition state = .inr (.inr residual) := by
  rw [generatedDisposition, disposition_eq]
  rfl

end

end ParticleWaveFockOccurrenceDebtActivation
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
