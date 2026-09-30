import H0mework.Realization.Audit.DebtFirstWrite
import H0mework.Versions.Y1.Arithmetic.RiemannRuntime.Debt.Effect.ClozelStageThreeIncidencePaymentReceipt

/-!
# Branch-neutral admission of the stage-three incidence debt

The debt law is fixed by the neutral receipt root, not by an off-center bit.
Its only strict step carries the root-generated stage-three incidence receipt.
The total source disposition either keeps the existing critical terminal or
generates a fresh debt row together with its first `1 -> 0` whole-ledger
payment.  The law also exposes an installed-state phase-terminal event; it
becomes authoritative only when a later root compiler installs it together
with a handoff that preserves every inherited canonical row.  It is not an RH
terminal and does not discharge the arithmetic world.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction.BranchNeutralDebtGate

open CanonicalUnitArithmeticRoot
open DebtActivationWorld
open DebtAdmissionFirstWrite
open A1cEnergySupportReceiptRoot

noncomputable section

/-- The admitted claim is fixed before the root chooses its outcome.  Exact
root provenance remains in the paying receipt rather than inflating this row
identifier. -/
inductive StageThreeIncidenceProjectionDebtClaimAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1))
  | accountRootStageThreeIncidence

def stageThreeIncidenceProjectionDebtClaim
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    StageThreeIncidenceProjectionDebtClaimAt observation nontrivial :=
  .accountRootStageThreeIncidence

inductive StageThreeIncidenceProjectionDebtId
  | rootStageThreeIncidence

/-- The installed state retains the exact paying receipt. -/
inductive StageThreeIncidenceProjectionDebtState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : Type
  | pending
  | installed
      (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)

def stageThreeIncidenceProjectionDebtBudget
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)} :
    StageThreeIncidenceProjectionDebtState observation nontrivial → Nat
  | .pending => 1
  | .installed _ => 0

/-- No caller supplies a target or a strictness proof: the target embeds the
actual receipt emitted by the neutral root. -/
inductive StageThreeIncidenceProjectionDebtStepAt
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)} :
    StageThreeIncidenceProjectionDebtState observation nontrivial →
      StageThreeIncidenceProjectionDebtState observation nontrivial → Type
  | install (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
      StageThreeIncidenceProjectionDebtStepAt .pending (.installed receipt)

theorem stageThreeIncidenceProjectionDebtStep_budget_lt
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    {source target :
      StageThreeIncidenceProjectionDebtState observation nontrivial}
    (step : StageThreeIncidenceProjectionDebtStepAt source target) :
    stageThreeIncidenceProjectionDebtBudget target <
      stageThreeIncidenceProjectionDebtBudget source := by
  cases step
  exact Nat.zero_lt_succ 0

/-- Local settlement of the projection obligation.  It carries no arithmetic
world terminal by itself; the law below only exposes it as a phase event for a
later root compiler whose handoff must preserve every inherited row. -/
inductive StageThreeIncidenceProjectionDebtSettlementAt
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)} :
    StageThreeIncidenceProjectionDebtState observation nontrivial → Type
  | installed
      (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
      StageThreeIncidenceProjectionDebtSettlementAt (.installed receipt)

theorem stageThreeIncidenceProjectionDebtSettlement_budget_zero
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    {state : StageThreeIncidenceProjectionDebtState observation nontrivial}
    (settlement : StageThreeIncidenceProjectionDebtSettlementAt state) :
    stageThreeIncidenceProjectionDebtBudget state = 0 := by
  cases settlement
  rfl

/-- One neutral law for both outcomes.  Only a generated negative receipt can
inhabit its strict-step fibre. -/
def stageThreeIncidenceProjectionDebtLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : DebtActivationLaw where
  DebtState := StageThreeIncidenceProjectionDebtState observation nontrivial
  DebtId := StageThreeIncidenceProjectionDebtId
  DebtClaim := StageThreeIncidenceProjectionDebtClaimAt observation nontrivial
  debtId := .rootStageThreeIncidence
  debtClaim := stageThreeIncidenceProjectionDebtClaim observation nontrivial
  budget := stageThreeIncidenceProjectionDebtBudget
  StepAt := StageThreeIncidenceProjectionDebtStepAt
  step_budget_lt := stageThreeIncidenceProjectionDebtStep_budget_lt
  SettlementAt := StageThreeIncidenceProjectionDebtSettlementAt
  settlement_budget_zero :=
    stageThreeIncidenceProjectionDebtSettlement_budget_zero
  supportTerminalLaw? := some
    { EventAt := StageThreeIncidenceProjectionDebtSettlementAt
      settles := id }
  ObstructionAt := fun _ => PEmpty

abbrev StageThreeIncidenceProjectionDebtNetwork
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :=
  ExtendedNetwork N
    (stageThreeIncidenceProjectionDebtLaw observation nontrivial)

def stageThreeIncidenceProjectionSupport
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : N.Support :=
  (sourceEvent observation nontrivial).occurrence.1

def stageThreeIncidenceAdmissionEvent
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceFixedDebtAdmissionEventAt
      (stageThreeIncidenceProjectionDebtLaw observation nontrivial)
      .pending :=
  SourceFixedDebtAdmissionEventAt.ofStep
    (StageThreeIncidenceProjectionDebtStepAt.install receipt)

def generatedStageThreeIncidenceAdmission
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceGeneratedDebtAdmissionFirstWriteAt
      (N := N)
      (law := stageThreeIncidenceProjectionDebtLaw observation nontrivial)
      (stageThreeIncidenceProjectionSupport observation nontrivial)
      (stageThreeIncidenceAdmissionEvent receipt) :=
  DebtAdmissionFirstWrite.generate
    (N := N)
    (law := stageThreeIncidenceProjectionDebtLaw observation nontrivial)
    (stageThreeIncidenceProjectionSupport observation nontrivial)
    (stageThreeIncidenceAdmissionEvent receipt)

/-- Consumer-ready fresh row and first payment, retaining the exact root
effect receipt which justified admission. -/
structure RootGeneratedStageThreeIncidenceFirstWriteAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : Type where
  private mk ::
  receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial

namespace RootGeneratedStageThreeIncidenceFirstWriteAt

def admission
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (generated : RootGeneratedStageThreeIncidenceFirstWriteAt
      observation nontrivial) : SourceGeneratedDebtAdmissionFirstWriteAt
    (N := N)
    (law := stageThreeIncidenceProjectionDebtLaw observation nontrivial)
    (stageThreeIncidenceProjectionSupport observation nontrivial)
    (stageThreeIncidenceAdmissionEvent generated.receipt) :=
  generatedStageThreeIncidenceAdmission generated.receipt

@[simp] theorem claim_is_neutral_root_claim
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (generated : RootGeneratedStageThreeIncidenceFirstWriteAt
      observation nontrivial) :
    generated.admission.initialEntry.claim =
      .inr (stageThreeIncidenceProjectionDebtClaim observation nontrivial)
    := rfl

def fresh
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (generated : RootGeneratedStageThreeIncidenceFirstWriteAt
      observation nontrivial) : RootDebtFreshAt
    (StageThreeIncidenceProjectionDebtNetwork observation nontrivial)
    ⟨stageThreeIncidenceProjectionSupport observation nontrivial, none⟩
    generated.admission.initialEntry :=
  generated.admission.fresh

theorem first_payment_strict
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (generated : RootGeneratedStageThreeIncidenceFirstWriteAt
      observation nontrivial) :
    generated.admission.paidEntry.progressBudget <
      generated.admission.initialEntry.progressBudget :=
  generated.admission.firstPayment_budget_strict

theorem first_payment_destination
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (generated : RootGeneratedStageThreeIncidenceFirstWriteAt
      observation nontrivial) :
    (generated.admission.firstPayment.destination
      generated.admission.initialEntry).1 =
        generated.admission.paidEntry :=
  generated.admission.firstPayment_destination_debt

def local_projection_settlement
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (generated : RootGeneratedStageThreeIncidenceFirstWriteAt
      observation nontrivial) :
    (stageThreeIncidenceProjectionDebtLaw observation nontrivial).SettlementAt
      (.installed generated.receipt) :=
  StageThreeIncidenceProjectionDebtSettlementAt.installed generated.receipt

end RootGeneratedStageThreeIncidenceFirstWriteAt

private def firstWriteOfReceipt
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)}
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    RootGeneratedStageThreeIncidenceFirstWriteAt observation nontrivial := by
  exact { receipt := receipt }

/-- Branch-neutral source entry: either the existing critical consumer, or
the exact fresh admission and strict first payment. -/
inductive StageThreeIncidenceAdmissionDispositionAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) : Type where
  | supported (outcome : SupportedAt observation nontrivial)
  | firstWrite
      (generated : RootGeneratedStageThreeIncidenceFirstWriteAt
        observation nontrivial)

def generateStageThreeIncidenceAdmissionDisposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    StageThreeIncidenceAdmissionDispositionAt observation nontrivial :=
  match generateStageThreeProjectionDisposition observation nontrivial with
  | .supported outcome => .supported outcome
  | .payment receipt => .firstWrite (firstWriteOfReceipt receipt)

/-- A critical occurrence cannot mint the debt law's first strict event. -/
theorem no_stageThreeIncidenceProjectionStep_of_critical
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1))
    (critical : observation.coordinate.re = 1 / 2)
    (target : (stageThreeIncidenceProjectionDebtLaw
      observation nontrivial).DebtState) :
    IsEmpty ((stageThreeIncidenceProjectionDebtLaw observation nontrivial).StepAt
      .pending target) where
  false step := by
    cases step with
    | install receipt =>
        exact (no_stageThreeIncidencePaymentReceipt_of_critical
          observation nontrivial critical).false receipt

/-- The ordinary old-origin ABI still cannot manufacture the fresh row. -/
theorem ordinary_root_evolution_cannot_replace_stageThree_admission
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    ¬ Nonempty
      (LedgerWriteEvolutionAt
        (StageThreeIncidenceProjectionDebtNetwork observation nontrivial)
        (DebtActivationLedger.inactiveLedger
          (N := N)
          (law := stageThreeIncidenceProjectionDebtLaw observation nontrivial)
          (stageThreeIncidenceProjectionSupport observation nontrivial))
        (DebtActivationLedger.activeLedger
          (N := N)
          (law := stageThreeIncidenceProjectionDebtLaw observation nontrivial)
          (stageThreeIncidenceProjectionSupport observation nontrivial)
          .pending)) :=
  ordinaryEvolution_cannot_admit
    (N := N)
    (law := stageThreeIncidenceProjectionDebtLaw observation nontrivial)
    (stageThreeIncidenceProjectionSupport observation nontrivial) .pending

end
end IntegralGraphJointAction.BranchNeutralDebtGate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.generateStageThreeIncidenceAdmissionDisposition
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.ordinary_root_evolution_cannot_replace_stageThree_admission
