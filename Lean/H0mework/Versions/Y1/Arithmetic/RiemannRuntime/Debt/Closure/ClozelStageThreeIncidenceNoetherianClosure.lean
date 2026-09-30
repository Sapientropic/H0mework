import H0mework.Versions.Y1.Arithmetic.RiemannRuntime.Debt.Runtime.ClozelStageThreeIncidenceDebtProcess

/-!
# Noetherian closure of the stage-three incidence projection debt

The receipt-generated debt is paid by the active root's exact `1 -> 0` step.
The installed phase then emits its exact local terminal, and the handoff target
contains no row with the debt's lineage and claim.  The generic Noetherian
engine therefore generates the final row receipt without a domain-local
termination table.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction.BranchNeutralDebtGate.NoetherianClosure

open DebtActivationWorld
open BranchNeutralDebtGate

noncomputable section

variable {observation : GeneratedRiemannZeroObservation}
variable {nontrivial : ¬ ∃ n : Nat,
  observation.coordinate = -2 * (n + 1)}

local notation "Law" =>
  stageThreeIncidenceProjectionDebtLaw observation nontrivial
local notation "W" =>
  StageThreeIncidenceProjectionDebtNetwork observation nontrivial

def pendingDebtEntry :
    OpenResponsibilityAt W
      (ActiveRoot.pendingSupport
        (observation := observation) (nontrivial := nontrivial)) :=
  DebtActivationWorld.debtEntry
    (N := CanonicalUnitArithmeticRoot.N) (law := Law)
    (ActiveRoot.baseSupport
      (observation := observation) (nontrivial := nontrivial))
    (StageThreeIncidenceProjectionDebtState.pending
      (observation := observation) (nontrivial := nontrivial))

def installedDebtEntry
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    OpenResponsibilityAt W (ActiveRoot.installedSupport receipt) :=
  DebtActivationWorld.debtEntry
    (N := CanonicalUnitArithmeticRoot.N) (law := Law)
    (ActiveRoot.baseSupport
      (observation := observation) (nontrivial := nontrivial))
    (StageThreeIncidenceProjectionDebtState.installed receipt)

theorem activeDebtEntry_eq_of_claim
    (state : (Law).DebtState)
    (entry : OpenResponsibilityAt W
      ⟨ActiveRoot.baseSupport
          (observation := observation) (nontrivial := nontrivial),
        some state⟩)
    (claim_eq : (.inr (Law).debtClaim) = entry.claim) :
    entry = DebtActivationWorld.debtEntry
      (N := CanonicalUnitArithmeticRoot.N) (law := Law)
      (ActiveRoot.baseSupport
        (observation := observation) (nontrivial := nontrivial)) state := by
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl oldResponsibility => exact nomatch claim_eq
  | inr debtId =>
      rcases opened with ⟨⟨debtId_eq⟩⟩
      subst debtId
      rfl

def originCurrent
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeRootDebtCurrentAt (DebtProcess.process receipt)
      (pendingDebtEntry
        (observation := observation) (nontrivial := nontrivial)) where
  state := none
  entry := pendingDebtEntry
    (observation := observation) (nontrivial := nontrivial)
  sameDebt := ⟨rfl, rfl⟩

def paymentStep
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeRootDebtStepAt (originCurrent receipt) where
  targetEntry := installedDebtEntry receipt
  evolution := by
    change LedgerEntryEvolutionAt W
      (pendingDebtEntry
        (observation := observation) (nontrivial := nontrivial))
      (installedDebtEntry receipt)
    exact (ActiveRoot.paymentEvolution receipt).destination
      (pendingDebtEntry
        (observation := observation) (nontrivial := nontrivial)) |>.2
  sameDebtTarget_unique := by
    intro alternative sameDebt
    exact activeDebtEntry_eq_of_claim
      (StageThreeIncidenceProjectionDebtState.installed receipt) alternative
      ((DebtActivationWorld.debtEntry_claim
        (N := CanonicalUnitArithmeticRoot.N) (law := Law)
        (ActiveRoot.baseSupport
          (observation := observation) (nontrivial := nontrivial))
        (StageThreeIncidenceProjectionDebtState.pending
          (observation := observation) (nontrivial := nontrivial))).symm.trans
          sameDebt.claim_eq)

def exactPayment
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeRootDebtPaymentStepAt (originCurrent receipt) where
  step := paymentStep receipt
  strictDebit := by
    exact (Law).step_budget_lt (ActiveRoot.paymentStep receipt)

def paidCurrent
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeRootDebtCurrentAt (DebtProcess.process receipt)
      (pendingDebtEntry
        (observation := observation) (nontrivial := nontrivial)) :=
  (originCurrent receipt).next (paymentStep receipt)

def onePaymentMacro
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativePaidRootDebtMacroContinuationAt (originCurrent receipt) :=
  SourceNativePaidRootDebtMacroContinuationAt.ofPayment
    .refl (exactPayment receipt) .refl

def installedExactTerminal
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceFaithfulTerminalOccurrenceAt (ActiveRoot.authoritySource receipt)
      (ActiveRoot.emitted receipt ActiveRoot.Phase.installed) where
  terminal := PUnit.unit
  structural_eq := rfl
  ledgerEvolution := (ActiveRoot.terminalPatch receipt).toLedgerTerminalEvolution
  generated_eq := rfl

theorem noDebtLineageAtInactiveTarget
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    IsEmpty (SourceNativeRootDebtTargetAt (paidCurrent receipt)) where
  false target := by
    rcases target with ⟨targetEntry, sameDebt⟩
    cases InactiveRoot.inactiveEntry_unique
      (InactiveRoot.initialBaseCurrent
        (observation := observation) (nontrivial := nontrivial)) targetEntry
    have claim_eq := sameDebt.claim_eq
    change Sum.inr (Law).debtClaim = Sum.inl PUnit.unit at claim_eq
    exact nomatch claim_eq

def paidSettlement
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeRootDebtSettlementAt (paidCurrent receipt) where
  localTerminal := installedExactTerminal receipt
  noSameDebtAtTarget := noDebtLineageAtInactiveTarget receipt

private theorem rootDebtLineage_eq
    {sourceSupport targetSupport : (W).Support}
    {source : OpenResponsibilityAt W sourceSupport}
    {target : OpenResponsibilityAt W targetSupport}
    (left right : RootDebtLineageAt W source target) :
    left = right := by
  cases left
  cases right
  rfl

inductive DebtCurrentCaseAt
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeRootDebtCurrentAt (DebtProcess.process receipt)
      (pendingDebtEntry
        (observation := observation) (nontrivial := nontrivial)) → Type
  | origin : DebtCurrentCaseAt receipt (originCurrent receipt)
  | paid : DebtCurrentCaseAt receipt (paidCurrent receipt)

def debtCurrentCase
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : SourceNativeRootDebtCurrentAt (DebtProcess.process receipt)
      (pendingDebtEntry
        (observation := observation) (nontrivial := nontrivial))) :
    DebtCurrentCaseAt receipt current := by
  rcases current with ⟨state, entry, sameDebt⟩
  cases state with
  | none =>
      have claim_eq := sameDebt.claim_eq
      change Sum.inr (Law).debtClaim = entry.claim at claim_eq
      have entry_eq := activeDebtEntry_eq_of_claim
        (StageThreeIncidenceProjectionDebtState.pending
          (observation := observation) (nontrivial := nontrivial))
        entry claim_eq
      cases entry_eq
      cases rootDebtLineage_eq sameDebt (originCurrent receipt).sameDebt
      exact .origin
  | some state =>
      cases state with
      | none =>
          have claim_eq := sameDebt.claim_eq
          change Sum.inr (Law).debtClaim = entry.claim at claim_eq
          have entry_eq := activeDebtEntry_eq_of_claim (.installed receipt)
            entry claim_eq
          cases entry_eq
          cases rootDebtLineage_eq sameDebt (paidCurrent receipt).sameDebt
          exact .paid
      | some depth =>
          have target_eq := InactiveRoot.inactiveEntry_unique
            (DebtProcess.inactiveFiniteVisit receipt depth).current entry
          cases target_eq
          have claim_eq := sameDebt.claim_eq
          change Sum.inr (Law).debtClaim = Sum.inl PUnit.unit at claim_eq
          exact nomatch claim_eq

def closureLaw
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeNoetherianDebtClosureLaw (DebtProcess.process receipt)
      (pendingDebtEntry
        (observation := observation) (nontrivial := nontrivial)) where
  emit := by
    intro current
    cases debtCurrentCase receipt current with
    | origin => exact .inr (onePaymentMacro receipt)
    | paid => exact .inl (paidSettlement receipt)

def generatedTerminalReceipt
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    Sigma fun target : SourceNativeRootDebtCurrentAt (DebtProcess.process receipt)
        (pendingDebtEntry
          (observation := observation) (nontrivial := nontrivial)) =>
      LedgerEntryTerminalAt W target.entry :=
  (closureLaw receipt).generatedReceipt (originCurrent receipt)

theorem closure_emits_exact_payment
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (closureLaw receipt).emit (originCurrent receipt) =
      .inr (onePaymentMacro receipt) :=
  rfl

theorem closure_emits_exact_settlement
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (closureLaw receipt).emit (paidCurrent receipt) =
      .inl (paidSettlement receipt) :=
  rfl

theorem generated_history_is_one_payment_then_settlement
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    Nonempty
      ((closureLaw receipt).GeneratedHistoryAt (originCurrent receipt)) :=
  ⟨(closureLaw receipt).generatedHistory (originCurrent receipt)⟩

end
end IntegralGraphJointAction.BranchNeutralDebtGate.NoetherianClosure
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.NoetherianClosure.generatedTerminalReceipt
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.NoetherianClosure.closure_emits_exact_payment
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.NoetherianClosure.closure_emits_exact_settlement
