import H0mework.Foundation.Responsibility.DebtLedger

/-!
# Readback for complete debt-activation ledger evolution

These equations expose both directions of the total whole-ledger evolution,
the common terminal receipt, and the exact old-row/debt-row separation at the
inactive face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DebtActivationLedger

open DebtActivationWorld

universe u

variable {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}

@[simp]
theorem stepLedgerEvolution_destination_old
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target)
    (entry : OpenResponsibilityAt N support) :
    ((stepLedgerEvolution support step).destination
      (oldEntry (law := law) (state? := some source) entry)).1 =
        oldEntry (law := law) (state? := some target) entry := by
  rfl

/-- The old-row destination is carried by the source step's actual transfer
receipt, not by finite omission or definitional carry. -/
theorem stepLedgerEvolution_destination_old_evolution
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target)
    (entry : OpenResponsibilityAt N support) :
    HEq
      ((stepLedgerEvolution support step).destination
        (oldEntry (law := law) (state? := some source) entry)).2
      (.transferred (debtStepReceipt support step) rfl rfl
          (Nat.le_refl entry.progressBudget) :
        LedgerEntryEvolutionAt (ExtendedNetwork N law)
          (oldEntry (law := law) (state? := some source) entry)
          (oldEntry (law := law) (state? := some target) entry)) := by
  rfl

@[simp]
theorem stepLedgerEvolution_origin_old
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target)
    (entry : OpenResponsibilityAt N support) :
    ((stepLedgerEvolution support step).origin
      (oldEntry (law := law) (state? := some target) entry)).1 =
        oldEntry (law := law) (state? := some source) entry := by
  rfl

@[simp]
theorem stepLedgerEvolution_destination_debt
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target) :
    ((stepLedgerEvolution support step).destination
      (debtEntry (N := N) support source)).1 =
        debtEntry (N := N) support target := by
  rfl

/-- The unique debt row consumes the strict maintenance constructor generated
by the same source step. -/
theorem stepLedgerEvolution_destination_debt_evolution
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target) :
    HEq
      ((stepLedgerEvolution support step).destination
        (debtEntry (N := N) support source)).2
      (.maintained rfl rfl rfl rfl rfl (law.step_budget_lt step) :
        LedgerEntryEvolutionAt (ExtendedNetwork N law)
          (debtEntry (N := N) support source)
          (debtEntry (N := N) support target)) := by
  rfl

@[simp]
theorem stepLedgerEvolution_origin_debt
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target) :
    ((stepLedgerEvolution support step).origin
      (debtEntry (N := N) support target)).1 =
        debtEntry (N := N) support source := by
  rfl

/-- Destination followed by origin returns every source entry, including an
arbitrary proof-relevant old row and the unique debt row. -/
theorem stepLedgerEvolution_origin_destination
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target)
    (entry : (activeLedger support source).Entry) :
    ((stepLedgerEvolution support step).origin
      ((stepLedgerEvolution support step).destination entry).1).1 = entry := by
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl oldResponsibility => rfl
  | inr debtId =>
      rcases opened with ⟨⟨debtId_eq⟩⟩
      subst debtId
      rfl

/-- Origin followed by destination returns every target entry. -/
theorem stepLedgerEvolution_destination_origin
    (support : N.Support) {source target : law.DebtState}
    (step : law.StepAt source target)
    (entry : (activeLedger support target).Entry) :
    ((stepLedgerEvolution support step).destination
      ((stepLedgerEvolution support step).origin entry).1).1 = entry := by
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl oldResponsibility => rfl
  | inr debtId =>
      rcases opened with ⟨⟨debtId_eq⟩⟩
      subst debtId
      rfl

@[simp]
theorem transportLedgerEvolution_destination_old
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target)
    (entry : OpenResponsibilityAt N support) :
    ((transportLedgerEvolution support transport).destination
      (oldEntry (law := law) (state? := some source) entry)).1 =
        oldEntry (law := law) (state? := some target) entry := by
  rfl

/-- Every inherited row consumes the same actual transport receipt as the
debt row; transport is not a definitional carry between changed supports. -/
theorem transportLedgerEvolution_destination_old_evolution
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target)
    (entry : OpenResponsibilityAt N support) :
    HEq
      ((transportLedgerEvolution support transport).destination
        (oldEntry (law := law) (state? := some source) entry)).2
      (.transferred (debtTransportReceipt support transport) rfl rfl
          (Nat.le_refl entry.progressBudget) :
        LedgerEntryEvolutionAt (ExtendedNetwork N law)
          (oldEntry (law := law) (state? := some source) entry)
          (oldEntry (law := law) (state? := some target) entry)) := by
  rfl

@[simp]
theorem transportLedgerEvolution_origin_old
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target)
    (entry : OpenResponsibilityAt N support) :
    ((transportLedgerEvolution support transport).origin
      (oldEntry (law := law) (state? := some target) entry)).1 =
        oldEntry (law := law) (state? := some source) entry := by
  rfl

@[simp]
theorem transportLedgerEvolution_destination_debt
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target) :
    ((transportLedgerEvolution support transport).destination
      (debtEntry (N := N) support source)).1 =
        debtEntry (N := N) support target := by
  rfl

/-- The debt row is transported with its exact lineage and the law-generated
non-refill inequality; no strict payment is fabricated. -/
theorem transportLedgerEvolution_destination_debt_evolution
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target) :
    HEq
      ((transportLedgerEvolution support transport).destination
        (debtEntry (N := N) support source)).2
      (.transferred (debtTransportReceipt support transport) rfl rfl
          (law.transport_budget_le transport) :
        LedgerEntryEvolutionAt (ExtendedNetwork N law)
          (debtEntry (N := N) support source)
          (debtEntry (N := N) support target)) := by
  rfl

@[simp]
theorem transportLedgerEvolution_origin_debt
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target) :
    ((transportLedgerEvolution support transport).origin
      (debtEntry (N := N) support target)).1 =
        debtEntry (N := N) support source := by
  rfl

/-- The transport accounts for every source row in both directions. -/
theorem transportLedgerEvolution_origin_destination
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target)
    (entry : (activeLedger support source).Entry) :
    ((transportLedgerEvolution support transport).origin
      ((transportLedgerEvolution support transport).destination entry).1).1 =
        entry := by
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl oldResponsibility => rfl
  | inr debtId =>
      rcases opened with ⟨⟨debtId_eq⟩⟩
      subst debtId
      rfl

/-- The transport also accounts for every generated target row. -/
theorem transportLedgerEvolution_destination_origin
    (support : N.Support) {source target : law.DebtState}
    (transport : law.TransportAt source target)
    (entry : (activeLedger support target).Entry) :
    ((transportLedgerEvolution support transport).destination
      ((transportLedgerEvolution support transport).origin entry).1).1 =
        entry := by
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl oldResponsibility => rfl
  | inr debtId =>
      rcases opened with ⟨⟨debtId_eq⟩⟩
      subst debtId
      rfl

@[simp]
theorem settlementLedgerEvolution_receipt
    (support : N.Support) {state : law.DebtState}
    (settlement : law.SettlementAt state)
    (baseReceipt : N.DispositionAt support .supportSettlement)
    (entry : (activeLedger support state).Entry) :
    ((settlementLedgerEvolution support settlement baseReceipt).discharge
      entry).receipt =
        baseSettlementReceipt (law := law) (state? := some state)
          support baseReceipt :=
  rfl

@[simp]
theorem supportTerminalLedgerEvolution_receipt
    (support : N.Support) {state : law.DebtState}
    (terminal : law.SupportTerminalAt state)
    (entry : (activeLedger support state).Entry) :
    ((supportTerminalLedgerEvolution support terminal).discharge
      entry).receipt =
        debtSupportTerminalReceipt support terminal :=
  rfl

/-- Every inactive target row is literally an inherited old row. -/
def inactiveEntryOldOrigin
    (support : N.Support)
    (entry : (inactiveLedger (law := law) support).Entry) :
    Sigma fun old : OpenResponsibilityAt N support =>
      PLift (entry = oldEntry (law := law) (state? := none) old) := by
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl oldResponsibility =>
      exact ⟨⟨oldResponsibility, opened⟩, ⟨rfl⟩⟩
  | inr debtId => exact nomatch opened

/-- Every inactive row has its faithful old-row origin at every active state. -/
def inactiveRowActiveOrigin
    (support : N.Support) (state : law.DebtState)
    (entry : (inactiveLedger (law := law) support).Entry) :
    Sigma fun sourceEntry : (activeLedger support state).Entry =>
      RootDebtLineageAt (ExtendedNetwork N law) sourceEntry entry := by
  rcases inactiveEntryOldOrigin (law := law) support entry with
    ⟨old, ⟨entry_eq⟩⟩
  cases entry_eq
  exact ⟨oldEntry (law := law) (state? := some state) old, ⟨rfl, rfl⟩⟩

/-- The tracked debt has no same-lineage target on the inactive face. -/
theorem debt_noSameDebtAtInactive
    (support : N.Support) (state : law.DebtState) :
    ¬ Nonempty
      (Sigma fun targetEntry : (inactiveLedger (law := law) support).Entry =>
        RootDebtLineageAt (ExtendedNetwork N law)
          (debtEntry (N := N) support state) targetEntry) := by
  rintro ⟨witness⟩
  exact (by
    rcases witness with ⟨⟨responsibility, opened⟩, sameDebt⟩
    cases responsibility with
    | inl oldResponsibility => exact nomatch sameDebt.claim_eq
    | inr debtId => exact nomatch opened)

/-- Deactivation cannot launder the tracked debt through a different base
support.  Every inactive target still lies in the inherited claim summand, so
the active debt claim has no same-lineage target anywhere on that face. -/
theorem debt_noSameDebtAtAnyInactive
    (sourceSupport targetSupport : N.Support) (state : law.DebtState) :
    ¬ Nonempty
      (Sigma fun targetEntry : (inactiveLedger (law := law) targetSupport).Entry =>
        RootDebtLineageAt (ExtendedNetwork N law)
          (debtEntry (N := N) sourceSupport state) targetEntry) := by
  rintro ⟨witness⟩
  rcases witness with ⟨⟨responsibility, opened⟩, sameDebt⟩
  cases responsibility with
  | inl _ => exact nomatch sameDebt.claim_eq
  | inr _ => exact nomatch opened

end DebtActivationLedger
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
