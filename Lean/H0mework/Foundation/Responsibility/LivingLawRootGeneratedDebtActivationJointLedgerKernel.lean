import H0mework.Foundation.Responsibility.DebtLedger

/-! The original complete base write and an actual debt step jointly update
both support and activation state. The base owner generates the debt lineage. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace DebtActivationLedger

open DebtActivationWorld

universe u

variable {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
  {sourceSupport targetSupport : N.Support}
  {source target : law.DebtState}

/-- A joint step retains the original old-row receipt. Only a base carry uses
the actual debt step receipt to account for the changed activation coordinate. -/
def jointOldEvolution (step : law.StepAt source target)
    {sourceEntry : OpenResponsibilityAt N sourceSupport}
    {targetEntry : OpenResponsibilityAt N targetSupport}
    (evolution : LedgerEntryEvolutionAt N sourceEntry targetEntry) :
    LedgerEntryEvolutionAt (ExtendedNetwork N law)
      (oldEntry (law := law) (state? := some source) sourceEntry)
      (oldEntry (law := law) (state? := some target) targetEntry) := by
  cases evolution with
  | carried supportEq entryEq =>
      cases supportEq
      cases entryEq
      exact .transferred (debtStepReceipt sourceSupport step) rfl rfl (Nat.le_refl _)
  | maintained anchorEq incidenceEq lineageEq responsibilityEq claimEq debit =>
      exact .maintained anchorEq incidenceEq lineageEq
        (congrArg Sum.inl responsibilityEq) (congrArg Sum.inl claimEq) debit
  | transferred receipt lineageEq claimEq budget =>
      exact .transferred (.inl receipt) lineageEq (congrArg Sum.inl claimEq) budget

/-- The source owner supplies lineage through its actual generated destination;
no target lineage equation is accepted. -/
def jointStepLedgerEvolution
    (base : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt N sourceSupport)
    (step : law.StepAt source target) :
    LedgerWriteEvolutionAt (ExtendedNetwork N law)
      (activeLedger sourceSupport source) (activeLedger targetSupport target) where
  destination := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl oldResponsibility =>
        let generated := base.destination ⟨oldResponsibility, opened⟩
        exact ⟨oldEntry (state? := some target) generated.1,
          jointOldEvolution step generated.2⟩
    | inr debtId =>
        rcases opened with ⟨⟨debtIdEq⟩⟩
        subst debtId
        exact ⟨debtEntry (N := N) targetSupport target,
          .transferred (debtStepReceipt sourceSupport step)
            (base.destination owner).2.toDebtLineage.lineage_eq rfl
            (Nat.le_of_lt (law.step_budget_lt step))⟩
  origin := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl oldResponsibility =>
        let generated := base.origin ⟨oldResponsibility, opened⟩
        exact ⟨oldEntry (state? := some source) generated.1,
          jointOldEvolution step generated.2⟩
    | inr debtId =>
        rcases opened with ⟨⟨debtIdEq⟩⟩
        subst debtId
        exact ⟨debtEntry (N := N) sourceSupport source,
          .transferred (debtStepReceipt sourceSupport step)
            (base.destination owner).2.toDebtLineage.lineage_eq rfl
            (Nat.le_of_lt (law.step_budget_lt step))⟩

variable (base : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨targetSupport⟩)
  (owner : OpenResponsibilityAt N sourceSupport) (step : law.StepAt source target)

@[simp] theorem jointStepLedgerEvolution_destination_old
    (entry : OpenResponsibilityAt N sourceSupport) :
    ((jointStepLedgerEvolution base owner step).destination
      (oldEntry (law := law) (state? := some source) entry)).1 =
        oldEntry (law := law) (state? := some target) (base.destination entry).1 := rfl

@[simp] theorem jointStepLedgerEvolution_origin_old
    (entry : OpenResponsibilityAt N targetSupport) :
    ((jointStepLedgerEvolution base owner step).origin
      (oldEntry (law := law) (state? := some target) entry)).1 =
        oldEntry (law := law) (state? := some source) (base.origin entry).1 := rfl

theorem jointStepLedgerEvolution_destination_old_evolution
    (entry : OpenResponsibilityAt N sourceSupport) :
    HEq ((jointStepLedgerEvolution base owner step).destination
      (oldEntry (law := law) (state? := some source) entry)).2
        (jointOldEvolution step (base.destination entry).2) := HEq.rfl

theorem jointStepLedgerEvolution_origin_old_evolution
    (entry : OpenResponsibilityAt N targetSupport) :
    HEq ((jointStepLedgerEvolution base owner step).origin
      (oldEntry (law := law) (state? := some target) entry)).2
        (jointOldEvolution step (base.origin entry).2) := HEq.rfl

@[simp] theorem jointStepLedgerEvolution_destination_debt :
    ((jointStepLedgerEvolution base owner step).destination
      (debtEntry (N := N) sourceSupport source)).1 =
        debtEntry (N := N) targetSupport target := rfl

@[simp] theorem jointStepLedgerEvolution_origin_debt :
    ((jointStepLedgerEvolution base owner step).origin
      (debtEntry (N := N) targetSupport target)).1 =
        debtEntry (N := N) sourceSupport source := rfl

theorem jointStepLedgerEvolution_debt_strict :
    ((jointStepLedgerEvolution base owner step).destination
      (debtEntry (N := N) sourceSupport source)).1.progressBudget <
      (debtEntry (N := N) sourceSupport source).progressBudget :=
  law.step_budget_lt step

def jointStepLedgerEvolution_debt_sameDebt
    (base : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt N sourceSupport) (step : law.StepAt source target) :
    RootDebtLineageAt (ExtendedNetwork N law)
      (debtEntry (N := N) sourceSupport source)
      (debtEntry (N := N) targetSupport target) :=
  ((jointStepLedgerEvolution base owner step).destination
    (debtEntry (N := N) sourceSupport source)).2.toDebtLineage

theorem jointStepLedgerEvolution_destination_debt_evolution :
    HEq ((jointStepLedgerEvolution base owner step).destination
      (debtEntry (N := N) sourceSupport source)).2
      (.transferred (debtStepReceipt sourceSupport step)
        (base.destination owner).2.toDebtLineage.lineage_eq rfl
        (Nat.le_of_lt (law.step_budget_lt step)) :
        LedgerEntryEvolutionAt (ExtendedNetwork N law)
          (debtEntry (N := N) sourceSupport source)
          (debtEntry (N := N) targetSupport target)) := HEq.rfl

theorem jointOldEvolution_transferred
    {sourceEntry : OpenResponsibilityAt N sourceSupport}
    {targetEntry : OpenResponsibilityAt N targetSupport}
    (receipt : N.DispositionAt sourceSupport .transfer)
    (lineageEq : N.lineageAt sourceSupport = N.lineageAt targetSupport)
    (claimEq : sourceEntry.claim = targetEntry.claim)
    (budget : targetEntry.progressBudget ≤ sourceEntry.progressBudget) :
    jointOldEvolution step
        (.transferred receipt lineageEq claimEq budget :
          LedgerEntryEvolutionAt N sourceEntry targetEntry) =
      .transferred (.inl receipt) lineageEq (congrArg Sum.inl claimEq) budget := rfl

end DebtActivationLedger
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
