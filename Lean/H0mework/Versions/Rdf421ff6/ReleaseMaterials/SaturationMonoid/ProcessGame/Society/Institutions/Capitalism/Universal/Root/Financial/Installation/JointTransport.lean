import H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel

/-! An actual whole-account update can change the base support while
carrying every previously admitted loan at the same registration rank. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger

universe u

variable {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
  {sourceSupport targetSupport : N.Support} {source target : law.DebtState}

def oldTransport (transport : law.TransportAt source target)
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
      exact .transferred (debtTransportReceipt sourceSupport transport) rfl rfl (Nat.le_refl _)
  | maintained anchorEq incidenceEq lineageEq responsibilityEq claimEq debit =>
      exact .maintained anchorEq incidenceEq lineageEq
        (congrArg Sum.inl responsibilityEq) (congrArg Sum.inl claimEq) debit
  | transferred receipt lineageEq claimEq budget =>
      exact .transferred (.inl receipt) lineageEq (congrArg Sum.inl claimEq) budget

def wholeTransport
    (base : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt N sourceSupport) (transport : law.TransportAt source target) :
    LedgerWriteEvolutionAt (ExtendedNetwork N law)
      (activeLedger sourceSupport source) (activeLedger targetSupport target) where
  destination := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl oldResponsibility =>
        let generated := base.destination ⟨oldResponsibility, opened⟩
        exact ⟨oldEntry (state? := some target) generated.1,
          oldTransport transport generated.2⟩
    | inr debtId =>
        rcases opened with ⟨⟨debtIdEq⟩⟩
        subst debtId
        exact ⟨debtEntry (N := N) targetSupport target,
          .transferred (debtTransportReceipt sourceSupport transport)
            (base.destination owner).2.toDebtLineage.lineage_eq rfl
            (law.transport_budget_le transport)⟩
  origin := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl oldResponsibility =>
        let generated := base.origin ⟨oldResponsibility, opened⟩
        exact ⟨oldEntry (state? := some source) generated.1,
          oldTransport transport generated.2⟩
    | inr debtId =>
        rcases opened with ⟨⟨debtIdEq⟩⟩
        subst debtId
        exact ⟨debtEntry (N := N) sourceSupport source,
          .transferred (debtTransportReceipt sourceSupport transport)
            (base.destination owner).2.toDebtLineage.lineage_eq rfl
            (law.transport_budget_le transport)⟩

theorem wholeTransport_old_destination
    (base : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt N sourceSupport) (transport : law.TransportAt source target)
    (entry : OpenResponsibilityAt N sourceSupport) :
    ((wholeTransport base owner transport).destination
      (oldEntry (law := law) (state? := some source) entry)).1 =
      oldEntry (law := law) (state? := some target) (base.destination entry).1 := rfl

theorem wholeTransport_original_debt
    (base : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt N sourceSupport) (transport : law.TransportAt source target) :
    ((wholeTransport base owner transport).destination
      (debtEntry (N := N) sourceSupport source)).1.claim =
      (debtEntry (N := N) sourceSupport source).claim := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
