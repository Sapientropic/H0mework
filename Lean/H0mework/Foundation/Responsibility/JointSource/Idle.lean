import H0mework.Realization.Operations.Execution.Debt.Source
import H0mework.Foundation.Responsibility.DebtU7
import H0mework.Foundation.Responsibility.DebtLedger

/-! A completed source request stays at the same paid state while the original native action transports the whole ledger. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Idle

open SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

def transportLaw (environment : Env Value Var) (raw : Expr Value Var sort) :
    DebtTransportLaw (SourceOperationExecutionDebt.State environment raw) (fun state => remaining state.1) where
  EventAt source target := SourceOperationExecutionDebt.Settlement source × PLift (target = source)
  budget_le := by
    rintro source target ⟨settled, ⟨same⟩⟩
    cases same
    exact Nat.le_refl _

def law (environment : Env Value Var) (raw : Expr Value Var sort) : DebtActivationLaw.{u} :=
  { SourceOperationExecutionDebt.law environment raw with
    transportLaw? := some (transportLaw environment raw) }

def identityTransport {environment : Env Value Var} {raw : Expr Value Var sort}
    (state : SourceOperationExecutionDebt.State environment raw)
    (settled : SourceOperationExecutionDebt.Settlement state) :
    (law environment raw).TransportAt state state :=
  ⟨settled, ⟨rfl⟩⟩

variable {N : WorldRelationNetwork.{u}} {sourceSupport targetSupport : N.Support}
variable {environment : Env Value Var} {raw : Expr Value Var sort}

def wholeEvolution
    (base : LedgerWriteEvolutionAt N ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (owner : OpenResponsibilityAt N sourceSupport)
    (state : SourceOperationExecutionDebt.State environment raw)
    (settled : SourceOperationExecutionDebt.Settlement state) :
    LedgerWriteEvolutionAt (ExtendedNetwork N (law environment raw))
      (activeLedger sourceSupport state) (activeLedger targetSupport state) where
  destination := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl oldResponsibility =>
        let generated := base.destination ⟨oldResponsibility, opened⟩
        exact ⟨oldEntry (law := law environment raw) (state? := some state) generated.1,
          RootGeneratedDebtActivationU7.mapOldEntryEvolution
            (law := law environment raw) (state? := some state) generated.2⟩
    | inr debtId =>
        rcases opened with ⟨⟨debtIdEq⟩⟩
        subst debtId
        exact ⟨debtEntry (N := N) (law := law environment raw) targetSupport state,
          .transferred (debtTransportReceipt sourceSupport (identityTransport state settled))
            (base.destination owner).2.toDebtLineage.lineage_eq rfl
            ((law environment raw).transport_budget_le (identityTransport state settled))⟩
  origin := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl oldResponsibility =>
        let generated := base.origin ⟨oldResponsibility, opened⟩
        exact ⟨oldEntry (law := law environment raw) (state? := some state) generated.1,
          RootGeneratedDebtActivationU7.mapOldEntryEvolution
            (law := law environment raw) (state? := some state) generated.2⟩
    | inr debtId =>
        rcases opened with ⟨⟨debtIdEq⟩⟩
        subst debtId
        exact ⟨debtEntry (N := N) (law := law environment raw) sourceSupport state,
          .transferred (debtTransportReceipt sourceSupport (identityTransport state settled))
            (base.destination owner).2.toDebtLineage.lineage_eq rfl
            ((law environment raw).transport_budget_le (identityTransport state settled))⟩

end RootGeneratedDebtActivationJointSource.Idle
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
