import H0mework.Foundation.Source.SequentialAction

/-!
# Zero-budget closure for sequential actual actions

A conservative sequential ingress cannot refill a ledger whose every source
row is already at budget zero.  The target root's first whole-ledger write
cannot do so either: every target row has an exact old origin and every legal
row evolution is non-increasing.  Thus a law or representation change may
make a residual addressable, but it cannot manufacture positive progress
capacity without a new source-owned renewal occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootInquiryCompletion
namespace NoFreeCapacityRestoration

noncomputable section

universe u

/-- A live ledger entry whose source-owned progress budget is positive. -/
def PositiveProgressEntryAt
    {N : WorldRelationNetwork.{u}}
    (ledger : CompleteLiveLedgerAt N) : Type u :=
  Sigma fun entry : ledger.Entry => PLift (0 < entry.progressBudget)

theorem positiveProgressEntry_isEmpty_of_all_zero
    {N : WorldRelationNetwork.{u}}
    (ledger : CompleteLiveLedgerAt N)
    (allZero : (entry : ledger.Entry) → entry.progressBudget = 0) :
    IsEmpty (PositiveProgressEntryAt ledger) := by
  constructor
  intro positive
  rcases positive with ⟨entry, budgetPositive⟩
  have positiveBudget := budgetPositive.down
  rw [allZero entry] at positiveBudget
  exact (Nat.lt_irrefl 0) positiveBudget

namespace SourceNativeSequentialActualActionTargetAt

variable
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {sourceRoot : SourceNativeLivingRootClosure N V}
    {sourceVisit : SourceNativeTemporalVisitAt
      sourceRoot.toAuthoritativeRoot.toLedgerRoot}
    {sourceEvent : ExactTemporalCausalRootEventAt
      sourceRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit}
    {sourceEntry : OpenResponsibilityAt N
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current))}
    {sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      sourceRoot sourceVisit sourceEntry}

/-- Surjective no-fresh ingress plus rowwise conservativity preserves a
completely exhausted source ledger. -/
theorem initialLedger_all_zero
    (target : SourceNativeSequentialActualActionTargetAt
      sourceRoot sourceVisit sourceEvent sourceEntry sourceAuthority)
    (sourceAllZero :
      (entry : OpenResponsibilityAt N
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (sourceRoot.emitted sourceVisit.current))) →
        entry.progressBudget = 0) :
    (targetEntry : OpenResponsibilityAt target.TargetN
      (target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (target.targetRoot.emitted
          target.targetRoot.toAuthoritativeRoot.toRoot.source.initial))) →
      targetEntry.progressBudget = 0 := by
  intro targetEntry
  rcases target.initialLedgerNoFresh targetEntry with
    ⟨⟨oldEntry, entryEquality⟩⟩
  have budgetLe := target.initialLedger_budget_conservative oldEntry
  rw [sourceAllZero oldEntry] at budgetLe
  have translatedZero :
      (target.initialOpenLedger.forward oldEntry).progressBudget = 0 :=
    Nat.eq_zero_of_le_zero budgetLe
  simpa only [entryEquality.down] using translatedZero

/-- The first generated whole-ledger successor also remains exhausted.  This
uses target-origin coverage and the global no-refill law for every legal row
evolution, so merge, split, transfer and carry cannot evade the result. -/
theorem firstSuccessorLedger_all_zero
    (target : SourceNativeSequentialActualActionTargetAt
      sourceRoot sourceVisit sourceEvent sourceEntry sourceAuthority)
    (sourceAllZero :
      (entry : OpenResponsibilityAt N
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (sourceRoot.emitted sourceVisit.current))) →
        entry.progressBudget = 0) :
    (targetEntry : OpenResponsibilityAt target.TargetN
      (target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        target.firstSuccessor.targetOccurrence)) →
      targetEntry.progressBudget = 0 := by
  intro targetEntry
  let origin := target.firstSuccessor.ledgerEvolution.origin targetEntry
  have originZero : origin.1.progressBudget = 0 :=
    initialLedger_all_zero target sourceAllZero origin.1
  have budgetLe : targetEntry.progressBudget ≤ origin.1.progressBudget :=
    origin.2.progressBudget_not_refilled
  rw [originZero] at budgetLe
  exact Nat.eq_zero_of_le_zero budgetLe

/-- No positive-budget row can be hidden in the action-generated target
ledger. -/
theorem firstSuccessorPositiveProgress_isEmpty
    (target : SourceNativeSequentialActualActionTargetAt
      sourceRoot sourceVisit sourceEvent sourceEntry sourceAuthority)
    (sourceAllZero :
      (entry : OpenResponsibilityAt N
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (sourceRoot.emitted sourceVisit.current))) →
        entry.progressBudget = 0) :
    IsEmpty
      (PositiveProgressEntryAt
        (⟨target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          target.firstSuccessor.targetOccurrence⟩ :
          CompleteLiveLedgerAt target.TargetN)) :=
  positiveProgressEntry_isEmpty_of_all_zero _
    (firstSuccessorLedger_all_zero target sourceAllZero)

end SourceNativeSequentialActualActionTargetAt

end
end NoFreeCapacityRestoration
end RootInquiryCompletion
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.NoFreeCapacityRestoration.SourceNativeSequentialActualActionTargetAt.initialLedger_all_zero
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.NoFreeCapacityRestoration.SourceNativeSequentialActualActionTargetAt.firstSuccessorLedger_all_zero
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.NoFreeCapacityRestoration.SourceNativeSequentialActualActionTargetAt.firstSuccessorPositiveProgress_isEmpty
