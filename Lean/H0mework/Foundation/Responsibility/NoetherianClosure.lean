import H0mework.Foundation.Authority.EntryDisposition

/-!
# Source-native Noetherian debt closure

An actual write does not imply termination.  This kernel closes one fixed debt
lineage only when the existing living-root process generates a finite paid
macro at every non-settled current:

```text
same debt + exact process successors + stepwise no-refill
+ finite no-refill context + one exact payment step
  -> well-founded continuation -> exact debt settlement
```

Local root terminal is not enough: it counts as settlement only when the exact
source-generated successor ledger contains no continuation of the same debt.
Fresh obligations and genuinely new writes remain unrestricted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

namespace RootDebtLineageAt

/-- Debt identity composes across actual carrier and root changes. -/
def trans
    {N : WorldRelationNetwork.{u}}
    {sourceSupport middleSupport targetSupport : N.Support}
    {source : OpenResponsibilityAt N sourceSupport}
    {middle : OpenResponsibilityAt N middleSupport}
    {target : OpenResponsibilityAt N targetSupport}
    (left : RootDebtLineageAt N source middle)
    (right : RootDebtLineageAt N middle target) :
    RootDebtLineageAt N source target where
  lineage_eq := left.lineage_eq.trans right.lineage_eq
  claim_eq := left.claim_eq.trans right.claim_eq

end RootDebtLineageAt

namespace SourceNativeLivingRootCurrentAt

/-- Complete live-entry fibre at one registered living-process current. -/
abbrev Entry
    {N : WorldRelationNetwork.{u}}
    (current : SourceNativeLivingRootCurrentAt N) : Type u :=
  OpenResponsibilityAt N
    (current.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (current.root.emitted current.visit.current))

end SourceNativeLivingRootCurrentAt

/-- One exact live debt at one registered state of a fixed living-root process.
The process state fixes the complete root source, temporal visit and successor;
the entry is an actual row of that current's complete ledger. -/
structure SourceNativeRootDebtCurrentAt
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)
    {originSupport : N.Support}
    (origin : OpenResponsibilityAt N originSupport) : Type (u + 4) where
  state : process.State
  entry : (process.stateAt state).Entry
  sameDebt : RootDebtLineageAt N origin entry

namespace SourceNativeRootDebtCurrentAt

def rooted
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (current : SourceNativeRootDebtCurrentAt process origin) :
    SourceNativeLivingRootCurrentAt N :=
  process.stateAt current.state

def budget
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (current : SourceNativeRootDebtCurrentAt process origin) : Nat :=
  current.entry.progressBudget

end SourceNativeRootDebtCurrentAt

/-- Actual successor-ledger rows which retain the exact source debt.  This is
the complete target fibre used both to continue and to certify settlement. -/
abbrev SourceNativeRootDebtTargetAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin) : Type u :=
  Sigma fun targetEntry :
      (process.stateAt (process.successor source.state)).Entry =>
    RootDebtLineageAt N source.entry targetEntry

/-- One exact micro-step of the tracked debt.  The target root/current is the
source process's canonical successor, never a caller-selected world.  Debt
identity and no-refill are read from the actual whole-ledger row evolution;
they are not parallel fields which a domain may submit independently.  The
target row is unique among rows carrying this source debt. -/
structure SourceNativeRootDebtStepAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin) : Type (u + 1) where
  targetEntry : (process.stateAt (process.successor source.state)).Entry
  evolution : LedgerEntryEvolutionAt N source.entry targetEntry
  sameDebtTarget_unique :
    (alternative : (process.stateAt (process.successor source.state)).Entry) →
      RootDebtLineageAt N source.entry alternative →
      alternative = targetEntry

namespace SourceNativeRootDebtStepAt

/-- The debt identity is the invariant face of the generated ledger row. -/
def sameDebt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source : SourceNativeRootDebtCurrentAt process origin}
    (step : SourceNativeRootDebtStepAt source) :
    RootDebtLineageAt N source.entry step.targetEntry :=
  step.evolution.toDebtLineage

/-- No-refill is a conservation readout of the same generated ledger row. -/
theorem progressBudget_not_refilled
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source : SourceNativeRootDebtCurrentAt process origin}
    (step : SourceNativeRootDebtStepAt source) :
    step.targetEntry.progressBudget ≤ source.entry.progressBudget :=
  step.evolution.progressBudget_not_refilled

end SourceNativeRootDebtStepAt

namespace SourceNativeRootDebtCurrentAt

/-- The target current is derived from the process successor and exact debt
row carried by the step. -/
def next
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin)
    (step : SourceNativeRootDebtStepAt source) :
    SourceNativeRootDebtCurrentAt process origin where
  state := process.successor source.state
  entry := step.targetEntry
  sameDebt := source.sameDebt.trans step.sameDebt

/-- Every exact process micro-step preserves the finite budget of this debt. -/
theorem next_budget_le
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin)
    (step : SourceNativeRootDebtStepAt source) :
    (source.next step).budget ≤ source.budget :=
  step.progressBudget_not_refilled

end SourceNativeRootDebtCurrentAt

/-- A finite, possibly empty no-refill history consisting only of exact
successors of one fixed living-root process.  Empty history is structural
identity, not a progress event.  A paid macro below must additionally exhibit
one exact strict-debit step. -/
inductive SourceNativeRootDebtMacroHistoryAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin) :
    SourceNativeRootDebtCurrentAt process origin → Type (u + 4)
  | refl : SourceNativeRootDebtMacroHistoryAt source source
  | one (step : SourceNativeRootDebtStepAt source) :
      SourceNativeRootDebtMacroHistoryAt source (source.next step)
  | snoc
      {middle : SourceNativeRootDebtCurrentAt process origin}
      (prior : SourceNativeRootDebtMacroHistoryAt source middle)
      (step : SourceNativeRootDebtStepAt middle) :
      SourceNativeRootDebtMacroHistoryAt source (middle.next step)

namespace SourceNativeRootDebtMacroHistoryAt

/-- Concatenate two exact histories without manufacturing a temporal step at
their common face. -/
def append
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source middle target : SourceNativeRootDebtCurrentAt process origin}
    (left : SourceNativeRootDebtMacroHistoryAt source middle) :
    SourceNativeRootDebtMacroHistoryAt middle target →
      SourceNativeRootDebtMacroHistoryAt source target
  | .refl => left
  | .one step => .snoc left step
  | .snoc prior step => .snoc (left.append prior) step

/-- Stepwise no-refill composes over the complete finite macro. -/
theorem target_budget_le_source
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source target : SourceNativeRootDebtCurrentAt process origin}
    (history : SourceNativeRootDebtMacroHistoryAt source target) :
    target.budget ≤ source.budget := by
  induction history with
  | refl => exact Nat.le_refl _
  | one step => exact source.next_budget_le step
  | snoc prior step ih =>
      exact Nat.le_trans
        (SourceNativeRootDebtCurrentAt.next_budget_le _ step) ih

end SourceNativeRootDebtMacroHistoryAt

/-- One exact same-debt successor which genuinely pays the finite root clock.
The step is already an actual whole-ledger evolution; strictness is the
domain's generated payment fact, not a consequence of no-refill alone. -/
structure SourceNativeRootDebtPaymentStepAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin) : Type (u + 1) where
  step : SourceNativeRootDebtStepAt source
  strictDebit : (source.next step).budget < source.budget

namespace SourceNativeRootDebtPaymentStepAt

/-- An equality-only carry or reassignment cannot inhabit the payment role. -/
theorem target_budget_ne_source
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source : SourceNativeRootDebtCurrentAt process origin}
    (payment : SourceNativeRootDebtPaymentStepAt source) :
    (source.next payment.step).budget ≠ source.budget :=
  Nat.ne_of_lt payment.strictDebit

end SourceNativeRootDebtPaymentStepAt

/-- One completed paid macro.  Prefix and suffix may carry, re-present, or
transfer the same debt without refilling it.  Strict macro descent is derived
only from the exhibited actual payment step between them; it is no longer a
caller-supplied endpoint field. -/
structure SourceNativePaidRootDebtMacroContinuationAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin) : Type (u + 4) where
  paymentSource : SourceNativeRootDebtCurrentAt process origin
  beforeHistory : SourceNativeRootDebtMacroHistoryAt source paymentSource
  payment : SourceNativeRootDebtPaymentStepAt paymentSource
  target : SourceNativeRootDebtCurrentAt process origin
  afterHistory : SourceNativeRootDebtMacroHistoryAt
    (paymentSource.next payment.step) target

namespace SourceNativePaidRootDebtMacroContinuationAt

/-- Build a paid macro from generated no-refill context and one exact payment.
There is deliberately no endpoint-inequality argument. -/
def ofPayment
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source paymentSource target :
      SourceNativeRootDebtCurrentAt process origin}
    (beforeHistory : SourceNativeRootDebtMacroHistoryAt source paymentSource)
    (payment : SourceNativeRootDebtPaymentStepAt paymentSource)
    (afterHistory : SourceNativeRootDebtMacroHistoryAt
      (paymentSource.next payment.step) target) :
    SourceNativePaidRootDebtMacroContinuationAt source where
  paymentSource := paymentSource
  beforeHistory := beforeHistory
  payment := payment
  target := target
  afterHistory := afterHistory

/-- The complete macro history contains the exact paying step. -/
def history
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source : SourceNativeRootDebtCurrentAt process origin}
    (continuation : SourceNativePaidRootDebtMacroContinuationAt source) :
    SourceNativeRootDebtMacroHistoryAt source continuation.target :=
  (continuation.beforeHistory.snoc continuation.payment.step).append
    continuation.afterHistory

/-- `≤ ; < ; ≤` composes to strict macro descent.  Equality-only carry or
bearer reassignment therefore cannot masquerade as payment. -/
theorem strictDebit
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source : SourceNativeRootDebtCurrentAt process origin}
    (continuation : SourceNativePaidRootDebtMacroContinuationAt source) :
    continuation.target.budget < source.budget := by
  exact lt_of_le_of_lt
    continuation.afterHistory.target_budget_le_source
    (lt_of_lt_of_le continuation.payment.strictDebit
      continuation.beforeHistory.target_budget_le_source)

end SourceNativePaidRootDebtMacroContinuationAt

/-- Law-free exact paid-continuation relation for one source-owned debt.

Unlike `SourceNativeNoetherianDebtClosureLaw.ContinuationRel`, this mouth does
not assume a total closure law.  Its only edges are already generated paid
macros, so it can certify the arithmetic death of a purported unbounded
same-debt history even when no total settlement/continuation classifier
exists. -/
def SourceNativePaidRootDebtContinuationRel
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (target source : SourceNativeRootDebtCurrentAt process origin) : Prop :=
  ∃ continuation : SourceNativePaidRootDebtMacroContinuationAt source,
    continuation.target = target

/-- Exact paid same-debt continuation is globally well founded on the
source-owned finite progress budget.  No caller supplies a global bound,
every-edge table, completed history, or terminal state. -/
theorem sourceNativePaidRootDebtContinuationRel_wellFounded
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport} :
    WellFounded
      (SourceNativePaidRootDebtContinuationRel
        (process := process) (origin := origin)) := by
  exact Subrelation.wf
    (fun relation => by
      rcases relation with ⟨continuation, rfl⟩
      exact continuation.strictDebit)
    (InvImage.wf
      (fun current : SourceNativeRootDebtCurrentAt process origin =>
        current.budget)
      Nat.lt_wfRel.wf)

/-- One exact paid macro cannot return the same debt current to itself. -/
theorem no_paidRootDebtMacro_self_return
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin) :
    ¬ SourceNativePaidRootDebtContinuationRel source source := by
  rintro ⟨continuation, target_eq⟩
  have strict := continuation.strictDebit
  rw [target_eq] at strict
  exact (Nat.lt_irrefl _) strict

/-- Zero remaining credit cannot support another paid continuation of the
same debt. -/
theorem no_paidRootDebtMacroContinuation_of_budget_eq_zero
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (source : SourceNativeRootDebtCurrentAt process origin)
    (budget_eq : source.budget = 0) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt source) where
  false continuation := by
    have strict := continuation.strictDebit
    rw [budget_eq] at strict
    exact Nat.not_lt_zero _ strict

/-- Exact inventory-complete terminal emitted by the source process's current
root.  A vocabulary-local terminal label cannot inhabit this type. -/
abbrev SourceNativeRootDebtLocalTerminalAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (current : SourceNativeRootDebtCurrentAt process origin) : Type u :=
  SourceFaithfulTerminalOccurrenceAt current.rooted.root.source.base
    (current.rooted.root.emitted current.rooted.visit.current)

namespace SourceNativeRootDebtLocalTerminalAt

/-- The local receipt is the exact whole-ledger compiler discharge. -/
def receipt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {current : SourceNativeRootDebtCurrentAt process origin}
    (terminal : SourceNativeRootDebtLocalTerminalAt current) :
    LedgerEntryTerminalAt N current.entry :=
  terminal.ledgerEvolution.discharge current.entry

end SourceNativeRootDebtLocalTerminalAt

/-- Final settlement of the tracked debt.  A local root terminal closes the
debt only when the exact source-generated successor ledger has no row carrying
the same lineage and claim. -/
structure SourceNativeRootDebtSettlementAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (current : SourceNativeRootDebtCurrentAt process origin) : Type (u + 1) where
  localTerminal : SourceNativeRootDebtLocalTerminalAt current
  noSameDebtAtTarget : IsEmpty (SourceNativeRootDebtTargetAt current)

namespace SourceNativeRootDebtSettlementAt

def receipt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {current : SourceNativeRootDebtCurrentAt process origin}
    (settlement : SourceNativeRootDebtSettlementAt current) :
    LedgerEntryTerminalAt N current.entry :=
  settlement.localTerminal.receipt

end SourceNativeRootDebtSettlementAt

/-- Complete same-debt closure law over one fixed living-root process.  Every
current emits either an exact settlement or a finite paid macro.  Target root,
current and visit remain fixed by `process.successor`; no fresh budget or local
terminal label occurs in this mouth. -/
structure SourceNativeNoetherianDebtClosureLaw
    {N : WorldRelationNetwork.{u}}
    (process : SourceNativeLivingRootProcess N)
    {originSupport : N.Support}
    (origin : OpenResponsibilityAt N originSupport) : Type (u + 5) where
  emit : (current : SourceNativeRootDebtCurrentAt process origin) →
    SourceNativeRootDebtSettlementAt current ⊕
      SourceNativePaidRootDebtMacroContinuationAt current

/-- A zero-budget debt with no exact local terminal cannot be covered by a
total Noetherian closure law.  Zero budget does not itself settle anything:
it excludes the paid-continuation branch, while the separately supplied empty
terminal fibre excludes settlement. -/
theorem no_noetherianDebtClosureLaw_of_budget_eq_zero_of_noLocalTerminal
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (current : SourceNativeRootDebtCurrentAt process origin)
    (budget_eq : current.budget = 0)
    (terminalEmpty : IsEmpty (SourceNativeRootDebtLocalTerminalAt current)) :
    IsEmpty (SourceNativeNoetherianDebtClosureLaw process origin) := by
  constructor
  intro law
  cases emitted_eq : law.emit current with
  | inl settlement =>
      exact terminalEmpty.false settlement.localTerminal
  | inr continuation =>
      exact
        (no_paidRootDebtMacroContinuation_of_budget_eq_zero current budget_eq
          ).false continuation

namespace SourceNativeNoetherianDebtClosureLaw

def ContinuationRel
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (_law : SourceNativeNoetherianDebtClosureLaw process origin)
    (target source : SourceNativeRootDebtCurrentAt process origin) : Prop :=
  SourceNativePaidRootDebtContinuationRel target source

/-- Paid macro continuation is an exact subrelation of strict descent on the
origin debt's source-owned `Nat` budget. -/
theorem continuationRel_wellFounded
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (law : SourceNativeNoetherianDebtClosureLaw process origin) :
    WellFounded law.ContinuationRel := by
  exact sourceNativePaidRootDebtContinuationRel_wellFounded

/-- Finite generated closure history.  Recursive continuation occurs only at
the exact paid macro target emitted by the source law. -/
inductive GeneratedHistoryAt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (law : SourceNativeNoetherianDebtClosureLaw process origin) :
    SourceNativeRootDebtCurrentAt process origin → Type (u + 4)
  | settled
      {current : SourceNativeRootDebtCurrentAt process origin}
      (settlement : SourceNativeRootDebtSettlementAt current)
      (emitted_eq : law.emit current = .inl settlement) :
      GeneratedHistoryAt law current
  | continued
      {current : SourceNativeRootDebtCurrentAt process origin}
      (continuation : SourceNativePaidRootDebtMacroContinuationAt current)
      (emitted_eq : law.emit current = .inr continuation)
      (tail : GeneratedHistoryAt law continuation.target) :
      GeneratedHistoryAt law current

def generatedHistory
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (law : SourceNativeNoetherianDebtClosureLaw process origin) :
    (current : SourceNativeRootDebtCurrentAt process origin) →
      law.GeneratedHistoryAt current :=
  law.continuationRel_wellFounded.fix
    (C := fun current => law.GeneratedHistoryAt current)
    (fun current recurse =>
      match emitted_eq : law.emit current with
      | .inl settlement => .settled settlement emitted_eq
      | .inr continuation =>
          .continued continuation emitted_eq
            (recurse continuation.target ⟨continuation, rfl⟩))

def GeneratedHistoryAt.terminalSettlement
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {law : SourceNativeNoetherianDebtClosureLaw process origin}
    {current : SourceNativeRootDebtCurrentAt process origin} :
    law.GeneratedHistoryAt current →
      Sigma fun target : SourceNativeRootDebtCurrentAt process origin =>
        SourceNativeRootDebtSettlementAt target
  | .settled settlement _ => ⟨current, settlement⟩
  | .continued _ _ tail => tail.terminalSettlement

/-- Every exact same-debt current reaches a typed settlement in the same fixed
living-root process. -/
def generatedSettlement
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (law : SourceNativeNoetherianDebtClosureLaw process origin)
    (current : SourceNativeRootDebtCurrentAt process origin) :
    Sigma fun target : SourceNativeRootDebtCurrentAt process origin =>
      SourceNativeRootDebtSettlementAt target :=
  (law.generatedHistory current).terminalSettlement

/-- The terminal receipt is the exact local compiler discharge at a current
whose generated successor ledger contains no continuation of the same debt. -/
def generatedReceipt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (law : SourceNativeNoetherianDebtClosureLaw process origin)
    (current : SourceNativeRootDebtCurrentAt process origin) :
    Sigma fun target : SourceNativeRootDebtCurrentAt process origin =>
      LedgerEntryTerminalAt N target.entry :=
  let settlement := law.generatedSettlement current
  ⟨settlement.1, settlement.2.receipt⟩

end SourceNativeNoetherianDebtClosureLaw

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.no_noetherianDebtClosureLaw_of_budget_eq_zero_of_noLocalTerminal
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.sourceNativePaidRootDebtContinuationRel_wellFounded
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.no_paidRootDebtMacro_self_return
