import H0mework.Versions.R2.Foundation.Responsibility.PendingClaimBirth
import H0mework.Foundation.Responsibility.DebtU7

/-!
# Source-native gated claim pre-process

A pending-claim birth already owns a complete active ledger and one exact
fresh debt row, but it owns no successor.  This kernel keeps that boundary:
the sole next-generating authority is an actual strict `StepAt` receipt from
the package's installed debt law.

Settlement closes the local debt clock.  Whole-ledger terminal authority
requires either a base-world support-settlement receipt together with that
local settlement, or the same law's independent `SupportTerminalAt`.  An
obstruction exposes the installed debt obstruction to the existing U7
theory-audit calculus and does not generate a next.

This carrier is deliberately a gated pre-process, not a
`SourceNativeLivingRootProcess`, whose ABI requires a total successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace GatedClaimPreProcess

open DebtActivationWorld DebtActivationLedger PendingClaimBirth
open RootGeneratedDebtActivationU7

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}}
variable {facade : SourceNativePendingClaimRuntimeFacade N}
variable {runtime : LivingRuntimeState facade.base.process}
variable {activated : ExactActivatedRootOccurrenceAt runtime}
variable {face : facade.PendingFaceAt runtime}
variable {read : SourceInstalledPendingClaimFaceAt facade runtime face}

/-- A live active-ledger state descended from one exact pending-claim birth.
The token contains no event or future choice. -/
structure SourceNativeGatedClaimCurrentAt
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read)
    (_state : birth.law.DebtState) : Type (u + 4) where
  private mk ::

namespace SourceNativeGatedClaimCurrentAt

variable {birth : SourceExactPendingClaimBirthReceiptAt
  facade runtime activated read}
variable {state : birth.law.DebtState}

/-- The born debt row is the initial gated current. -/
def initial
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    SourceNativeGatedClaimCurrentAt birth birth.initial :=
  .mk

/-- Complete ledger at the current law-owned state. -/
def ledger
    (_current : SourceNativeGatedClaimCurrentAt birth state) :
    CompleteLiveLedgerAt (ExtendedNetwork N birth.law) :=
  activeLedger birth.sourceLedger.support state

/-- Exact tracked claim row at the current state. -/
def entry
    (_current : SourceNativeGatedClaimCurrentAt birth state) :
    (activeLedger birth.sourceLedger.support state).Entry :=
  debtEntry birth.sourceLedger.support state

@[simp] theorem initial_ledger_eq_birth
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    (initial birth).ledger = birth.targetLedger :=
  rfl

@[simp] theorem initial_entry_eq_birth
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    (initial birth).entry = birth.debtEntry :=
  rfl

@[simp] theorem entry_claim_eq_package
    (current : SourceNativeGatedClaimCurrentAt birth state) :
    current.entry.claim = .inr birth.law.debtClaim :=
  rfl

end SourceNativeGatedClaimCurrentAt

/-- Sealed advance authority.  Its only generator consumes an actual strict
step belonging to the birth package's law. -/
structure SourceNativeGatedClaimAdvanceAt
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (_current : SourceNativeGatedClaimCurrentAt birth state) : Type (u + 4) where
  targetState : birth.law.DebtState
  private step : birth.law.StepAt state targetState

namespace SourceNativeGatedClaimAdvanceAt

variable {birth : SourceExactPendingClaimBirthReceiptAt
  facade runtime activated read}
variable {state target : birth.law.DebtState}
variable {current : SourceNativeGatedClaimCurrentAt birth state}

/-- An installed strict step is the sole advance constructor. -/
def generate
    (current : SourceNativeGatedClaimCurrentAt birth state)
    (step : birth.law.StepAt state target) :
    SourceNativeGatedClaimAdvanceAt current :=
  ⟨target, step⟩

def event (advance : SourceNativeGatedClaimAdvanceAt current) :
    birth.law.StepAt state advance.targetState :=
  advance.step

def targetCurrent (advance : SourceNativeGatedClaimAdvanceAt current) :
    SourceNativeGatedClaimCurrentAt birth advance.targetState :=
  .mk

/-- The same strict step accounts for every row of the active ledger. -/
def ledgerEvolution (advance : SourceNativeGatedClaimAdvanceAt current) :
    LedgerWriteEvolutionAt (ExtendedNetwork N birth.law)
      current.ledger advance.targetCurrent.ledger :=
  stepLedgerEvolution birth.sourceLedger.support advance.event

theorem claim_eq (advance : SourceNativeGatedClaimAdvanceAt current) :
    current.entry.claim = advance.targetCurrent.entry.claim :=
  debtStep_claim_invariant birth.sourceLedger.support advance.event

theorem strict_debit (advance : SourceNativeGatedClaimAdvanceAt current) :
    advance.targetCurrent.entry.progressBudget <
      current.entry.progressBudget :=
  debtStep_budget_lt birth.sourceLedger.support advance.event

end SourceNativeGatedClaimAdvanceAt

/-- A gated current has a next exactly through strict-step authority. -/
abbrev SourceNativeGatedClaimGeneratedNextAt
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (current : SourceNativeGatedClaimCurrentAt birth state) : Type (u + 4) :=
  SourceNativeGatedClaimAdvanceAt current

theorem no_next_of_step_isEmpty
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (current : SourceNativeGatedClaimCurrentAt birth state)
    (empty : (target : birth.law.DebtState) →
      IsEmpty (birth.law.StepAt state target)) :
    IsEmpty (SourceNativeGatedClaimGeneratedNextAt current) :=
  ⟨fun advance => (empty advance.targetState).false advance.event⟩

/-- Local claim discharge.  It certifies zero debt budget but contains no
whole-support receipt and no successor. -/
structure SourceNativeGatedClaimSettlementAt
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (_current : SourceNativeGatedClaimCurrentAt birth state) : Type (u + 4) where
  private settlement : birth.law.SettlementAt state

namespace SourceNativeGatedClaimSettlementAt

variable {birth : SourceExactPendingClaimBirthReceiptAt
  facade runtime activated read}
variable {state : birth.law.DebtState}
variable {current : SourceNativeGatedClaimCurrentAt birth state}

def generate
    (current : SourceNativeGatedClaimCurrentAt birth state)
    (settlement : birth.law.SettlementAt state) :
    SourceNativeGatedClaimSettlementAt current :=
  ⟨settlement⟩

def event (settlement : SourceNativeGatedClaimSettlementAt current) :
    birth.law.SettlementAt state :=
  settlement.settlement

theorem budget_eq_zero
    (settlement : SourceNativeGatedClaimSettlementAt current) :
    current.entry.progressBudget = 0 :=
  debtSettlement_budget_zero birth.sourceLedger.support settlement.event

/-- A local settlement does not itself generate a next. -/
def GeneratedNextAt
    (_settlement : SourceNativeGatedClaimSettlementAt current) : Type :=
  PEmpty

instance generatedNext_isEmpty
    (settlement : SourceNativeGatedClaimSettlementAt current) :
    IsEmpty settlement.GeneratedNextAt :=
  ⟨fun next => nomatch next⟩

end SourceNativeGatedClaimSettlementAt

/-- A local settlement and an actual base-world support receipt together
discharge the complete extended ledger.  Neither input alone suffices. -/
def sourceNativeGatedClaimBaseSettlementWholeTerminal
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (current : SourceNativeGatedClaimCurrentAt birth state)
    (settlement : SourceNativeGatedClaimSettlementAt current)
    (baseReceipt : N.DispositionAt birth.sourceLedger.support
      .supportSettlement) :
    LedgerTerminalEvolutionAt (ExtendedNetwork N birth.law) current.ledger :=
  settlementLedgerEvolution birth.sourceLedger.support settlement.event
    baseReceipt

/-- An independent phase-terminal event is the second whole-ledger terminal
route.  It contains its own local settlement and needs no base receipt. -/
def sourceNativeGatedClaimSupportTerminalWholeTerminal
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (current : SourceNativeGatedClaimCurrentAt birth state)
    (terminal : birth.law.SupportTerminalAt state) :
    LedgerTerminalEvolutionAt (ExtendedNetwork N birth.law) current.ledger :=
  supportTerminalLedgerEvolution birth.sourceLedger.support terminal

/-- Exact obstruction of the live claim. -/
structure SourceNativeGatedClaimObstructionAt
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (_current : SourceNativeGatedClaimCurrentAt birth state) : Type (u + 4) where
  private obstruction : birth.law.ObstructionAt state

namespace SourceNativeGatedClaimObstructionAt

variable {birth : SourceExactPendingClaimBirthReceiptAt
  facade runtime activated read}
variable {state : birth.law.DebtState}
variable {current : SourceNativeGatedClaimCurrentAt birth state}

def generate
    (current : SourceNativeGatedClaimCurrentAt birth state)
    (obstruction : birth.law.ObstructionAt state) :
    SourceNativeGatedClaimObstructionAt current :=
  ⟨obstruction⟩

def event (obstruction : SourceNativeGatedClaimObstructionAt current) :
    birth.law.ObstructionAt state :=
  obstruction.obstruction

def worldObstruction
    (obstruction : SourceNativeGatedClaimObstructionAt current) :
    (ExtendedNetwork N birth.law).ObstructionAt current.ledger.support :=
  debtObstruction birth.sourceLedger.support obstruction.event

theorem obstructionClaim_eq_entryClaim
    (obstruction : SourceNativeGatedClaimObstructionAt current) :
    (ExtendedNetwork N birth.law).obstructionClaim
      obstruction.worldObstruction = current.entry.claim :=
  rfl

/-- Existing generic debt-U7 consumes the exact active obstruction and emits
its theory-audit answer. -/
def toTheoryAudit
    (obstruction : SourceNativeGatedClaimObstructionAt current)
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    SourceNativeU7TheoryAuditAt (extendU7Calculus oldU7 oldCalculus)
      ((extendU7Calculus oldU7 oldCalculus).source.emit
        obstruction.worldObstruction) :=
  debt_theoryAudit oldU7 oldCalculus birth.sourceLedger.support
    obstruction.event

def GeneratedNextAt
    (_obstruction : SourceNativeGatedClaimObstructionAt current) : Type :=
  PEmpty

instance generatedNext_isEmpty
    (obstruction : SourceNativeGatedClaimObstructionAt current) :
    IsEmpty obstruction.GeneratedNextAt :=
  ⟨fun next => nomatch next⟩

end SourceNativeGatedClaimObstructionAt

/-- Partial event grammar.  No inhabitant exists without an actual installed
step, settlement, or obstruction; in particular there is no idle branch. -/
inductive SourceNativeGatedClaimDispositionAt
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (current : SourceNativeGatedClaimCurrentAt birth state) : Type (u + 4)
  | advanced (advance : SourceNativeGatedClaimAdvanceAt current)
  | settled (settlement : SourceNativeGatedClaimSettlementAt current)
  | obstructed (obstruction : SourceNativeGatedClaimObstructionAt current)

theorem no_disposition_of_all_events_empty
    {birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read}
    {state : birth.law.DebtState}
    (current : SourceNativeGatedClaimCurrentAt birth state)
    (stepEmpty : (target : birth.law.DebtState) →
      IsEmpty (birth.law.StepAt state target))
    (settlementEmpty : IsEmpty (birth.law.SettlementAt state))
    (obstructionEmpty : IsEmpty (birth.law.ObstructionAt state)) :
    IsEmpty (SourceNativeGatedClaimDispositionAt current) :=
  ⟨fun disposition => by
    cases disposition with
    | advanced advance =>
        exact (stepEmpty advance.targetState).false advance.event
    | settled settlement =>
        exact settlementEmpty.false settlement.event
    | obstructed obstruction =>
        exact obstructionEmpty.false obstruction.event⟩

end


end GatedClaimPreProcess
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
