import H0mework.Versions.R2.Foundation.Runtime.GatedClaimProcess

/-!
# Whole-terminal authority for a gated claim

This file seals the two and only two existing whole-ledger terminal routes:
local settlement together with a base-world support receipt, or an independent
phase `SupportTerminalAt`.  The resulting receipt remains indexed by the exact
paid target current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace GatedClaimRootAuthority

open DebtActivationWorld PendingClaimBirth GatedClaimPreProcess

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}}
variable {facade : SourceNativePendingClaimRuntimeFacade N}
variable {runtime : LivingRuntimeState facade.base.process}
variable {activated : ExactActivatedRootOccurrenceAt runtime}
variable {face : facade.PendingFaceAt runtime}
variable {read : SourceInstalledPendingClaimFaceAt facade runtime face}
variable {birth : SourceExactPendingClaimBirthReceiptAt
  facade runtime activated read}
variable {state : birth.law.DebtState}
variable {current : SourceNativeGatedClaimCurrentAt birth state}

/-- Uniform whole-ledger terminal receipt sealed to one exact gated current.
No raw extended-world receipt enters the public constructors. -/
structure SourceNativeGatedClaimWholeTerminalAt
    (current : SourceNativeGatedClaimCurrentAt birth state) : Type (u + 4) where
  private localSettlement : birth.law.SettlementAt state
  private receipt : (ExtendedNetwork N birth.law).DispositionAt
    current.ledger.support .supportSettlement

namespace SourceNativeGatedClaimWholeTerminalAt

/-- Base-world settlement plus the exact local claim settlement. -/
def ofBaseSettlement
    (settlement : SourceNativeGatedClaimSettlementAt current)
    (baseReceipt : N.DispositionAt birth.sourceLedger.support
      .supportSettlement) :
    SourceNativeGatedClaimWholeTerminalAt current :=
  ⟨settlement.event,
    DebtActivationWorld.baseSettlementReceipt birth.sourceLedger.support
    baseReceipt⟩

/-- Independent phase-terminal event from the installed debt law. -/
def ofSupportTerminal
    (terminal : birth.law.SupportTerminalAt state) :
    SourceNativeGatedClaimWholeTerminalAt current :=
  ⟨birth.law.supportTerminal_settles terminal,
    DebtActivationWorld.debtSupportTerminalReceipt
    birth.sourceLedger.support terminal⟩

def worldReceipt
    (terminal : SourceNativeGatedClaimWholeTerminalAt current) :
    (ExtendedNetwork N birth.law).DispositionAt current.ledger.support
      .supportSettlement :=
  terminal.receipt

/-- Every row in the exact active ledger is discharged by the same sealed
support receipt. -/
def ledgerEvolution
    (terminal : SourceNativeGatedClaimWholeTerminalAt current) :
    LedgerTerminalEvolutionAt (ExtendedNetwork N birth.law) current.ledger :=
  ⟨fun _entry => ⟨terminal.worldReceipt⟩⟩

end SourceNativeGatedClaimWholeTerminalAt

end

end GatedClaimRootAuthority
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
