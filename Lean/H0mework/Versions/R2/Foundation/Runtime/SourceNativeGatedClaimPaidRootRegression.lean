import H0mework.Versions.R2.Foundation.Runtime.GatedClaimPaidRoot

/-! Generic consumers and hostiles for paid-root installation. -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace GatedClaimPaidRootRegression

open GatedClaimPreProcess GatedClaimPaidRoot PendingClaimBirth

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

def generatedRoot (input : InputAt birth) := authoritativeRoot input

def generatedPendingAuthority (input : InputAt birth) :=
  pendingDebtCausalAuthority input

def generatedPaidAuthority (input : InputAt birth) :=
  paidDebtCausalAuthority input

theorem generated_root_discharges_paid_row (input : InputAt birth) :
    ((generatedRoot input).generatedLedgerAt .paid).entryDisposition
      input.advance.targetCurrent.entry =
        .terminal (paidDebtTerminal input) :=
  paid_debt_disposition_is_terminal input

/-- No strict step means no paid-root input, even if arbitrary target states
remain present in the kinematic carrier. -/
theorem no_paid_root_of_empty_step
    (empty : (target : birth.law.DebtState) →
      IsEmpty (birth.law.StepAt birth.initial target)) :
    IsEmpty (InputAt birth) :=
  ⟨fun input => (empty input.advance.targetState).false input.advance.event⟩

/-- A same-row budget-preserving transport cannot replace the strict step. -/
theorem transport_does_not_create_paid_root
    {target : birth.law.DebtState}
    (_transport : birth.law.TransportAt birth.initial target)
    (empty : (next : birth.law.DebtState) →
      IsEmpty (birth.law.StepAt birth.initial next)) :
    IsEmpty (InputAt birth) :=
  no_paid_root_of_empty_step empty

/-- An obstruction goes to U7 and remains unable to create root continuation. -/
theorem obstruction_does_not_create_paid_root
    (_obstruction : SourceNativeGatedClaimObstructionAt
      (SourceNativeGatedClaimCurrentAt.initial birth))
    (empty : (next : birth.law.DebtState) →
      IsEmpty (birth.law.StepAt birth.initial next)) :
    IsEmpty (InputAt birth) :=
  no_paid_root_of_empty_step empty

end

end GatedClaimPaidRootRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
