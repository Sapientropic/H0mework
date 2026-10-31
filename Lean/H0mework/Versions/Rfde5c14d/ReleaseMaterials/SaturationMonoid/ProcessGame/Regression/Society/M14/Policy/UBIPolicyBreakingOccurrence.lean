import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicActualServiceCapacity
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M13.Audit.MotherLawBreakingRegression

/-!
# M14 UBI-policy breaking occurrence and U7/U8 gate

Full price capture is not merely a failed readout.  At the exact depth-zero
payment occurrence it preserves the actual payment/service process while
collapsing actionable exit capacity from one to zero.  A source-owned
mother-law classifier emits that breaking occurrence, joins it to the already
installed same-root failure face, and opens the existing rooted U8 gate.

The breaking carrier contains no failure, coface, revised law, first write, or
self-U8 result.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14UBIPolicyBreakingOccurrence

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Theory Audit UBI Renewal Capacity
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity

abbrev OldTheory := RootInquiryU8CompletionRegression.oldTheory
abbrev Root := jointRoot.toAuthoritativeRoot

/-- Exact policy-breaking occurrence.  All substantive policy facts are
generated propositions; no U8 output appears in this carrier. -/
structure UBIPolicyBreakingOccurrenceAt
    {current : M9ProofCarryingRenewalInquiryRoot.V.Current}
    (occurrence : Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current) : Type where
  private mk ::
  rootOccurrence_eq :
    (⟨current, occurrence⟩ :
      Sigma Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt) =
      ⟨(temporalVisitAt 0).current,
        (periodicSourceBackedPaymentAt 0).rootOccurrence.occurrence⟩
  fullCapture : capturedProgram.exitCone.FullPriceCaptureAt
  uncapturedCapacity :
    (geometryCompilerAt 0).actionableExitCapacity = 1
  capturedCapacity :
    (capturedGeometryCompilerAt 0).actionableExitCapacity = 0
  samePaymentStanding :
    capturedProgram.purchasingPowerStanding =
      exitCapacityProgram.purchasingPowerStanding
  sameActualServiceSlots :
    (anomiePhaseAt 0).served.length = 2

namespace UBIPolicyBreakingOccurrenceAt

/-- Sole classifier-side producer from an actual root occurrence. -/
def generate
    {current : M9ProofCarryingRenewalInquiryRoot.V.Current}
    (occurrence : Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current) : UBIPolicyBreakingOccurrenceAt occurrence := by
  cases current
  rcases occurrence with ⟨support, event⟩
  cases support with
  | false => exact nomatch event
  | true =>
      cases event
      exact
        ⟨rfl, capturedProgram_fullPriceCapture,
          actionableExitCapacity_eq_one_at 0,
          captured_nominal_capacity_eq_zero_at 0, rfl, rfl⟩

end UBIPolicyBreakingOccurrenceAt

/-- Occurrence-local deletion diagnostic for the unique old law.  It is not
the U8 gate and cannot manufacture a revision. -/
def deletionAuditSource : LawDeletionAuditSourceAt
    OldTheory.inventory RootInquiryU8CompletionRegression.obstruction where
  OccurrenceAt := fun _ => PUnit
  emit := fun _ => PUnit.unit
  event_eq_emit := by intros; rfl
  compileAudit := fun _ _ => .nearMiss ()

/-- UBI policy as a source-owned mother-law contract over the literal old
root.  `classify` generates the breaking occurrence for every inhabitable root
event; it stores no breaking witness or future audit table. -/
def contract : SourceOwnedMotherLawContractAt Root OldTheory where
  lawSurface_eq := rfl
  ScopeAt := fun _law {_current} _occurrence _entry => PUnit
  BreakingActiveAt := fun _law {_current} occurrence =>
    UBIPolicyBreakingOccurrenceAt occurrence
  BreakingInactiveAt := fun _law {_current} _occurrence => PEmpty
  classify := fun _law {_current} occurrence =>
    .inl (UBIPolicyBreakingOccurrenceAt.generate occurrence)
  scopeEntryAt := by
    intro law current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => exact entry
  scopeReceiptAt := fun _active => PUnit.unit
  obstructionAt := by
    intro law current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => exact RootInquiryU8CompletionRegression.obstruction
  obstructionClaim_eq_scopeClaim := by
    intro law current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => rfl
  deletionAuditSourceAt := by
    intro law current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => exact deletionAuditSource

def active : contract.BreakingActiveAt ()
    (Root.emitted jointVisit.current) :=
  UBIPolicyBreakingOccurrenceAt.generate _

@[simp] theorem classified :
    contract.classify () (Root.emitted jointVisit.current) = .inl active :=
  rfl

/-- The breaking occurrence and the installed failure coordinate are joined
at the exact same old-root visit. -/
def audit : SourceGeneratedMotherLawAuditAt contract () active classified
    failureFace rfl :=
  SourceGeneratedMotherLawAuditAt.generate contract () active classified
    failureFace rfl

@[simp] theorem audit_rootOccurrence_is_payment_rootOccurrence :
    (⟨jointVisit.current, audit.rootOccurrence⟩ :
      Sigma Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt) =
      ⟨(temporalVisitAt 0).current,
        (periodicSourceBackedPaymentAt 0).rootOccurrence.occurrence⟩ :=
  active.rootOccurrence_eq

theorem audit_breaking_capacity_collapse :
    (geometryCompilerAt 0).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt 0).actionableExitCapacity = 0 :=
  ⟨active.uncapturedCapacity, active.capturedCapacity⟩

def u8Gate : SourceGeneratedMotherLawU8GateAt audit
    authority.toAuthoritativeAuthority successor :=
  SourceGeneratedMotherLawU8GateAt.generate audit
    authority.toAuthoritativeAuthority successor

@[simp] theorem policyGate_rooted_is_existing_rooted :
    u8Gate.rooted = M9ProofCarryingRenewalU8Failure.rooted :=
  rfl

@[simp] theorem policyGate_coface_is_existing_coface :
    u8Gate.minimalCoface = M9ProofCarryingRenewalU8Failure.coface :=
  rfl

/-- A capacity-zero readout alone cannot open the U8 gate. -/
theorem bare_capacity_collapse_cannot_open_U8 : True := by
  fail_if_success
    exact SourceGeneratedMotherLawU8GateAt.generate
      (captured_nominal_capacity_eq_zero_at 0)
  trivial

/-- The breaking occurrence without its same-row failure audit and causal
authority likewise cannot open U8. -/
theorem bare_policy_breaking_occurrence_cannot_open_U8 : True := by
  fail_if_success
    exact SourceGeneratedMotherLawU8GateAt.generate active
  trivial

end
end M14UBIPolicyBreakingOccurrence
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPolicyBreakingOccurrence.audit
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPolicyBreakingOccurrence.u8Gate
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIPolicyBreakingOccurrence.policyGate_coface_is_existing_coface
