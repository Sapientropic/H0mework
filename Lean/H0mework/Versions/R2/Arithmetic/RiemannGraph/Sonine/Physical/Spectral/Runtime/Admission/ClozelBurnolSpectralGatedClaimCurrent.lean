import H0mework.Versions.R2.Foundation.Runtime.GatedClaimProcess
import H0mework.Versions.R2.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Admission.ClozelBurnolSpectralPendingClaimBirth

/-!
# Spectral actuality in the gated claim pre-process

The freshly born spectral claim becomes a gated current.  Its only installed
advance is the debt law's strict payment, which itself requires the normalized
physical kernel settlement.  Thus the old analytic successor cannot bypass
the characteristic landing.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace SpectralActualityGatedClaimCurrent

open GatedClaimPreProcess
open SpectralActuality
open SpectralActualityDebt
open SpectralActualityPendingClaimBirth

noncomputable section

def gatedCurrent (projection : ProjectionAt) :
    SourceNativeGatedClaimCurrentAt (pendingClaimBirth projection)
      (pendingClaimBirth projection).initial :=
  SourceNativeGatedClaimCurrentAt.initial (pendingClaimBirth projection)

theorem gatedCurrent_ledger_eq_birth (projection : ProjectionAt) :
    (gatedCurrent projection).ledger =
      (pendingClaimBirth projection).targetLedger :=
  SourceNativeGatedClaimCurrentAt.initial_ledger_eq_birth
    (pendingClaimBirth projection)

theorem gatedCurrent_claim (projection : ProjectionAt) :
    (gatedCurrent projection).entry.claim =
      .inr (SpectralActualityClaimAt.generate projection.event) :=
  rfl

def settlementOfKernelEvent (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    SpectralActualitySettlementAt projection.event :=
  SpectralActualitySettlementAt.ofKernelEvent projection.event kernelEvent

/-- The characteristic landing supplies the sole strict advance authority. -/
def advanceOfKernelEvent (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    SourceNativeGatedClaimAdvanceAt (gatedCurrent projection) :=
  SourceNativeGatedClaimAdvanceAt.generate (gatedCurrent projection)
    (StrictPaymentAt.ofSettlement
      (settlementOfKernelEvent projection kernelEvent))

theorem advanceOfKernelEvent_strict (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    (advanceOfKernelEvent projection kernelEvent).targetCurrent.entry.progressBudget <
      (gatedCurrent projection).entry.progressBudget :=
  (advanceOfKernelEvent projection kernelEvent).strict_debit

theorem advanceOfKernelEvent_claim_eq (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    (gatedCurrent projection).entry.claim =
      (advanceOfKernelEvent projection kernelEvent).targetCurrent.entry.claim :=
  (advanceOfKernelEvent projection kernelEvent).claim_eq

def localSettlementOfKernelEvent (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    SourceNativeGatedClaimSettlementAt
      (advanceOfKernelEvent projection kernelEvent).targetCurrent :=
  SourceNativeGatedClaimSettlementAt.generate
    (advanceOfKernelEvent projection kernelEvent).targetCurrent
    (.actual (settlementOfKernelEvent projection kernelEvent))

theorem localSettlementOfKernelEvent_budget_zero
    (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    (advanceOfKernelEvent projection kernelEvent).targetCurrent.entry.progressBudget = 0 :=
  (localSettlementOfKernelEvent projection kernelEvent).budget_eq_zero

theorem localSettlementOfKernelEvent_has_no_next
    (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    IsEmpty (localSettlementOfKernelEvent projection kernelEvent).GeneratedNextAt :=
  inferInstance

/-- Whole-ledger terminal authority appears only after the same kernel event
has generated the installed support-terminal receipt. -/
def wholeTerminalOfKernelEvent (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :=
  sourceNativeGatedClaimSupportTerminalWholeTerminal
    (advanceOfKernelEvent projection kernelEvent).targetCurrent
    (.actual (settlementOfKernelEvent projection kernelEvent))

theorem pendingObstruction_isEmpty (projection : ProjectionAt) :
    IsEmpty ((pendingClaimBirth projection).law.ObstructionAt
      (pendingClaimBirth projection).initial) :=
  ⟨fun obstruction => nomatch obstruction⟩

end


end SpectralActualityGatedClaimCurrent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
