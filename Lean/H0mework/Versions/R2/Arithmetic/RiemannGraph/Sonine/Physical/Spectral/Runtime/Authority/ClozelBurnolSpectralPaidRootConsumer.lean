import H0mework.Versions.R2.Foundation.Runtime.GatedClaimPaidRoot
import H0mework.Versions.R2.Arithmetic.RiemannGraph.Sonine.Physical.Spectral.Runtime.Admission.ClozelBurnolSpectralGatedClaimCurrent

/-!
# Conditional Burnol spectral paid-root consumer

An actual normalized kernel event generates the strict payment, exact
two-phase root, causal-entry authority and critical-line terminal.  The kernel
event remains the unresolved source event; it is not stored in the claim.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace SpectralActualityPaidRootConsumer

open GatedClaimPaidRoot GatedClaimRootAuthority
open SpectralActuality SpectralActualityGatedClaimCurrent
open SpectralActualityPendingClaimBirth

noncomputable section

def paidRootInput (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    InputAt (pendingClaimBirth projection) where
  advance := advanceOfKernelEvent projection kernelEvent
  terminal := SourceNativeGatedClaimWholeTerminalAt.ofSupportTerminal
    (.actual (settlementOfKernelEvent projection kernelEvent))

def pendingCausalAuthority (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :=
  GatedClaimPaidRoot.pendingDebtCausalAuthority
    (paidRootInput projection kernelEvent)

def paidCausalAuthority (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :=
  GatedClaimPaidRoot.paidDebtCausalAuthority
    (paidRootInput projection kernelEvent)

theorem kernel_event_generates_terminal_root
    (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    ((authoritativeRoot (paidRootInput projection kernelEvent)).generatedLedgerAt
      .paid).entryDisposition
        (advanceOfKernelEvent projection kernelEvent).targetCurrent.entry =
      .terminal (paidDebtTerminal (paidRootInput projection kernelEvent)) :=
  paid_debt_disposition_is_terminal (paidRootInput projection kernelEvent)

theorem kernel_event_terminal_forces_criticalLine
    (projection : ProjectionAt)
    (kernelEvent : NormalizedPhysicalKernelEventAt projection.coordinate) :
    projection.coordinate.re = 1 / 2 :=
  (settlementOfKernelEvent projection kernelEvent).forces_criticalLine

end

end SpectralActualityPaidRootConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
