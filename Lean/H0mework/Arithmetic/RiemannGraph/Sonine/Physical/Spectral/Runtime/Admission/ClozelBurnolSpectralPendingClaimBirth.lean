import H0mework.Foundation.Responsibility.PendingClaimBirth
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Facade.CanonicalRiemannAnalyticFacade

/-!
# Spectral-actuality pending claim birth

The package-valued spectral face already installed in the fixed analytic
runtime births its zero-field claim as a fresh complete-ledger row.  The
constructor accepts no characteristic landing, kernel vector, payment,
settlement, target root or next current.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace SpectralActualityPendingClaimBirth

open CanonicalUnitArithmeticRoot
open CanonicalRiemannAnalyticFacade
open PendingClaimBirth
open SpectralActuality
open SpectralActualityDebt

noncomputable section

/-- Strong package view of the spectral claim component already installed in
the fixed central analytic authority source. -/
abbrev pendingClaimRuntimeFacade :
    SourceNativePendingClaimRuntimeFacade CanonicalUnitArithmeticRoot.N where
  base := CanonicalRiemannAnalyticFacade.commonFacade
  PendingFaceAt := fun _runtime => ProjectionAt
  componentAt := fun _runtime _projection =>
    spectralActualityPendingClaimProjectionLaw
  installationAt := fun _runtime _projection =>
    CanonicalRiemannAnalyticFacade.spectralActualityInstallation
  projectionAt := fun _runtime projection => projection

theorem classifier_eq (projection : ProjectionAt) :
    spectralActualityPendingClaimProjectionLaw.classify projection
        CanonicalRiemannAnalyticFacade.commonFacadeSeed.emittedOccurrence =
      .inl ⟨rfl⟩ := by
  have seedCurrent :
      CanonicalRiemannAnalyticFacade.commonFacadeSeed.current.visit.current =
        initialCurrent := rfl
  simp only [spectralActualityPendingClaimProjectionLaw]
  split
  · apply congrArg Sum.inl
    apply PLift.down_injective
    exact Subsingleton.elim _ _
  · rename_i notInitial
    exact False.elim (notInitial seedCurrent)

/-- Exact active package read at the fixed analytic seed. -/
def installedPendingClaimFace (projection : ProjectionAt) :
    SourceInstalledPendingClaimFaceAt pendingClaimRuntimeFacade
      CanonicalRiemannAnalyticFacade.commonFacadeSeed projection where
  active := ⟨rfl⟩
  classifier_eq := classifier_eq projection

/-- Birth precedes every characteristic landing. -/
def pendingClaimBirth (projection : ProjectionAt) :
    SourceExactPendingClaimBirthReceiptAt pendingClaimRuntimeFacade
      CanonicalRiemannAnalyticFacade.commonFacadeSeed
      CanonicalRiemannAnalyticFacade.commonFacadeSeed.tick
      (installedPendingClaimFace projection) :=
  PendingClaimBirth.generate pendingClaimRuntimeFacade
    CanonicalRiemannAnalyticFacade.commonFacadeSeed
    CanonicalRiemannAnalyticFacade.commonFacadeSeed.tick
    (installedPendingClaimFace projection)

theorem pendingClaimBirth_law (projection : ProjectionAt) :
    (pendingClaimBirth projection).law =
      SpectralActualityDebt.activationLaw projection.event :=
  rfl

theorem pendingClaimBirth_initial (projection : ProjectionAt) :
    HEq (pendingClaimBirth projection).initial
      (SpectralActualityDebt.StateAt.pending :
        SpectralActualityDebt.StateAt projection.event) :=
  HEq.rfl

/-- The new row carries the semantic claim, not the zero proof or a kernel
event payload. -/
theorem pendingClaimBirth_claim (projection : ProjectionAt) :
    (pendingClaimBirth projection).debtEntry.claim =
      .inr (SpectralActualityClaimAt.generate projection.event) :=
  rfl

theorem pendingClaimBirth_budget_positive (projection : ProjectionAt) :
    0 < (pendingClaimBirth projection).debtEntry.progressBudget :=
  (pendingClaimBirth projection).debtEntry_budget_positive

def pendingClaimBirth_target_total (projection : ProjectionAt)
    (entry : (pendingClaimBirth projection).targetLedger.Entry) :
    SourceExactPendingClaimBirthReceiptAt.TargetOriginAt
      (pendingClaimBirth projection) entry :=
  (pendingClaimBirth projection).targetOrigin entry

theorem pendingClaimBirth_has_no_old_origin (projection : ProjectionAt) :
    ¬ Nonempty (ExactTargetDebtOriginAt
      (DebtActivationLedger.inactiveLedger
        (law := (pendingClaimBirth projection).law)
        (pendingClaimBirth projection).sourceLedger.support)
      (pendingClaimBirth projection).debtEntry) := by
  rintro ⟨origin⟩
  exact nomatch origin.excludesFresh
    (pendingClaimBirth projection).debtFresh

theorem pendingClaimBirth_has_no_next (projection : ProjectionAt) :
    IsEmpty (pendingClaimBirth projection).GeneratedNextAt :=
  ⟨fun next => nomatch next⟩

/-- The central named face and the strong package birth read the same source
projection; no sibling facade supplies the claim. -/
theorem central_readout_is_birth_package (projection : ProjectionAt) :
    CanonicalRiemannAnalyticFacade.commonFacade.readoutAt
        CanonicalRiemannAnalyticFacade.commonFacadeSeed
        (.spectralActuality projection) =
      .inl ⟨⟨rfl⟩, projectionPackage projection⟩ :=
  CanonicalRiemannAnalyticFacade.spectralActualitySeed_readout_is_generated
    projection

/-- A settlement can be consumed only downstream; it is not an argument of
the birth constructor. -/
theorem settlement_cannot_fill_birth_mouth
    (projection : ProjectionAt)
    (_settlement : SpectralActualitySettlementAt projection.event) : True := by
  fail_if_success
    exact (show SourceExactPendingClaimBirthReceiptAt
      pendingClaimRuntimeFacade
      CanonicalRiemannAnalyticFacade.commonFacadeSeed
      CanonicalRiemannAnalyticFacade.commonFacadeSeed.tick
      (installedPendingClaimFace projection) from _settlement)
  trivial

end

end SpectralActualityPendingClaimBirth
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
