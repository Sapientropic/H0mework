import H0mework.Versions.AB.Society.Renewal.RootInstalledRenewal
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.LivingLawOperationalSeparationSourceNativeRootRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.LivingLawNoFreeStarvationRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.LivingLawNoFreeWorldSeamRegression

/-!
# M8 temporal-root renewal seam regression

This regression reuses existing roots.  The operational-separation fixture's
`false` consumer has a canonical temporal row and continuing whole-ledger
transition, so it installs operational renewal.  Its `true` sibling has no
selected row.  The existing empty and omitted-row fixtures remain negative
controls: inventory membership cannot renew standing.

These root events are unrelated to the four M8 social domains and are not
projected into them.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8RootInstalledRenewalRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.OperationalSearchSourceNativeRootRegression
open Renewal

/-- Exact temporal root compiler image for the existing positive fixture. -/
def falseTemporalGenerated :=
  (root false).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite falseVisit)

/-- The same whole-ledger image is continuing, not terminal. -/
def falseTemporalSuccessor :
    SourceNativeLedgerGeneratedSuccessorAt
      falseTemporalGenerated.occurrence
      falseTemporalGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    falseTemporalGenerated.wholeLedgerWriteBack).get (by rfl)

/-- Positive operational renewal consumes the already canonical temporal row. -/
def falseRootInstalledRenewal :
    RootInstalledRenewalAt falseTemporalGenerated
      falseDeliveryRootConsumerEntry :=
  RootInstalledRenewalAt.install falseDeliveryGeneratedRow
    falseTemporalSuccessor

/-- Independent responsibility consumer generated from that exact renewal. -/
def falseRenewalConsumer :
    RenewalResponsibilityConsumerAt falseRootInstalledRenewal :=
  falseRootInstalledRenewal.responsibilityConsumer

theorem false_renewal_has_exact_temporal_membership :
    falseRootInstalledRenewal.exactEventMembership =
      falseDeliveryGeneratedRow :=
  rfl

theorem false_renewal_selected_row_commutes_with_world :
    falseRootInstalledRenewal.selected.sourceRow.CommutesWithWorld :=
  falseRootInstalledRenewal.selected_commutes_with_world

theorem false_renewal_budget_not_refilled :
    falseRootInstalledRenewal.operationalStanding.progressBudget ≤
      falseDeliveryRootConsumerEntry.progressBudget :=
  falseRootInstalledRenewal.progressBudget_not_refilled

/-- The sibling temporal visit has no canonical row at its requested
responsibility, so the M8 no-free law rejects operational standing. -/
theorem trueSibling_noOperationalStanding :
    RootInstalledStandingAt
      (root true).toAuthoritativeRoot.toLedgerRoot
      (.finite trueVisit) trueDeliveryRootConsumerEntry → False := by
  apply noTemporalSelectedRow_noOperationalStanding
  intro generated selected
  cases generated
  have isSome :
      (((root true).toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit (.finite trueVisit))
        |>.canonicalGeneratedEntryRow?
          trueDeliveryRootConsumerEntry).isSome = true := by
    unfold SourceNativeTemporalVisitGeneratedEvolutionAt.canonicalGeneratedEntryRow?
    exact sourceNativeFiniteLedgerPatchGeneratedEntry?_isSome
      _ _ _ selected.sourceRow
  rw [true_delivery_consumer_row_is_absent] at isSome
  exact Bool.noConfusion isSome

/-- Existing empty-patch temporal fixture: live presence has no canonical
row at any fresh visit. -/
theorem emptyInventory_noCanonicalRenewalRow :
    IsEmpty
      ((_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.NoFreeStarvationRegression.authorityAt 0).GeneratedEntryRowAt
        _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.SourceNativeLedgerCompilerRegression.falseEntry) :=
  _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.NoFreeStarvationRegression.no_visit_grants_entry_authority 0

/-- One exact existing incidence row reused by the omitted-inventory control. -/
def omittedControlRow : GeneratedLedgerWriteRowAt writeRowSource
    (emitted ()) liveEntry liveEntry :=
  writeRowSource.generate (.transferred () rfl rfl (Nat.le_refl _))

/-- Even two stored copies of an exact row grant no renewal when the world
selector omits both. -/
theorem omittedInventory_noCanonicalRenewalRow :
    ((NoFreeWorldSeamRegression.duplicateIgnoredPatchOf omittedControlRow)
      |>.canonicalGeneratedSourceRow? liveEntry) = none :=
  NoFreeWorldSeamRegression.ignored_rows_generate_no_canonical_authority
    omittedControlRow

/-- Whole seam certificate: operational renewal, its independent consumer,
temporal/world commuting and every focused no-free control are consumed
together. -/
structure RootInstalledRenewalSeamCertificate : Prop where
  positiveInstalled : Nonempty
    (RootInstalledRenewalAt falseTemporalGenerated
      falseDeliveryRootConsumerEntry)
  positiveConsumer : Nonempty
    (RenewalResponsibilityConsumerAt falseRootInstalledRenewal)
  exactTemporalMembership :
    falseRootInstalledRenewal.exactEventMembership =
      falseDeliveryGeneratedRow
  selectedWorldCommutes :
    falseRootInstalledRenewal.selected.sourceRow.CommutesWithWorld
  budgetNotRefilled :
    falseRootInstalledRenewal.operationalStanding.progressBudget ≤
      falseDeliveryRootConsumerEntry.progressBudget
  trueSiblingNoStanding :
    RootInstalledStandingAt
      (root true).toAuthoritativeRoot.toLedgerRoot
      (.finite trueVisit) trueDeliveryRootConsumerEntry → False
  emptyInventoryNoCanonicalRow :
    IsEmpty
      ((_root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.NoFreeStarvationRegression.authorityAt 0).GeneratedEntryRowAt
        _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.SourceNativeLedgerCompilerRegression.falseEntry)
  omittedInventoryNoCanonicalRow :
    ((NoFreeWorldSeamRegression.duplicateIgnoredPatchOf omittedControlRow)
      |>.canonicalGeneratedSourceRow? liveEntry) = none

theorem rootInstalledRenewalSeamDirectConsumer :
    RootInstalledRenewalSeamCertificate where
  positiveInstalled := ⟨falseRootInstalledRenewal⟩
  positiveConsumer := ⟨falseRenewalConsumer⟩
  exactTemporalMembership :=
    false_renewal_has_exact_temporal_membership
  selectedWorldCommutes :=
    false_renewal_selected_row_commutes_with_world
  budgetNotRefilled := false_renewal_budget_not_refilled
  trueSiblingNoStanding := trueSibling_noOperationalStanding
  emptyInventoryNoCanonicalRow := emptyInventory_noCanonicalRenewalRow
  omittedInventoryNoCanonicalRow := omittedInventory_noCanonicalRenewalRow

end M8RootInstalledRenewalRegression
end Society
end ProcessGame
end SaturationMonoid
