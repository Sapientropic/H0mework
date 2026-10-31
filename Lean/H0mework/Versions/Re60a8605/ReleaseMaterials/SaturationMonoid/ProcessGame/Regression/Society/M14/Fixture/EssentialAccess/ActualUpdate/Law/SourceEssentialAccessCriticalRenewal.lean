import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Law.SourceHealthCessationRenewal

/-!
# Event-dependent essential-access critical renewal

Each existing `EssentialAccessEvent` generates its own exact action seed,
critical-action consumer and terminal actual-update disposition.  These are
installed into the existing root shell; this file introduces no relation
compiler, process, registry, ledger, occurrence or root.

The event is a subordinate dependent-family index only.  It is not the whole
authority selector: a later source-owned root selector must still choose which
family member is installed before emission.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceEssentialAccessCriticalRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Renewal
open Lifecycle.Universal.FixedAdapter
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceHealthCessationRenewal

abbrev LocalGame := Lifecycle.actualEventGame

abbrev EssentialAccessCriticalLocalSeed (event : EssentialAccessEvent) :=
  (essentialAccessCriticalActionController event).ActionSeed

abbrev EssentialAccessCriticalLocalSeedAt (event : EssentialAccessEvent) :=
  (essentialAccessCriticalActionController event).actionSeedAt

abbrev sourceEssentialAccessCriticalSeed (event : EssentialAccessEvent) :=
  exactEssentialAccessCriticalAction event

/-! ## Event-generated local payload -/

structure SourceEssentialAccessCriticalConsumerAt
    (event : EssentialAccessEvent)
    (seed : SourceSeed Lifecycle.actualEventOccurrenceOf
      (EssentialAccessCriticalLocalSeed event)
      (EssentialAccessCriticalLocalSeedAt event) LocalGame.source) : Type where
  private mk ::
  seedExact : seed = sourceEssentialAccessCriticalSeed event
  action : SourceGeneratedEssentialAccessCriticalActionAt event
  actionExact : action =
    sourceGeneratedEssentialAccessCriticalActionAt event

structure SourceEssentialAccessCriticalDispositionAt
    (event : EssentialAccessEvent)
    (seed : SourceSeed Lifecycle.actualEventOccurrenceOf
      (EssentialAccessCriticalLocalSeed event)
      (EssentialAccessCriticalLocalSeedAt event) LocalGame.source) : Type where
  private mk ::
  seedExact : seed = sourceEssentialAccessCriticalSeed event
  update : EssentialAccessCriticalActualUpdateAt event
  updateExact : update =
    sourceGeneratedEssentialAccessCriticalActualUpdateAt event

def sourceEssentialAccessCriticalConsumer (event : EssentialAccessEvent) :
    SourceEssentialAccessCriticalConsumerAt event
      (sourceEssentialAccessCriticalSeed event) :=
  { seedExact := rfl
    action := sourceGeneratedEssentialAccessCriticalActionAt event
    actionExact := rfl }

def sourceEssentialAccessCriticalDisposition (event : EssentialAccessEvent) :
    SourceEssentialAccessCriticalDispositionAt event
      (sourceEssentialAccessCriticalSeed event) :=
  { seedExact := rfl
    update := sourceGeneratedEssentialAccessCriticalActualUpdateAt event
    updateExact := rfl }

theorem sourceEssentialAccessCriticalPayload_exact
    (event : EssentialAccessEvent) :
    (sourceEssentialAccessCriticalConsumer event).action =
        sourceGeneratedEssentialAccessCriticalActionAt event ∧
      (sourceEssentialAccessCriticalDisposition event).update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt event ∧
      (∃ archive,
        (essentialAccessCriticalTerminalAt event).terminal.target.slots[
            (criticalRelationSlot essentialAccessCriticalBearerOf event).val]? =
          some (.terminal archive)) ∧
      (∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
        IsEmpty ((criticalRelationTerminalProcess
          essentialAccessCriticalBearerOf).ReopenEvent archive)) :=
  ⟨rfl, rfl,
    (essentialAccessCriticalTerminalAt event).terminalDisposition,
    (essentialAccessCriticalTerminalAt event).noReopen⟩

/-! ## Root-polymorphic dependent law family -/

abbrev SourceEssentialAccessCriticalRenewalLawAt
    (event : EssentialAccessEvent)
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    (source : SourceNativeLedgerSource N RootV) :=
  SourceNativeRenewalProjectionLaw source LocalGame
    (EssentialAccessCriticalLocalSeed event)
    (EssentialAccessCriticalLocalSeedAt event)
    (SourceEssentialAccessCriticalConsumerAt event)
    (SourceEssentialAccessCriticalDispositionAt event)

/-- Install the event-generated payload into an already existing root shell. -/
def sourceEssentialAccessCriticalRenewalLaw
    (event : EssentialAccessEvent)
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source) :
    SourceEssentialAccessCriticalRenewalLawAt event source :=
  SourceNativeRenewalProjectionLaw.ofRootShell shell
    (sourceEssentialAccessCriticalSeed event)
    (sourceEssentialAccessCriticalConsumer event)
    (sourceEssentialAccessCriticalDisposition event)

/-- Every existing event generates one law over the same existing shell.  The
quantifier does not select a whole-root installation. -/
theorem everyEssentialAccessEvent_generatesCriticalRenewalLaw
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source) :
    ∀ event : EssentialAccessEvent,
      Nonempty (SourceEssentialAccessCriticalRenewalLawAt event source) :=
  fun event => ⟨sourceEssentialAccessCriticalRenewalLaw event shell⟩

/-- Direct all-event consumer of the generated law.  The root row and
successor remain those selected by `shell`; the event controls only the exact
local seed, action and disposition. -/
theorem sourceEssentialAccessCriticalRenewalLaw_directConsumer
    (event : EssentialAccessEvent)
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source)
    {current : RootV.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (active : shell.ActiveAt occurrence) :
    let law := sourceEssentialAccessCriticalRenewalLaw event shell
    (law.compile occurrence active).sourceSeed =
        sourceEssentialAccessCriticalSeed event ∧
      (law.compile occurrence active).consumer.action =
        sourceGeneratedEssentialAccessCriticalActionAt event ∧
      (law.compile occurrence active).disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt event ∧
      (law.compile occurrence active).sourceEntry =
        shell.sourceEntry occurrence active ∧
      HEq (law.compile occurrence active).selectedRow
        (shell.selectedRow occurrence active) ∧
      HEq (law.compile occurrence active).successor
        (shell.successor occurrence active) :=
  ⟨rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩

theorem everyEssentialAccessEvent_consumesCriticalRenewalLaw
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source)
    {current : RootV.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (active : shell.ActiveAt occurrence) :
    ∀ event : EssentialAccessEvent,
      let law := sourceEssentialAccessCriticalRenewalLaw event shell
      (law.compile occurrence active).sourceSeed =
          sourceEssentialAccessCriticalSeed event ∧
        (law.compile occurrence active).consumer.action =
          sourceGeneratedEssentialAccessCriticalActionAt event ∧
        (law.compile occurrence active).disposition.update =
          sourceGeneratedEssentialAccessCriticalActualUpdateAt event ∧
        (law.compile occurrence active).sourceEntry =
          shell.sourceEntry occurrence active ∧
        HEq (law.compile occurrence active).selectedRow
          (shell.selectedRow occurrence active) ∧
        HEq (law.compile occurrence active).successor
          (shell.successor occurrence active) :=
  fun event =>
    sourceEssentialAccessCriticalRenewalLaw_directConsumer event shell
      occurrence active

/-! ## Exact health recovery -/

@[simp] theorem sourceEssentialAccessCriticalSeed_health :
    sourceEssentialAccessCriticalSeed .health =
      sourceHealthCessationSeed :=
  rfl

@[simp] theorem sourceEssentialAccessCriticalConsumer_health_action :
    (sourceEssentialAccessCriticalConsumer .health).action =
      sourceHealthCessationConsumer.action :=
  rfl

@[simp] theorem sourceEssentialAccessCriticalDisposition_health_update :
    (sourceEssentialAccessCriticalDisposition .health).update =
      sourceHealthCessationDisposition.update :=
  rfl

/-- The generic health member and the fixed health law consume the same shell,
seed, action, update, ledger row and successor.  Their wrapper types differ,
but all authoritative faces are definitionally identical. -/
theorem sourceEssentialAccessCriticalHealthLaw_exactRecovery
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source)
    {current : RootV.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (active : shell.ActiveAt occurrence) :
    let generic :=
      sourceEssentialAccessCriticalRenewalLaw .health shell
    let fixed := sourceHealthCessationRenewalLaw shell
    HEq (generic.compile occurrence active).sourceSeed
        (fixed.compile occurrence active).sourceSeed ∧
      (generic.compile occurrence active).consumer.action =
        (fixed.compile occurrence active).consumer.action ∧
      (generic.compile occurrence active).disposition.update =
        (fixed.compile occurrence active).disposition.update ∧
      HEq (generic.compile occurrence active).sourceEntry
        (fixed.compile occurrence active).sourceEntry ∧
      HEq (generic.compile occurrence active).selectedRow
        (fixed.compile occurrence active).selectedRow ∧
      HEq (generic.compile occurrence active).successor
        (fixed.compile occurrence active).successor :=
  ⟨HEq.rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

/-! ## Exact mismatch control -/

def SourceEssentialAccessCriticalRenewalEventMismatchAt
    (expected actual : EssentialAccessEvent) : Prop :=
  (essentialAccessCriticalActionController expected).actionAdmittedAt actual

theorem sourceEssentialAccessCriticalRenewalEventMismatch_isEmpty
    {expected actual : EssentialAccessEvent}
    (different : actual ≠ expected) :
    IsEmpty
      (SourceEssentialAccessCriticalRenewalEventMismatchAt expected actual) :=
  ⟨fun replay =>
    essentialAccessCriticalController_rejects_mismatch different replay⟩

end
end M14SourceEssentialAccessCriticalRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialAccessCriticalRenewal.sourceEssentialAccessCriticalPayload_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialAccessCriticalRenewal.sourceEssentialAccessCriticalRenewalLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialAccessCriticalRenewal.sourceEssentialAccessCriticalRenewalLaw_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialAccessCriticalRenewal.everyEssentialAccessEvent_consumesCriticalRenewalLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialAccessCriticalRenewal.sourceEssentialAccessCriticalHealthLaw_exactRecovery
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialAccessCriticalRenewal.sourceEssentialAccessCriticalRenewalEventMismatch_isEmpty
