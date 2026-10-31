import H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Disposition.SourceGeneratedEssentialAccessCriticalTerminal

/-!
# Root-polymorphic health-cessation renewal law

The exact health action seed, lost power, relation bearer and terminal
responsibility update are compiled into one existing renewal projection
shell.  The law supplies no living root, row, successor, Payment or target;
those remain obligations of a later pre-emitter root assembler.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceHealthCessationRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Renewal
open Lifecycle.Universal.FixedAdapter
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal

abbrev LocalGame := Lifecycle.actualEventGame
abbrev LocalSeed :=
  (essentialAccessCriticalActionController .health).ActionSeed
abbrev LocalSeedAt :=
  (essentialAccessCriticalActionController .health).actionSeedAt

abbrev sourceHealthCessationSeed :=
  exactEssentialAccessCriticalAction .health

structure SourceHealthCessationConsumerAt
    (seed : SourceSeed Lifecycle.actualEventOccurrenceOf LocalSeed
      LocalSeedAt LocalGame.source) : Type where
  private mk ::
  seedExact : seed = sourceHealthCessationSeed
  action : SourceGeneratedEssentialAccessCriticalActionAt .health
  actionExact : action = sourceGeneratedHealthCriticalAction

structure SourceHealthCessationDispositionAt
    (seed : SourceSeed Lifecycle.actualEventOccurrenceOf LocalSeed
      LocalSeedAt LocalGame.source) : Type where
  private mk ::
  seedExact : seed = sourceHealthCessationSeed
  update : EssentialAccessCriticalActualUpdateAt .health
  updateExact : update = sourceGeneratedHealthCriticalActualUpdate

def sourceHealthCessationConsumer :
    SourceHealthCessationConsumerAt sourceHealthCessationSeed :=
  { seedExact := rfl
    action := sourceGeneratedHealthCriticalAction
    actionExact := rfl }

def sourceHealthCessationDisposition :
    SourceHealthCessationDispositionAt sourceHealthCessationSeed :=
  { seedExact := rfl
    update := sourceGeneratedHealthCriticalActualUpdate
    updateExact := rfl }

abbrev SourceHealthCessationRenewalLawAt
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    (source : SourceNativeLedgerSource N RootV) :=
  SourceNativeRenewalProjectionLaw source LocalGame LocalSeed LocalSeedAt
    SourceHealthCessationConsumerAt SourceHealthCessationDispositionAt

/-- Install the exact local action into a later root's existing entry/row/next
shell. -/
def sourceHealthCessationRenewalLaw
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source) :
    SourceHealthCessationRenewalLawAt source :=
  SourceNativeRenewalProjectionLaw.ofRootShell shell
    sourceHealthCessationSeed sourceHealthCessationConsumer
      sourceHealthCessationDisposition

theorem sourceHealthCessationConsumer_exact :
    sourceHealthCessationConsumer.action =
      sourceGeneratedHealthCriticalAction :=
  rfl

theorem sourceHealthCessationDisposition_terminal :
    ∃ archive,
      (essentialAccessCriticalTerminalAt .health).terminal.target.slots[
          (criticalRelationSlot essentialAccessCriticalBearerOf
            .health).val]? = some (.terminal archive) :=
  healthCriticalTerminal_disposition

theorem noHealthCriticalAction_noActiveLawPayload
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (noAction : IsEmpty
      (SourceGeneratedEssentialAccessCriticalActionAt .health))
    (law : SourceHealthCessationRenewalLawAt source)
    {current : RootV.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (active : law.ActiveAt occurrence) : False :=
  noAction.false (law.compile occurrence active).consumer.action

end
end M14SourceHealthCessationRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceHealthCessationRenewal.sourceHealthCessationRenewalLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceHealthCessationRenewal.sourceHealthCessationDisposition_terminal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceHealthCessationRenewal.noHealthCriticalAction_noActiveLawPayload
