import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.MigrationRegression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicNativeMigrationInstance

open ProcessGame.Society.PublicFunction.Distributed.Reaction
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev source := Native.MigrationRegression.source
abbrev publicNativeMigrationFacade := Native.Runtime.facade source
abbrev activated := Native.Runtime.activated source

theorem actual_native_migrations_are_consumed_with_the_original_row_and_next
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (source : Machine Party Good Port Technology Instrument) (depth index : Nat)
    (slot : ObligationSlot (Financial.vocabulary source.input))
    (present : (Financial.accountAt source.input (depth + 1)).current.slots[index]? = some slot) :
    let migrated := (Native.generate source depth).migrations index slot present
    let actual := Native.Runtime.activated source (depth + 1)
    Financial.Migration.identity source.input migrated.slot = Financial.Migration.identity source.input slot ∧
      Financial.total source.input (Financial.slotBalance source.input migrated.slot) +
        migrated.path.paid source.input = Financial.total source.input (Financial.slotBalance source.input slot) ∧
      (migrated.path.records source.input index) =
        (Native.generate source depth).financeArrival.events.filter (fun event => event.slot == index) ∧
      HEq ((Native.Runtime.facade source).readoutAt actual .responsibilities)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (Native.Runtime.facade source).process.stateAt
        ((Native.Runtime.facade source).process.successor actual.state) := by
  let migrated := (Native.generate source depth).migrations index slot present
  have factor := (Native.Runtime.facade source).readoutAt_factorizes
    (Native.Runtime.activated source (depth + 1)) .responsibilities
  exact ⟨migrated.path.preserves_identity source.input, migrated.path.conservation source.input,
    migrated.recorded, factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem named_actual_repayment_keeps_the_original_admission_and_own_root :
    Financial.Migration.identity source.input Native.MigrationRegression.evolution.slot =
        Financial.Migration.identity source.input Native.MigrationRegression.oldSlot ∧
      Native.MigrationRegression.evolution.path.paid source.input = 2 ∧
      HEq (publicNativeMigrationFacade.readoutAt (activated 4) .responsibilities)
        ((activated 4).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 4).tick.generated.wholeLedgerWriteBack
        ((activated 4).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 4).current.visit.current) ∧
      (activated 4).tick.nextCurrent = publicNativeMigrationFacade.process.stateAt
        (publicNativeMigrationFacade.process.successor (activated 4).state) := by
  have migration := Native.MigrationRegression.actual_slot_migration_changes_residual_without_rewriting_admission
  have factor := publicNativeMigrationFacade.readoutAt_factorizes (activated 4) .responsibilities
  exact ⟨migration.1, migration.2.2.2.1, factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.Tracks.LivingLawPublicNativeMigrationInstance
