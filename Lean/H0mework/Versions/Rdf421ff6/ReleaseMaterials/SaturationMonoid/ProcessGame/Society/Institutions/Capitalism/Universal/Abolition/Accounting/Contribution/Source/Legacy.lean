import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Accounts
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.Run
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Invariants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

private theorem translated_slot_keeps_its_original_origin
    (slot : ObligationSlot (Financial.vocabulary input)) :
    (Epoch.Finance.slotClaim input depth count (Epoch.Finance.Legacy.slot input depth count slot)).origin input depth count =
      Epoch.Finance.Origin.original (Financial.slotClaim input slot).origin := by
  cases slot <;> rfl

private theorem faithful_translation_keeps_source_uniqueness
    (old : (Financial.process input).GeneratedState)
    (unique : (old.current.slots.map (fun slot => (Financial.slotClaim input slot).origin)).Nodup) :
    ((Epoch.Finance.Legacy.generated input depth count old).current.slots.map
      (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)).Nodup := by
  rw [(Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained input depth count old).1,List.map_map]
  have mapped := unique.map (f := fun origin =>
    (Epoch.Finance.Origin.original origin : Epoch.Finance.Origin input depth count))
    (fun first second same => Epoch.Finance.Origin.original.inj same)
  simpa only [List.map_map,Function.comp_def,translated_slot_keeps_its_original_origin] using mapped

theorem the_actual_translated_account_has_one_slot_per_original_source (cut : Nat) :
    ((Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input cut)).current.slots.map
      (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)).Nodup :=
  faithful_translation_keeps_source_uniqueness input depth count _
    (each_actual_account_has_at_most_one_slot_per_original_contribution input cut)

theorem the_actual_translated_registered_account_has_one_slot_per_original_source (sourceDepth sourceCount : Nat) :
    ((Epoch.Finance.Legacy.generated input depth count
      ((Financial.Installation.Runtime.frames input sourceDepth sourceCount).cursor input).account).current.slots.map
        (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)).Nodup :=
  faithful_translation_keeps_source_uniqueness input depth count _
    (every_registered_old_account_has_unique_original_contributions input sourceDepth sourceCount)

def originalSourceContinuation (cut later : Nat) :
    (Epoch.Finance.process input depth count).Run
      (Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input cut)).current
      (Epoch.Finance.Legacy.generated input depth count (Financial.accountAt input (cut + later))).current := by
  have translated := Epoch.Finance.Legacy.foldRun input depth count
    (Financial.BalanceConservation.fromActualCut input cut later)
  have run := translated.run
  rw [translated.faithful] at run
  rw [Epoch.Finance.Legacy.generated_current,Epoch.Finance.Legacy.generated_current]
  exact run

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source
