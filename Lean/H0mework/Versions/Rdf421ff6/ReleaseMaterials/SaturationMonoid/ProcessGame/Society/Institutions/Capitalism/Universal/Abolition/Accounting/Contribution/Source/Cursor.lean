import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Receipts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root
open Financial.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

private def cursorRun (start : Cursor.State input) (steps : Nat) :
    (Financial.process input).Run start.account.current (((Cursor.next input)^[steps] start).account.current) := by
  induction steps with
  | zero => exact .nil
  | succ steps inherited =>
      rw [Function.iterate_succ_apply']
      exact inherited.concatRuns (Financial.process input) (Cursor.native input _)

abbrev enteringAccount (physical steps : Nat) := Epoch.Finance.Legacy.generated input depth count
  (((Cursor.next input)^[steps] (Cursor.enteringAt input physical)).account)

theorem the_actual_entering_account_has_one_slot_per_original_source (physical steps : Nat) :
    ((enteringAccount input depth count physical steps).current.slots.map
      (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count)).Nodup := by
  rw [(Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained input depth count _).1,List.map_map]
  have oldUnique := every_actual_entering_continuation_has_unique_original_contributions input physical steps
  have mapped := oldUnique.map (f := fun origin =>
    (Epoch.Finance.Origin.original origin : Epoch.Finance.Origin input depth count))
    (fun first second same => Epoch.Finance.Origin.original.inj same)
  have same : ∀ slot : ObligationSlot (Financial.vocabulary input),
      (Epoch.Finance.slotClaim input depth count (Epoch.Finance.Legacy.slot input depth count slot)).origin input depth count =
        Epoch.Finance.Origin.original (Financial.slotClaim input slot).origin := by
    intro slot
    cases slot <;> rfl
  simpa only [List.map_map,Function.comp_def,same] using mapped

def originalEnteringContinuation (physical start later : Nat) :
    (Epoch.Finance.process input depth count).Run
      (enteringAccount input depth count physical start).current
      (enteringAccount input depth count physical (start + later)).current := by
  let oldStart := (Cursor.next input)^[start] (Cursor.enteringAt input physical)
  have oldRun := cursorRun input oldStart later
  have targetEq : (Cursor.next input)^[later] oldStart =
      (Cursor.next input)^[start + later] (Cursor.enteringAt input physical) := by
    rw [Nat.add_comm start later,Function.iterate_add_apply]
  rw [targetEq] at oldRun
  have translated := Epoch.Finance.Legacy.foldRun input depth count oldRun
  have run := translated.run
  rw [translated.faithful] at run
  rw [Epoch.Finance.Legacy.generated_current,Epoch.Finance.Legacy.generated_current]
  exact run

theorem every_actual_cursor_continuation_bounds_the_whole_original_contribution
    (physical start later : Nat)
    (index : Fin (enteringAccount input depth count physical start).current.slots.length) :
    receivedForOrigin input depth count (originalEnteringContinuation input depth count physical start later)
      ((Epoch.Finance.slotClaim input depth count
        ((enteringAccount input depth count physical start).current.slots.get index)).origin input depth count) ≤
      (Epoch.Finance.slotClaim input depth count
        ((enteringAccount input depth count physical start).current.slots.get index)).quantity input depth count :=
  a_source_unique_account_lifts_the_original_slot_bound input depth count _ _ index
    (the_actual_entering_account_has_one_slot_per_original_source input depth count physical (start + later))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source
