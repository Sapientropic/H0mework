import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Readback
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

/-!
# The original-law native finance consumer

Each submitted primitive is interpreted at the cursor carrying its original
prefix. The native fold consumes that physical occurrence's own inventory.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capitalism.Universal.Root Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered

noncomputable section

abbrev depth : Nat := 0
abbrev sourceStart : Nat := 8
abbrev count := Macro.Ingress.cut input depth sourceStart
abbrev Cursor := Physical.Cursor Party Unit Party Bool Unit
abbrev Account := (Epoch.Finance.process input depth count).GeneratedState

def openingNative : Account := (Epoch.Finance.settleCommitted input depth count).after

theorem the_native_cut_reads_the_original_cut :
    (Actual.initial input depth count).raw = cut := by
  change Migration.origin input depth count = cut
  rw [← Migration.Readback.origin_exact]
  unfold Migration.Readback.origin Financial.Installation.Cursor.physicalVisit
  have index :
      Financial.Installation.Cursor.physicalVisitIndex input
        (Financial.Installation.Runtime.cursorAt input depth count) = 2 := by
    decide +kernel
  rw [index]
  rfl

def submitted (cursor : Cursor) (command : Command) : Cursor :=
  Physical.receive cursor (.primitive command)

def nativeTag (cursor : Cursor) (command : Command) : Epoch.Interface.Tag input depth count :=
  .actual 0 0 (submitted cursor command)

def consume (cursor : Cursor) (command : Command) (account : Account) : Account :=
  Epoch.Finance.consumeVisit input depth count (nativeTag cursor command)
    (Epoch.Interface.root input depth count (nativeTag cursor command)).initialVisit account

def nativeFold : Cursor → Account → Word → Cursor × Account
  | cursor, account, [] => (cursor, account)
  | cursor, account, command :: tail =>
      nativeFold (Physical.next (submitted cursor command)) (consume cursor command account) tail

def run (word : Word) : Cursor × Account := nativeFold Physical.initial openingNative word

def raw (word : Word) : State := (Physical.stateAt input depth count 0 0 (run word).1.past).raw

def principals (account : Account) : List (Party × Party × ℚ × ℚ) :=
  account.current.slots.map (fun slot =>
    let claim := Epoch.Finance.slotClaim input depth count slot
    (claim.debtor, claim.holder, claim.quantity,
      Financial.total input (Epoch.Finance.slotBalance input depth count slot)))

def actual_native_run (cursor : Cursor) (account : Account) (word : Word) :
    (Epoch.Finance.process input depth count).Run account.current (nativeFold cursor account word).2.current := by
  induction word generalizing cursor account with
  | nil => exact .nil
  | cons command tail inherited =>
      let tag := nativeTag cursor command
      let step := Epoch.Finance.consumeVisit_run input depth count tag
        (Epoch.Interface.root input depth count tag).initialVisit account
      exact step.concatRuns _ (inherited (Physical.next (submitted cursor command)) (consume cursor command account))

theorem all_runs_preserve_the_original_slot_and_history (word : Word) :
    openingNative.current.slots.map (Epoch.Finance.slotClaim input depth count) <+:
      (run word).2.current.slots.map (Epoch.Finance.slotClaim input depth count) ∧
    openingNative.current.history <+: (run word).2.current.history := by
  have trace := actual_native_run Physical.initial openingNative word
  refine ⟨Epoch.Finance.run_retains_all_claims input depth count trace, ?_⟩
  change openingNative.current.history <+: (nativeFold Physical.initial openingNative word).2.current.history
  rw [trace.history_eq]
  exact List.prefix_append _ _

theorem the_original_slot_is_paid_once_in_each_alternative :
    principals openingNative = [(controller, creditor, 6, 6)] ∧
      principals (run peace).2 = [(controller, creditor, 6, 0)] ∧
      principals (run imposed).2 = [(controller, creditor, 6, 0)] ∧
      principals (run (reattached 6)).2 = [(controller, creditor, 6, 0)] := by
  decide +kernel

theorem exact_native_material_controls :
    stock (raw peace) controller = 4 ∧
      stock (raw imposed) controller = 8 ∧
      stock (raw (reattached 6)) controller = 2 ∧
      stock (raw peace) exposed = 10 ∧
      stock (raw imposed) exposed = 4 ∧
      stock (raw (reattached 6)) exposed = 10 ∧
      total (raw peace) = 21 ∧ total (raw imposed) = 19 ∧ total (raw (reattached 6)) = 19 := by
  decide +kernel

#print axioms actual_native_run
#print axioms all_runs_preserve_the_original_slot_and_history
#print axioms the_original_slot_is_paid_once_in_each_alternative
#print axioms exact_native_material_controls

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers
