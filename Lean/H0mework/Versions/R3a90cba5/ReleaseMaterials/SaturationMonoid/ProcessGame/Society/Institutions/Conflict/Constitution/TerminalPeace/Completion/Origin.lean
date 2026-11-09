import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Consumer
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal.Cofinality

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Renewal Installation
open private install installAction from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Write

noncomputable section

abbrev anchor := Settlement.settledHistory

theorem the_original_payment_releases_the_living_reserve :
    Supply.Stocked (originalNative anchor).raw := by
  change Supply.Stocked Settlement.settledCut.raw
  rw [Settlement.settled_raw]
  intro person
  cases person <;> decide +kernel

private theorem firstAdmission : Admission (originalNative anchor) service
    (serviceReplies (originalNative anchor) false) :=
  the_service_is_admitted_from_its_current_stock _ the_original_payment_releases_the_living_reserve false

/-- First living write on the settled original account. Its new material
coordinate is read at the exact generated root visit. -/
def peace : Ready anchor :=
  ⟨install Settlement.settled service firstAdmission, firstAdmission.stocked⟩

theorem the_first_peace_write_is_the_original_whole_successor :
    (⟨Settlement.settled.world,
      (installAction Settlement.settled service firstAdmission).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = peace.val.state.resident.erase :=
  install_is_the_canonical_whole_write Settlement.settled service firstAdmission

theorem the_first_peace_write_carries_each_original_row :
    let written := (installAction Settlement.settled service firstAdmission).target.firstSuccessor.ledgerEvolution
    let original := (Reparation.Actual.identityWhole Settlement.settled.resident.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  install_keeps_every_original_row Settlement.settled service firstAdmission

theorem the_first_peace_write_clears_the_original_loss_but_keeps_its_address :
    peace.val.state.stack.balances = [(Original.occurrence, Settlement.clearedBalance)] :=
  (congrArg _ (install_keeps_the_exact_original_stack Settlement.settled service firstAdmission)).trans
    Settlement.settled_balances

theorem the_first_peace_write_reads_the_paid_current :
    peace.val.native.raw = { Original.snapshot 117 107 with clock := 5, round := 5 } := by
  change (readAction (originalNative anchor) service).next.raw = _
  rw [the_service_raw _ the_original_payment_releases_the_living_reserve false]
  change ({ Settlement.settledCut.raw with clock := Settlement.settledCut.raw.clock + 1, round := Settlement.settledCut.raw.round + 1 } : Original.Raw) = _
  rw [Settlement.settled_raw]
  apply RawCurrent.ext
  · rfl
  · rfl
  · rfl
  · decide +kernel
  · decide +kernel

theorem the_first_peace_write_pays_each_person (person : Bool) :
    foodPaid peace.val.items person = 1 :=
  the_service_pays_exactly_one_to_each_original_person _ the_original_payment_releases_the_living_reserve false person

theorem the_first_peace_write_has_no_new_damage : NoNewDamage peace.val := by
  intro item written key
  obtain ⟨index, inside, same⟩ := List.mem_iff_getElem.mp written
  exact (same ▸ (firstAdmission.owns ⟨index, inside⟩).1).no_damage key

theorem the_first_peace_write_keeps_each_item_exit : ItemExits peace.val.items :=
  admitted_items_have_independent_exits _ _ firstAdmission

theorem the_independent_living_unit_is_at_its_actual_first_positions (person : Bool) :
    ∃ work ∈ peace.val.items, ∃ meal ∈ peace.val.items,
      work.request = Supply.grow person ∧
      meal.request = Conflict.Consumers.Evolving.life person ∧
      work.request.signer = person ∧ meal.request.signer = person ∧
      work.index + 1 = meal.index ∧
      work.before = (originalNative anchor).raw ∧
      meal.before = Supply.physical.step work.before work.request ∧
      Supply.physical.actualDebit work.before work.request = [((person, false), 18)] ∧
      Supply.physical.actualCredit work.before work.request = [((person, false), 18), ((person, true), 1)] ∧
      Supply.physical.actualDebit meal.before meal.request = [((person, true), 1)] ∧
      work.index = (if person = false then 0 else 2) :=
  Supply.the_ordered_native_renewal_contains_each_persons_paid_work_and_meal
    _ the_original_payment_releases_the_living_reserve false person

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion

-- These dependent ledger terms are expensive to expand in the suggestion index.
run_cmd Lean.modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "the_first_peace_write_is_the_original_whole_successor"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "the_first_peace_write_carries_each_original_row"
