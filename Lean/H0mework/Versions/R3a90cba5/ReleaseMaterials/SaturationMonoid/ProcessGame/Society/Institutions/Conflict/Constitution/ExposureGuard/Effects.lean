import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Dispatch
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.MaterialSupport
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Consent

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt next query inventory)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

theorem every_actual_item_has_already_dropped_the_claimed_consent_list
    (cut : C) (input : Input) (item : Item) (listed : item ∈ Boundary.Actual.items cut input) :
    item.request.consents = [] := by
  let asked := query cut input
  change item ∈ Optimality.Programme.Epoch.materialItems asked ++ [] at listed
  rw [List.append_nil] at listed
  unfold Optimality.Programme.Epoch.materialItems at listed
  split at listed
  · exact (List.not_mem_nil listed).elim
  · rw [Optimality.Programme.Epoch.the_epoch_physical_result_is_the_original_selected_compilation] at listed
    exact Physical.Public.every_actual_public_instruction_has_no_controller_consent _ _ _ item listed

private theorem total_debit_le_credit (cut : C) (person : Party) (good : Good) (items : List Item)
    (unspent : ∀ item ∈ items, netDebit cut item person good ≤ 0) :
    (physical cut).totalDebit items person good ≤ (physical cut).totalCredit items person good := by
  induction items with
  | nil => exact le_rfl
  | cons item rest earlier =>
    simp only [RawLaw.totalDebit, RawLaw.totalCredit, List.map_cons, List.sum_cons]
    exact add_le_add (sub_nonpos.mp (unspent item List.mem_cons_self))
      (earlier (fun later listed => unspent later (List.mem_cons_of_mem _ listed)))

variable {seed : Root.Cut Party Good Port Technology Instrument}
  (roster : List Party) (answers : OwnerAnswers seed)
  (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)
  (person : Party) (original : person ∈ roster)

include original

theorem each_admitted_rival_input_preserves_the_refusers_original_stock
    (admitted : Admitted roster (withhold answers person) past input) (good : Good) :
    (endAt seed past).raw.stock person good ≤ (next (endAt seed past) input).raw.stock person good := by
  let cut := endAt seed past
  let items := originalItems (seed := seed) past input
  have noLoss : ∀ item ∈ items, netDebit cut item person good ≤ 0 := by
    intro item listed
    obtain ⟨index, selected⟩ := List.getElem?_of_mem listed
    obtain ⟨inside, same⟩ := List.getElem?_eq_some_iff.mp selected
    have atPosition := a_withholding_bearer_cannot_be_charged_by_any_actual_item roster answers past input
      person original ⟨index, inside⟩ admitted.2 good
    change netDebit cut items[index] person good ≤ 0 at atPosition
    rwa [same] at atPosition
  have spent := total_debit_le_credit cut person good items noLoss
  have balance := Quantities.all_capacity_is_paid_from_the_original_stock_and_actual_credits cut [input] person good
  change (next cut input).raw.stock person good + (physical cut).totalDebit items person good =
    cut.raw.stock person good + (physical cut).totalCredit items person good at balance
  linarith

/-- Quantification over the actual material inventory covers every
command name, technology, controller and dispatch route of the source. -/
theorem no_admitted_rival_opcode_can_charge_a_withholding_bearer :
    ¬ ∃ (attempt : Input) (position : Fin (originalItems (seed := seed) past attempt).length) (good : Good),
      Admitted roster (withhold answers person) past attempt ∧
        0 < netDebit (endAt seed past) (originalItems (seed := seed) past attempt)[position] person good := by
  rintro ⟨attempt, position, good, admitted, positive⟩
  exact (not_lt_of_ge (a_withholding_bearer_cannot_be_charged_by_any_actual_item roster answers past attempt
    person original position admitted.2 good)) positive

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
