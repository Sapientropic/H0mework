import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Effects

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

abbrev receipts (shared : Bool) (count : Nat) := SharedAudit.receipts (source shared) count

theorem receipt_machine (shared : Bool) (count : Nat) :
    receipts shared count = (List.range count).flatMap (itemsAt shared) := by
  apply List.flatMap_congr
  intro ordinal _inside
  change law.rawItems _ _ = _
  rw [← ((source shared).canonical_frame ordinal).1, ← ((source shared).canonical_frame ordinal).2,
    actual_current_is_the_machine, actual_word_is_the_machine]
  rfl

theorem all_actual_flow_addresses_are_bounded : ∀ shared : Bool,
    ∀ item ∈ receipts shared 25, ∀ entry ∈ law.actualDebit item.before item.request ++ law.actualCredit item.before item.request,
      entry.1.1 < 6 := by
  intro shared
  rw [receipt_machine]
  cases shared <;> decide +kernel

private theorem zero_flow (shared : Bool) (actor : Party) (outside : 6 ≤ actor)
    (item : Born.Item) (member : item ∈ receipts shared 25) (good : Good) :
    flowAt (law.actualDebit item.before item.request) actor good = 0 ∧
      flowAt (law.actualCredit item.before item.request) actor good = 0 := by
  have zero (flow : Flow Party Good) (bounded : ∀ entry ∈ flow, entry.1.1 < 6) : flowAt flow actor good = 0 := by
    unfold flowAt amount
    apply List.sum_eq_zero
    intro value present
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp present
    have different : entry.1 ≠ (actor, good) := by
      intro same
      have bound := bounded entry inside
      have equal := congrArg Prod.fst same
      have too_small : actor < 6 := by simpa only [equal] using bound
      exact Nat.not_lt_of_ge outside too_small
    simp only [if_neg different]
  exact ⟨zero _ (fun entry inside => all_actual_flow_addresses_are_bounded shared item member entry
    (List.mem_append_left _ inside)), zero _ (fun entry inside =>
      all_actual_flow_addresses_are_bounded shared item member entry (List.mem_append_right _ inside))⟩

theorem outside_totals (shared : Bool) (actor : Party) (outside : 6 ≤ actor) (good : Good) :
    law.totalDebit (receipts shared 25) actor good = 0 ∧ law.totalCredit (receipts shared 25) actor good = 0 := by
  constructor
  all_goals
    first | unfold RawLaw.totalDebit | unfold RawLaw.totalCredit
    apply List.sum_eq_zero
    intro value present
    obtain ⟨item, member, rfl⟩ := List.mem_map.mp present
    first | exact (zero_flow shared actor outside item member good).1
          | exact (zero_flow shared actor outside item member good).2

theorem outside_inventory (shared : Bool) (actor : Party) (outside : 6 ≤ actor) (good : Good) :
    ((source shared).currentAt 25).stock actor good = 0 := by
  have balance := SharedAudit.receipt_balance (source shared) 25 actor good
  have debit := (outside_totals shared actor outside good).1
  have credit := (outside_totals shared actor outside good).2
  change ((source shared).frameAt 25).raw.stock actor good + law.totalDebit (receipts shared 25) actor good =
    initial.stock actor good + law.totalCredit (receipts shared 25) actor good at balance
  rw [debit, credit] at balance
  have zero : initial.stock actor good = 0 := by
    have a : actor ≠ 0 := by intro same; subst actor; norm_num at outside
    have b : actor ≠ 1 := by intro same; subst actor; norm_num at outside
    have c : actor ≠ 2 := by intro same; subst actor; norm_num at outside
    have d : actor ≠ 3 := by intro same; subst actor; norm_num at outside
    simp [initial, a, b, c, d]
  rw [← ((source shared).canonical_frame 25).1] at balance
  linarith

theorem complete_inventory_difference (actor : Party) (good : Good) :
    ((source true).currentAt 25).stock actor good = ((source false).currentAt 25).stock actor good +
      if actor = 0 ∧ good = .labor then 1 else 0 := by
  by_cases bounded : actor < 6
  · rw [actual_current_is_the_machine, actual_current_is_the_machine]
    exact full_final_inventory_difference ⟨actor, bounded⟩ good
  · have outside := Nat.le_of_not_gt bounded
    rw [outside_inventory true actor outside, outside_inventory false actor outside,
      if_neg (by rintro ⟨zero, _⟩; subst actor; norm_num at outside)]
    norm_num

theorem complete_credits_equal (actor : Party) (good : Good) :
    law.totalCredit (receipts true 25) actor good = law.totalCredit (receipts false 25) actor good := by
  by_cases bounded : actor < 6
  · have finite : ∀ address : Fin 6, ∀ unit : Good,
        law.totalCredit (receipts true 25) address unit = law.totalCredit (receipts false 25) address unit := by
      rw [receipt_machine, receipt_machine]
      decide +kernel
    exact finite ⟨actor, bounded⟩ good
  · exact (outside_totals true actor (Nat.le_of_not_gt bounded) good).2.trans
      (outside_totals false actor (Nat.le_of_not_gt bounded) good).2.symm

theorem complete_debit_difference (actor : Party) (good : Good) :
    law.totalDebit (receipts true 25) actor good + (if actor = 0 ∧ good = .labor then 1 else 0) =
      law.totalDebit (receipts false 25) actor good := by
  have left := SharedAudit.receipt_balance (source true) 25 actor good
  have right := SharedAudit.receipt_balance (source false) 25 actor good
  change ((source true).frameAt 25).raw.stock actor good + law.totalDebit (receipts true 25) actor good =
    initial.stock actor good + law.totalCredit (receipts true 25) actor good at left
  change ((source false).frameAt 25).raw.stock actor good + law.totalDebit (receipts false 25) actor good =
    initial.stock actor good + law.totalCredit (receipts false 25) actor good at right
  rw [← ((source true).canonical_frame 25).1, complete_inventory_difference, complete_credits_equal] at left
  rw [← ((source false).canonical_frame 25).1] at right
  linarith

def dividend : ℚ := law.totalDebit (receipts false 25) 0 .labor - law.totalDebit (receipts true 25) 0 .labor

theorem extended_strict_dividend : dividend = 1 ∧ 0 < dividend := by
  have paid := complete_debit_difference 0 .labor
  simp only [true_and, ↓reduceIte] at paid
  unfold dividend
  constructor <;> linarith

abbrev account (shared : Bool) (ordinal : Nat) := Financial.accountAt (source shared).input ordinal

theorem financial_matrix (shared : Bool) (ordinal : Nat) :
    Financial.BalanceConservation.ledgerClaims (source shared).input (account shared ordinal).current =
      ((source shared).currentAt ordinal).claims :=
  Financial.BalanceConservation.generated_prefix_claims (source shared).input rfl ordinal

private def archived (shared : Bool) (slot : ObligationSlot (Financial.vocabulary (source shared).input)) : Prop :=
  match slot with | .terminal _ => True | .live _ => False

private instance (shared : Bool) (slot : ObligationSlot (Financial.vocabulary (source shared).input)) : Decidable (archived shared slot) := by
  cases slot <;> unfold archived <;> infer_instance

theorem original_debt_remains_archived (shared : Bool) :
    ∀ slot ∈ (account shared 25).current.slots, archived shared slot := by
  cases shared <;> decide +kernel

theorem all_claims_zero (shared : Bool) (instrument : Unit) (debtor holder : Party) :
    ((source shared).currentAt 25).claims instrument debtor holder = 0 := by
  rw [← financial_matrix]
  unfold Financial.BalanceConservation.ledgerClaims
  apply List.sum_eq_zero
  intro value present
  obtain ⟨slot, member, rfl⟩ := List.mem_map.mp present
  have terminal := original_debt_remains_archived shared slot member
  cases slot with
  | terminal archive => exact Financial.BalanceConservation.slotClaims_terminal _ _ _ _ _
  | live obligation => exact terminal.elim

theorem full_carrier_has_exactly_the_same_dividend :
    (source true).currentAt 25 = withLabor ((source false).currentAt 25) 1 := by
  apply RawCurrent.ext
  · funext actor good; exact complete_inventory_difference actor good
  · funext instrument debtor holder
    exact (all_claims_zero true instrument debtor holder).trans (all_claims_zero false instrument debtor holder).symm
  all_goals
    simp only [actual_current_is_the_machine]
    decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
