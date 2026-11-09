import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.History
import Mathlib.Data.List.Nodup

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "History" => Script Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument

variable (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)

theorem openings_are_at_their_original_cut (past : History) (input : Proposal)
    {origin : Occurrence seed community} (listed : origin ∈ openings seed community past input) :
    origin.past = past := by
  obtain ⟨damage, _, rfl⟩ := List.mem_map.mp listed
  rfl

theorem every_origin_is_earlier_than_its_readback (history : History)
    {origin : Occurrence seed community} (listed : origin ∈ originalLosses seed community history) :
    origin.past.length < history.length := by
  induction history using List.reverseRecOn with
  | nil =>
    rw [originalLosses, List.reverseRecOn_nil] at listed
    exact (List.not_mem_nil listed).elim
  | append_singleton past input prior =>
    rw [losses_snoc] at listed
    rw [List.length_append, List.length_singleton]
    rcases List.mem_append.mp listed with old | new
    · exact (prior old).trans (Nat.lt_succ_self _)
    · rw [openings_are_at_their_original_cut _ _ _ _ new]
      exact Nat.lt_succ_self _

private theorem new_addresses_are_distinct (past : History) (input : Proposal) :
    ((openings seed community past input).map Occurrence.address).Nodup := by
  rw [openings, List.map_map]
  apply (Boundary.Actual.each_damage_address_occurs_once _ _ _).map
  intro left right same
  apply Subtype.ext
  exact Prod.ext (Fin.ext (congrArg (fun address => address.2.1) same))
    (congrArg (fun address => address.2.2) same)

theorem one_original_loss_has_one_address_on_the_whole_trajectory (history : History) :
    ((originalLosses seed community history).map Occurrence.address).Nodup := by
  induction history using List.reverseRecOn with
  | nil => rw [originalLosses, List.reverseRecOn_nil]; exact List.nodup_nil
  | append_singleton past input prior =>
    rw [losses_snoc, List.map_append, List.nodup_append']
    refine ⟨prior, new_addresses_are_distinct seed community past input, ?_⟩
    intro addr previous later
    obtain ⟨old, inPast, rfl⟩ := List.mem_map.mp previous
    obtain ⟨fresh, inTick, same⟩ := List.mem_map.mp later
    have earlier := every_origin_is_earlier_than_its_readback seed community past inPast
    have collision : fresh.past.length = old.past.length := congrArg Prod.fst same
    rw [openings_are_at_their_original_cut _ _ _ _ inTick] at collision
    exact (Nat.ne_of_gt earlier) collision

theorem original_addresses_are_distinct_in_the_installed_whole_ledger (history : History) :
    (((run seed community history).stack.balances.map Prod.fst).map Occurrence.address).Nodup := by
  rw [the_live_ledger_contains_exactly_the_original_losses]
  exact one_original_loss_has_one_address_on_the_whole_trajectory seed community history

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
