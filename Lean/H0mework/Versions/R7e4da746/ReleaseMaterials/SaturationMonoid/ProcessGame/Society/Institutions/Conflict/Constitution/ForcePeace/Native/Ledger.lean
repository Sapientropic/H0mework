import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution
open Reparation.Actual (State run advance openings written_balances run_snoc
  publishAfter publication_consumes_the_retained_visit)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument

theorem any_original_native_step_keeps_every_reparation_balance
    {seed : C} {community : Party → Community} {past : Word}
    (live : State seed community past) (input : Input) (pending : Quantities.Pending (endAt seed past)) :
    (advance live input).stack.balances = live.stack.balances := by
  have empty := (a_competing_input_cannot_add_native_work_to_the_pending_visit _ input pending).2.2.2
  have noOpening : openings seed community past input = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ empty]
    rfl
  rw [written_balances, noOpening, List.map_nil, List.append_nil]
  exact (Reparation.Actual.Allocation.no_original_items_keeps_rows past input live.stack.balances empty).1

theorem every_native_interleaving_carries_the_identical_reparation_balances
    (seed : C) (community : Party → Community) (past wait : Word)
    (within : wait.length ≤ remainingNative (endAt seed past)) :
    (run seed community (past ++ wait)).stack.balances = (run seed community past).stack.balances := by
  induction wait using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton front input earlier =>
    have strict : front.length < remainingNative (endAt seed past) := by
      simp only [List.length_append, List.length_singleton] at within
      omega
    have pending := (exactly_the_original_rank_precedes_the_first_material_visit
      (endAt seed past) front strict.le).mpr strict
    rw [← endAt_append] at pending
    rw [← List.append_assoc, run_snoc, any_original_native_step_keeps_every_reparation_balance _ _ pending]
    exact earlier strict.le

theorem the_original_waiting_prefix_is_accounted_with_all_reparation_balances
    (seed : C) (community : Party → Community) (past wait : Word)
    (within : wait.length ≤ remainingNative (endAt seed past)) :
    let written := publishAfter (run seed community past) wait
    Quantities.Recorded seed (past ++ wait) ∧
      written.next.stack.balances = (run seed community past).stack.balances := by
  refine ⟨(publishAfter (run seed community past) wait).recorded, ?_⟩
  rw [publication_consumes_the_retained_visit]
  exact every_native_interleaving_carries_the_identical_reparation_balances seed community past wait within

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
