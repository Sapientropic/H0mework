import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Tick
import Mathlib.Data.List.Induction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt observedScript)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "History" => Script Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument

variable (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)

/-- Each input consumes the canonical authority of the preceding joint
write. The original current supplies the only source dispatcher. -/
def run (history : History) : State seed community history :=
  List.reverseRecOn (motive := State seed community) history (initialState seed community)
    (fun _ input state => advance state input)

theorem run_nil : run seed community [] = initialState seed community := by
  rw [run, List.reverseRecOn_nil]

theorem run_snoc (past : History) (input : Proposal) :
    run seed community (past ++ [input]) = advance (run seed community past) input := by
  rw [run, List.reverseRecOn_concat]
  rfl

theorem an_observed_policy_uses_each_original_generated_successor
    (policy : Nat → C → Proposal) (tick : Nat) :
    let past := observedScript policy tick seed
    run seed community (observedScript policy (tick + 1) seed) =
      advance (run seed community past) (policy tick (endAt seed past)) :=
  run_snoc seed community _ _

/-- Finite restriction of the source's own damage inventory, preserving
both the dispatcher position and the actual material position. -/
def originalLosses (history : History) : List (Occurrence seed community) :=
  List.reverseRecOn (motive := fun _ => List (Occurrence seed community)) history []
    (fun past input old => old ++ openings seed community past input)

theorem losses_snoc (past : History) (input : Proposal) :
    originalLosses seed community (past ++ [input]) = originalLosses seed community past ++
      openings seed community past input := by
  rw [originalLosses, List.reverseRecOn_concat]
  rfl

theorem the_live_ledger_contains_exactly_the_original_losses (history : History) :
    (run seed community history).stack.balances.map Prod.fst = originalLosses seed community history := by
  induction history using List.reverseRecOn with
  | nil => rw [run_nil, originalLosses, List.reverseRecOn_nil]; rfl
  | append_singleton past input earlier =>
    rw [run_snoc, losses_snoc, each_input_keeps_its_old_claims_and_files_exactly_its_new_damage, earlier]

theorem every_actual_loss_has_its_own_row_on_every_later_current (past suffix : History)
    (origin : Occurrence seed community) (listed : origin ∈ originalLosses seed community past) :
    let reached := run seed community (past ++ suffix)
    ∃ balance, ∃ row, reached.read row = .inr (origin, balance) := by
  have retained : ∀ tail : History, origin ∈ originalLosses seed community (past ++ tail) := by
    intro tail
    induction tail using List.reverseRecOn with
    | nil => simpa only [List.append_nil] using listed
    | append_singleton front input ih =>
      rw [← List.append_assoc, losses_snoc]
      exact List.mem_append_left _ ih
  let reached := run seed community (past ++ suffix)
  have member := retained suffix
  rw [← the_live_ledger_contains_exactly_the_original_losses seed community] at member
  obtain ⟨⟨found, balance⟩, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, exactRow⟩ := reached.every_balance_is_a_row_of_the_current (found, balance) present
  exact ⟨balance, row, exactRow⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
