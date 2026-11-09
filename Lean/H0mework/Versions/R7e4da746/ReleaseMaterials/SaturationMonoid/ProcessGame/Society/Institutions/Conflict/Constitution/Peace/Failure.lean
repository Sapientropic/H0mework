import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.AttackOrigin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Reparation.Actual (Occurrence Published run publishAfter originalLosses losses_snoc
  publication_consumes_the_retained_visit
  the_live_ledger_contains_exactly_the_original_losses)
open Quantities.Execution (endAt endAt_append)

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community] {Observation : Type u}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "Strategy" => History Observation → Word

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {past : Script Party Good Port Technology Instrument} {command : List Party}
  {observe : Root.Cut Party Good Port Technology Instrument → Observation}
  {strategy : History Observation → Script Party Good Port Technology Instrument}
  {rival : List (Script Party Good Port Technology Instrument)}

local notation "origin" => endAt seed past
local notation "First" => FirstFailureWithExit origin command community observe strategy rival

private def prependAttack {word : Word} (attack : OriginalAttack origin community word) :
    OriginalAttack seed community (past ++ word) :=
  ⟨⟨past ++ attack.val.past, attack.val.input, (endAt_append seed past attack.val.past).symm ▸ attack.val.damage⟩,
    (congrArg (past ++ ·) attack.property).trans (List.append_assoc _ _ _).symm⟩

/-- The failed branch consumes exactly through the first failed input.
The first issue and original damage remain attached to the same prefix. -/
def failedWrite (first : First) : Published seed community (past ++ first.originalScript) :=
  publishAfter (run seed community past) first.originalScript

def firstRootAttack (first : First) : Option (OriginalAttack seed community (past ++ first.originalScript)) :=
  first.originalAttack.map prependAttack

private theorem loss_readback {suffix : Word} (originalRow : Occurrence seed community)
    (listed : originalRow ∈ originalLosses seed community (past ++ suffix)) :
    ∃ balance, ∃ row, (publishAfter (run seed community past) suffix).next.read row = .inr (originalRow, balance) := by
  rw [← the_live_ledger_contains_exactly_the_original_losses] at listed
  obtain ⟨⟨actual, balance⟩, present, same⟩ := List.mem_map.mp listed
  change actual = originalRow at same
  subst actual
  rw [publication_consumes_the_retained_visit]
  exact ⟨balance, (run seed community _).every_balance_is_a_row_of_the_current _ present⟩

theorem an_original_breakthrough_is_written_at_its_first_failed_prefix
    {suffix : Word} (attack : OriginalAttack seed community (past ++ suffix)) :
    ∃ balance, ∃ row, (publishAfter (run seed community past) suffix).next.read row = .inr (attack.val, balance) := by
  apply loss_readback
  rw [congrArg (originalLosses seed community) attack.property, losses_snoc]
  exact List.mem_append_right _ attack.is_in_the_original_openings

theorem the_first_breakthrough_files_its_original_victim_on_the_refused_successor
    (first : First) (attack : OriginalAttack seed community (past ++ first.originalScript)) :
    ∃ balance, ∃ row, (failedWrite first).next.read row = .inr (attack.val, balance) :=
  an_original_breakthrough_is_written_at_its_first_failed_prefix attack

def AccountedFailure (first : First) : Prop :=
    let whole := past ++ first.originalScript
    (∃ untouched, past ++ (play origin observe strategy (submitted rival) (first.round + 1)).script =
      whole ++ untouched) ∧
    Quantities.Recorded seed whole ∧ Evolving.Epoch.Current.ClosedAt (endAt seed whole) ∧
    (∀ old ∈ originalLosses seed community whole,
      ∃ balance, ∃ row, (failedWrite first).next.read row = .inr (old, balance)) ∧
    ∀ attack, firstRootAttack first = some attack →
      ∃ balance, ∃ row, (failedWrite first).next.read row = .inr (attack.val, balance)

theorem first_failure_consumes_the_original_prefix_and_keeps_the_complete_ledger (first : First) :
    AccountedFailure first := by
  obtain ⟨untouched, exactPrefix⟩ := first.original_prefix_and_next.1
  refine ⟨⟨untouched, ?_⟩, (failedWrite first).recorded, (failedWrite first).recorded.next, ?_, ?_⟩
  · rw [List.append_assoc, exactPrefix]
  · exact loss_readback
  · intro attack _
    exact the_first_breakthrough_files_its_original_victim_on_the_refused_successor first attack

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace
