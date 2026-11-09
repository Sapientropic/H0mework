import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Adaptive
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Reparation.Actual (originalLosses run publishAfter publication_keeps_every_previous_loss)
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
  {past : Script Party Good Port Technology Instrument} {command : List Party} {observe : Root.Cut Party Good Port Technology Instrument → Observation}
  {strategy : Civil.Persistence.History Observation → Civil.Persistence.Script Party Good Port Technology Instrument}

local notation "origin" => endAt seed past
local notation "playAt" => play origin observe strategy

/-- The live whole ledger is taken from the original seed through the
already performed prefix. The protection game observes that exact cut. -/
def roundWrite (rival : Nat → Word) (round : Nat) :=
  let prior := playAt rival round
  publishAfter (run seed community (past ++ prior.script)) (strategy prior.position.seen ++ rival round)

def ProtectedRound (command : List Party) (rival : Nat → Word) (round : Nat) : Prop :=
    let prior := playAt rival round
    let word := (past ++ prior.script) ++ (strategy prior.position.seen ++ rival round)
    let written := roundWrite (seed := seed) (community := community) (past := past)
      (observe := observe) (strategy := strategy) rival round
    RequiresExit origin command community prior.position (strategy prior.position.seen) (rival round) ∧
    Quantities.Recorded seed word ∧
    (playAt rival (round + 1)).position.window.current = endAt seed word ∧
    ∀ old ∈ originalLosses seed community (past ++ prior.script),
      ∃ balance, ∃ row, written.next.read row = .inr (old, balance)

theorem round_on_the_original_ledger (rival : Nat → Word) (round : Nat)
    (checked : let prior := playAt rival round
      RequiresExit origin command community prior.position (strategy prior.position.seen) (rival round)) :
    ProtectedRound (seed := seed) (community := community) (past := past) (observe := observe)
      (strategy := strategy) command rival round := by
  refine ⟨checked, (roundWrite (seed := seed) (community := community) (past := past)
    (observe := observe) (strategy := strategy) rival round).recorded, ?_, ?_⟩
  · rw [play_is_the_original_execution, endAt_append]
    simp only [play, endAt_append]
  · exact publication_keeps_every_previous_loss seed community _ _

theorem every_protected_round_consumes_its_actual_whole_ledger
    (wins : ProtectsWithExit origin command community observe strategy) (rival : Nat → Word) (round : Nat) :
    ProtectedRound (seed := seed) (community := community) (past := past) (observe := observe)
      (strategy := strategy) command rival round :=
  round_on_the_original_ledger rival round (wins rival round)

/-- The opponent may stop at any original input. The same policy supplies
an independent exit there and spends it from the retained original visit. -/
theorem every_rival_cut_has_a_rooted_independent_exit
    (wins : ProtectsWithExit origin command community observe strategy)
    (rival : Nat → Word) (round : Nat) (front pending : Word) (split : rival round = front ++ pending) :
    let prior := playAt rival round
    let own := strategy prior.position.seen
    let path := past ++ (prior.script ++ (own ++ front))
    let exit := strategy (prior.position.extend observe own front).seen
    let written := publishAfter (run seed community path) exit
    ExitAtCut origin command community (endAt seed path) exit ∧
    Quantities.Recorded seed (path ++ exit) ∧
    Evolving.Epoch.Current.ClosedAt (endAt seed (path ++ exit)) ∧
    ∀ old ∈ originalLosses seed community path, ∃ balance, ∃ row, written.next.read row = .inr (old, balance) := by
  have exit := every_rival_prefix_keeps_a_fresh_paid_exit_on_the_original_ledger wins rival round front pending split
  refine ⟨?_, (publishAfter (run seed community _) _).recorded, (Quantities.record seed _).next, ?_⟩
  · rw [endAt_append]
    exact exit.2.1
  · exact publication_keeps_every_previous_loss seed community _ _

/-- At an intermediate civilian cut the rest of the intervention has
already been checked. Completing it permits the next fresh independent
exit without waiting for a rival action. -/
theorem every_civilian_cut_has_a_rooted_independent_continuation
    (wins : ProtectsWithExit origin command community observe strategy)
    (rival : Nat → Word) (round : Nat) (front pending : Word)
    (split : strategy (playAt rival round).position.seen = front ++ pending) :
    let prior := playAt rival round
    let own := strategy prior.position.seen
    let path := past ++ (prior.script ++ front)
    let exit := strategy (prior.position.extend observe own []).seen
    let written := publishAfter (run seed community path) (pending ++ exit)
    Checked origin command community true (prior.position.window.run front) pending ∧
    ExitAtCut origin command community (endAt seed (path ++ pending)) exit ∧
    Quantities.Recorded seed (path ++ (pending ++ exit)) ∧
    Evolving.Epoch.Current.ClosedAt (endAt seed (path ++ (pending ++ exit))) ∧
    ∀ old ∈ originalLosses seed community path, ∃ balance, ∃ row, written.next.read row = .inr (old, balance) := by
  have suffix := the_rest_of_the_committed_intervention_is_an_original_checked_continuation wins rival round front pending split
  have exit := every_rival_cut_has_a_rooted_independent_exit wins rival round [] (rival round) rfl
  refine ⟨suffix.1, ?_, (publishAfter (run seed community _) _).recorded, (Quantities.record seed _).next, ?_⟩
  · simpa only [List.append_nil, split, List.append_assoc] using exit.1
  · exact publication_keeps_every_previous_loss seed community _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace
