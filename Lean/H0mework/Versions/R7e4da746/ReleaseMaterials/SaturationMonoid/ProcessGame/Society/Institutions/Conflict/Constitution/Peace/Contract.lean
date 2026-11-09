import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Shortage
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Cofinal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Quantities.Execution (endAt endAt_append)
open Reparation.Actual (publishAfter run originalLosses publication_keeps_every_previous_loss)

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community] {Observation : Type u}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "Strategy" => History Observation → Word
local notation "P" => Position Party Good Port Technology Instrument Observation

variable (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)
  (past : Script Party Good Port Technology Instrument) (command : List Party)
  (observe : Root.Cut Party Good Port Technology Instrument → Observation)

local notation "origin" => endAt seed past

def ProtectsAtRoot (strategy : Strategy) : Prop :=
  ∀ rival round, ProtectedRound (seed := seed) (community := community)
    (past := past) (observe := observe) (strategy := strategy) command rival round

theorem protects_at_root_iff (strategy : Strategy) :
    ProtectsAtRoot seed community past command observe strategy ↔ ProtectsWithExit origin command community observe strategy :=
  ⟨fun wins rival round => (wins rival round).1, every_protected_round_consumes_its_actual_whole_ledger⟩

theorem sustainable_civilian_peace_iff_one_move_protects_each_reachable_observation_fibre :
    (∃ strategy, ProtectsAtRoot seed community past command observe strategy) ↔
    ∃ family : P → Prop, family (Position.start origin observe) ∧
      ClosedFor observe (RequiresExit origin command community) family := by
  simp only [protects_at_root_iff]
  exact wins_with_exit_iff_one_response_closes_each_reachable_observation_fibre origin command community observe

def RootCounterexample (strategy : Strategy) :=
  Σ rival : List Word,
    { first : FirstFailureWithExit origin command community observe strategy rival //
      AccountedFailure (seed := seed) (past := past) first }

def RootCounterexample.namedShortage {strategy : Strategy}
    (counter : RootCounterexample seed community past command observe strategy) :=
  namedShortageAtFailure (seed := seed) (past := past) counter.2.val

/-- Evaluate the supplied finite tape using the native compiler. A failing
input carries a generated successor at its first original failed cut. -/
def inspectOriginalPrefix (strategy : Strategy) (rival : List Word) :
    { first : FirstFailureWithExit origin command community observe strategy rival //
      AccountedFailure (seed := seed) (past := past) first } ⊕
      PLift (∀ round < rival.length, ProtectedRound (seed := seed) (community := community)
        (past := past) (observe := observe) (strategy := strategy) command (submitted rival) round) :=
  match inspectThroughWithExit origin command community observe strategy rival rival.length le_rfl with
  | .inl first => .inl ⟨first.val, first_failure_consumes_the_original_prefix_and_keeps_the_complete_ledger first.val⟩
  | .inr passed => .inr ⟨fun round within =>
      round_on_the_original_ledger (submitted rival) round (passed.down round within)⟩

theorem a_policy_fails_iff_it_has_an_original_accounted_first_counterexample (strategy : Strategy) :
    ¬ ProtectsAtRoot seed community past command observe strategy ↔
      Nonempty (RootCounterexample seed community past command observe strategy) := by
  rw [protects_at_root_iff]
  constructor
  · intro denied
    obtain ⟨⟨rival, first⟩⟩ := a_failed_contract_has_an_original_first_counterexample
      (RequiresExit origin command community) (FailureWithExit origin command community)
      (inspectWithExit origin command community) denied
    exact ⟨⟨rival, first, first_failure_consumes_the_original_prefix_and_keeps_the_complete_ledger _⟩⟩
  · rintro ⟨⟨rival, first, _⟩⟩ safe
    exact first.failure.refutes (safe (submitted rival) first.round)

theorem no_shared_policy_iff_each_policy_has_a_rooted_counterexample :
    (¬ ∃ strategy, ProtectsAtRoot seed community past command observe strategy) ↔
      ∀ strategy, Nonempty (RootCounterexample seed community past command observe strategy) := by
  simp only [not_exists, a_policy_fails_iff_it_has_an_original_accounted_first_counterexample]

theorem every_actual_response_is_covered_even_when_it_reads_the_civilian_action
    (strategy : Strategy) (safe : ProtectsAtRoot seed community past command observe strategy)
    (choose : Nat → C → Word → Word) (round : Nat) :
    let actual := adaptivePlay origin observe strategy choose round
    RequiresExit origin command community actual.position (strategy actual.position.seen)
      (emitted origin observe strategy choose round) ∧
    Quantities.Recorded seed (past ++ (adaptivePlay origin observe strategy choose (round + 1)).script) := by
  rw [adaptive_play_is_the_actual_play_of_its_emitted_inputs, adaptive_play_is_the_actual_play_of_its_emitted_inputs]
  exact ⟨(safe _ round).1, by simpa only [play, List.append_assoc] using (safe _ round).2.1⟩

def RootedClockBound (strategy : Strategy) (rival : Nat → Word) (bound : ℚ) : Prop :=
  ∀ round,
    let reached := play origin observe strategy rival round
    let written := publishAfter (run seed community past) reached.script
    reached.position.window.current.raw.clock < bound ∧
    reached.position.window.current = endAt seed (past ++ reached.script) ∧
    Quantities.Recorded seed (past ++ reached.script) ∧
    ∀ old ∈ originalLosses seed community past, ∃ balance, ∃ row, written.next.read row = .inr (old, balance)

theorem a_cofinal_policy_fails_iff_first_counterexample_or_an_original_clock_bound (strategy : Strategy) :
    ¬ (ProtectsAtRoot seed community past command observe strategy ∧
        ∀ rival, Quantities.Bounds.Cofinal.ClockCofinal origin (stages origin observe strategy rival)) ↔
    Nonempty (RootCounterexample seed community past command observe strategy) ∨
      ∃ (rival : Nat → Word) (bound : ℚ), RootedClockBound seed community past observe strategy rival bound := by
  rw [protects_at_root_iff]
  change ¬ ProtectsCofinally origin command community observe strategy ↔ _
  rw [no_cofinal_protection_iff_first_failure_or_a_real_clock_bound]
  apply or_congr
  · constructor
    · rintro ⟨⟨rival, first⟩⟩
      exact ⟨⟨rival, first, first_failure_consumes_the_original_prefix_and_keeps_the_complete_ledger _⟩⟩
    · rintro ⟨⟨rival, first, _⟩⟩
      exact ⟨⟨rival, first⟩⟩
  · constructor
    · rintro ⟨rival, bound, bounded⟩
      refine ⟨rival, bound, fun round => ⟨bounded round, ?_, Quantities.record seed _, ?_⟩⟩
      · rw [play_is_the_original_execution, endAt_append]
      · exact publication_keeps_every_previous_loss seed community _ _
    · rintro ⟨rival, bound, bounded⟩
      exact ⟨rival, bound, fun round => (bounded round).1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace
