import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Replay

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)

def original (words : List (RawEvent Party Good Port Technology Instrument)) :=
  Open.original (seed.withContinuation words)

def replacement (words : List (RawEvent Party Good Port Technology Instrument)) :=
  Open.replacement (seed.withContinuation words) feasible


theorem same_selection (words : List (RawEvent Party Good Port Technology Instrument)) :
    selection (seed.withContinuation words) feasible = selection seed feasible := by
  unfold selection Machine.withContinuation
  dsimp only
  split
  next choice result =>
    have same : compile seed.code seed.reference seed.reference_generated = .selected choice := result
    simp only [same]
  next rejected _ =>
    exact False.elim (feasible_original_cannot_be_blocked seed.code seed.reference seed.reference_generated feasible rejected)

theorem original_response_current (words : List (RawEvent Party Good Port Technology Instrument)) :
    (original seed words).currentAt (seed.history.length + 2) =
      terminal seed.code seed.reference seed.history seed.opponent :=
  ((original seed words).actual_reaction_word_and_next seed.reference rfl).2.2.2

theorem replacement_response_current (words : List (RawEvent Party Good Port Technology Instrument)) :
    (replacement seed feasible words).currentAt (seed.history.length + 2) =
      terminal seed.code (selection seed feasible).policy.policy seed.history seed.opponent :=
by
  have actual := ((replacement seed feasible words).actual_reaction_word_and_next _ rfl).2.2.2
  change (replacement seed feasible words).currentAt (seed.history.length + 2) =
    terminal seed.code (selection (seed.withContinuation words) feasible).policy.policy seed.history seed.opponent at actual
  rw [same_selection seed feasible words] at actual
  exact actual

omit [DecidableEq Port] [DecidableEq Technology] in
theorem legal_prefix (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (words : List (RawEvent Party Good Port Technology Instrument))
    (accepted : LegalHistory law current words) (count : Nat) : LegalHistory law current (words.take count) := by
  induction words generalizing current count with
  | nil => simpa only [List.take_nil] using accepted
  | cons word tail ih =>
      cases count with
      | zero => trivial
      | succ count => exact ⟨accepted.1, ih (law.next current word) accepted.2 count⟩

theorem every_submitted_continuation_is_actually_emitted
    (words : List (RawEvent Party Good Port Technology Instrument)) (index : Nat) (inside : index < words.length) :
    ((original seed words).actualExecution (seed.history.length + 1 + index)).submitted = words[index] ∧
      ((replacement seed feasible words).actualExecution (seed.history.length + 1 + index)).submitted = words[index] :=
  ⟨(original seed words).continuation_word_is_actual index inside,
    (replacement seed feasible words).continuation_word_is_actual index inside⟩

theorem every_actual_cut_keeps_the_full_original_carrier (stable : Stable seed.code.law)
    (words : List (RawEvent Party Good Port Technology Instrument))
    (accepted : LegalHistory seed.code.law (terminal seed.code seed.reference seed.history seed.opponent) words)
    (count : Nat) (bounded : count ≤ words.length) :
    (replacement seed feasible words).currentAt (seed.history.length + 2 + count) =
      ((original seed words).currentAt (seed.history.length + 2 + count)).addReserve
        (reserve seed.code (selection seed feasible).policy.policy seed.reference seed.history seed.opponent) := by
  have newPrefix := (replacement seed feasible words).continuation_prefix_is_actual count bounded
  have oldPrefix := (original seed words).continuation_prefix_is_actual count bounded
  change (replacement seed feasible words).currentAt (seed.history.length + 2 + count) =
    (words.take count).foldl seed.code.law.next ((replacement seed feasible words).currentAt (seed.history.length + 2)) at newPrefix
  change (original seed words).currentAt (seed.history.length + 2 + count) =
    (words.take count).foldl seed.code.law.next ((original seed words).currentAt (seed.history.length + 2)) at oldPrefix
  rw [newPrefix, oldPrefix, replacement_response_current seed feasible words, original_response_current seed words]
  obtain ⟨nonnegative, extension⟩ := generated_full_carrier_extension seed.code _ _
    (selection seed feasible).policy.generated seed.reference_generated (selection seed feasible).policy.no_regression
    seed.opponent seed.history seed.original
  rw [extension]
  exact (every_old_legal_history_remains_open seed.code.law stable _ _ nonnegative (words.take count)
    (legal_prefix seed.code.law _ words accepted count)).2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Replay
