import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Round
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Reparation.Actual (SourceAuthority)
open Quantities.Execution (inventory_append)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "W" => Window Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument

inductive WaitingDomain
  | lawful
  | physicallyPossible

def WaitingDomain.permits (mode : WaitingDomain) (cut : C) (word : Word) : Prop :=
  match mode with
  | .lawful => SourceAuthority cut word
  | .physicallyPossible => True

theorem WaitingDomain.permits_prefix {mode : WaitingDomain} {cut : C} {first tail : Word}
    (permitted : mode.permits cut (first ++ tail)) : mode.permits cut first := by
  cases mode
  · intro item present
    apply permitted item
    rw [inventory_append]
    exact List.mem_append_left _ present
  · trivial

variable (origin : Root.Cut Party Good Port Technology Instrument) (command : List Party) (community : Party → Community)
  (window : Window Party Good Port Technology Instrument) (mode : WaitingDomain)

/-- The original input at which waiting loses a condition. The prior
script remains in the same native material and authority domain. -/
structure WaitBreach where
  before : Word
  input : Input
  permitted : mode.permits window.current (before ++ [input])
  issue : StepFailure origin command community false (window.run before) input

def SafeThrough (limit : Nat) : Prop :=
  ∀ word : Word, word.length ≤ limit → mode.permits window.current word →
    Checked origin command community false window word

private theorem first_issue_is_a_native_breach {word : Word}
    (permitted : mode.permits window.current word)
    (first : FirstFailure origin command community false window word) :
    ∃ found : WaitBreach origin command community window mode,
      found.before.length < word.length := by
  have split : word = (first.before ++ [first.input]) ++ first.after := by
    simpa only [List.append_assoc, List.singleton_append] using first.split
  have permittedFirst : mode.permits window.current (first.before ++ [first.input]) :=
    WaitingDomain.permits_prefix (split ▸ permitted)
  refine ⟨⟨first.before, first.input, permittedFirst, first.issue⟩, ?_⟩
  have length := congrArg List.length first.split
  simp only [List.length_append, List.length_cons] at length
  change first.before.length < word.length
  omega

theorem safe_through_iff_every_original_breakthrough_is_at_or_after_it (limit : Nat) :
    SafeThrough origin command community window mode limit ↔
    ∀ found : WaitBreach origin command community window mode, limit ≤ found.before.length := by
  constructor
  · intro safe found
    by_contra early
    have permitted := safe (found.before ++ [found.input]) (by simp only [List.length_append, List.length_singleton]; omega)
      found.permitted
    exact found.issue.refutes ((checked_append origin command community false window _ _).mp permitted).2.1
  · intro beyond word within permitted
    cases inspectSegment origin command community false window word with
    | inl first =>
      obtain ⟨found, earlier⟩ := first_issue_is_a_native_breach origin command community window mode permitted first
      exact (not_lt_of_ge (beyond found) (earlier.trans_le within)).elim
    | inr safe => exact safe.down

inductive WaitingFrontier
  | unbounded (safe : ∀ limit, SafeThrough origin command community window mode limit)
  | finite (first : WaitBreach origin command community window mode)
      (tight : ∀ limit, SafeThrough origin command community window mode limit ↔ limit ≤ first.before.length)

def waitingFrontier : WaitingFrontier origin command community window mode := by
  classical
  let Hit (ordinal : Nat) := ∃ found : WaitBreach origin command community window mode,
    found.before.length = ordinal
  by_cases existsHit : ∃ ordinal, Hit ordinal
  · let first := Classical.choose (Nat.find_spec existsHit)
    have exactFirst : first.before.length = Nat.find existsHit := Classical.choose_spec (Nat.find_spec existsHit)
    refine .finite first (fun limit => ?_)
    rw [safe_through_iff_every_original_breakthrough_is_at_or_after_it]
    exact ⟨fun all => all first, fun before found =>
      before.trans (exactFirst.trans_le (Nat.find_min' existsHit (show Hit found.before.length from ⟨found, rfl⟩)))⟩
  · refine .unbounded (fun limit => (safe_through_iff_every_original_breakthrough_is_at_or_after_it _ _ _ _ _ _).mpr ?_)
    intro found
    exact (existsHit ⟨found.before.length, found, rfl⟩).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
