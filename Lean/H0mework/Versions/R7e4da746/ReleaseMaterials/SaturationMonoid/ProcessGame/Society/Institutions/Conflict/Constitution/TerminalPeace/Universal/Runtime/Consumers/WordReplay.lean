import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Projection
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Unbounded

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Reparation.Actual (StateAt)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

theorem Attempt.first_paid_word_controls_the_actual_effect
    {input : ProgrammeSource.Input Party Good Port Technology Instrument}
    {origin : RawCurrent Party Good Technology Instrument} {roster : List Party}
    (attempt : Attempt input origin roster) (word : RawEvent Party Good Port Technology Instrument)
    (rest : List (RawEvent Party Good Port Technology Instrument))
    (offers : attempt.offers = word :: rest) (paid : Supply.Period input origin attempt.before.raw roster word) :
    attempt.Succeeds ∧
      attempt.after.raw = input.law.next attempt.before.raw word ∧
      attempt.items = input.law.rawItems attempt.before.raw word := by
  obtain ⟨approval, checked⟩ := (Supply.inspect_passes_iff _ _ _ _ _).mpr paid
  have selected : attempt.Succeeds := by
    rcases attempt.pays_or_refuses with selected | denied
    · exact selected
    · exact ((attempt.fails_iff.mp denied) word (offers.symm ▸ List.mem_cons_self) paid).elim
  have physical := paid.native_write attempt.before
  refine ⟨selected, ?_, ?_⟩
  · cases attempt with
    | mk before menu =>
      change menu = word :: rest at offers
      subst menu
      simp only [Attempt.after, Attempt.selected, Supply.select, checked]
      exact congrArg (fun next : Native Party Good Port Technology Instrument => next.raw) physical.2.2
  · cases attempt with
    | mk before menu =>
      change menu = word :: rest at offers
      subst menu
      simp only [Attempt.items, Attempt.selected, Supply.select, checked]
      exact congrArg ExecutionResult.items physical.2.1

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)
  (wordAt : Nat → RawEvent Party Good Port Technology Instrument)

def wordReplay (initial : RawCurrent Party Good Technology Instrument) : Nat → RawCurrent Party Good Technology Instrument
  | 0 => initial
  | n + 1 => input.law.next (wordReplay initial n) (wordAt n)

def replayMenus : Menus Party Good Port Technology Instrument :=
  fun n current => wordAt n :: roster.flatMap (fun person => (Supply.search input origin current [person]).chosen)

variable {Community : Type} [DecidableEq Port] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (prior : StateAt seed community cut)

theorem replay_of_each_checked_word_is_the_same_actual_material_current
    (paid : ∀ n, Supply.Period input origin (wordReplay input wordAt cut.raw n) roster (wordAt n))
    (n : Nat) :
    (eventAt prior input origin roster (replayMenus input origin roster wordAt) n).before.raw =
      wordReplay input wordAt cut.raw n := by
  induction n with
  | zero => rfl
  | succ n previous =>
    let current := eventAt prior input origin roster (replayMenus input origin roster wordAt) n
    have offered := the_original_root_records_each_new_menu prior input origin roster
      (replayMenus input origin roster wordAt) n
    have same : current.before.raw = wordReplay input wordAt cut.raw n := previous
    have due : Supply.Period input origin current.before.raw roster (wordAt n) := same.symm ▸ paid n
    change current.after.raw = input.law.next (wordReplay input wordAt cut.raw n) (wordAt n)
    exact (current.first_paid_word_controls_the_actual_effect (wordAt n) _ offered due).2.1.trans
      (congrArg (fun raw => input.law.next raw (wordAt n)) same)

theorem a_cofinal_paid_word_replay_produces_the_original_live_runtime
    (paid : ∀ n, Supply.Period input origin (wordReplay input wordAt cut.raw n) roster (wordAt n))
    (exits : ∀ n person, person ∈ roster →
      ∃ word, Supply.Registered input (wordReplay input wordAt cut.raw n) word ∧
        Supply.Period input origin (wordReplay input wordAt cut.raw n) [person] word)
    (time : ∀ start bound, ∃ n ≥ start, bound < (wordReplay input wordAt cut.raw n).clock) :
    ∃ ready clock, classify prior input origin roster (replayMenus input origin roster wordAt) = .live ready clock := by
  let menu := replayMenus input origin roster wordAt
  refine (a_living_terminal_is_generated_exactly_on_a_paid_cofinal_source prior input origin roster menu).mpr ⟨?_, ?_⟩
  · intro n
    let current := eventAt prior input origin roster menu n
    have same : current.before.raw = wordReplay input wordAt cut.raw n :=
      replay_of_each_checked_word_is_the_same_actual_material_current input origin roster wordAt prior paid n
    have offered := the_original_root_records_each_new_menu prior input origin roster menu n
    have due : Supply.Period input origin current.before.raw roster (wordAt n) := same.symm ▸ paid n
    refine ⟨(current.first_paid_word_controls_the_actual_effect (wordAt n) _ offered due).1, ?_⟩
    intro person listed
    rcases (current.personal person).pays_or_refuses with success | failed
    · exact success
    · have personal : ∃ word, Supply.Registered input current.before.raw word ∧
          Supply.Period input origin current.before.raw [person] word := same.symm ▸ exits n person listed
      obtain ⟨word, registered, witness⟩ := personal
      obtain ⟨chosen, member, valid⟩ := Supply.Search.a_registered_paid_word_forces_a_chosen_word
        (Supply.search input origin current.before.raw [person]) word registered witness
      have inMenu : chosen ∈ (current.personal person).offers := by
        change chosen ∈ current.offers
        rw [offered]
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨person, listed, member⟩)
      exact (((current.personal person).fails_iff.mp failed) chosen inMenu valid).elim
  · intro start bound
    obtain ⟨n, after, passed⟩ := time start bound
    refine ⟨n, after, ?_⟩
    unfold clockAt
    rw [replay_of_each_checked_word_is_the_same_actual_material_current _ _ _ _ _ paid]
    exact passed

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime
