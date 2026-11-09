import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Select
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Migration (sourceWords sourceAlphabet sourceWords_complete)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (roster : List Party)

def Registered (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ request ∈ word, request ∈ sourceAlphabet input current

inductive Search where
  | paid (word : RawEvent Party Good Port Technology Instrument)
      (registered : Registered input current word)
      (witness : Period input origin current roster word)
      (shortest : ∀ other, Registered input current other →
        Period input origin current roster other → word.length ≤ other.length)
  | blocked (failures : ∀ width, ∀ position : Fin (sourceWords input current width).length,
      Issue input origin current roster (sourceWords input current width)[position])

private def PaysWithin (width : Nat) : Prop :=
  ∃ word ∈ sourceWords input current width, Period input origin current roster word

/-- Search across all finite words of the current registered alphabet.
A success pays at the least actual instruction count. An obstruction
retains the first concrete issue at every finite horizon. -/
def search : Search input origin current roster := by
  classical
  by_cases existsWidth : ∃ width, PaysWithin input origin current roster width
  · let width := Nat.find existsWidth
    have available : PaysWithin input origin current roster width := Nat.find_spec existsWidth
    cases selected : selectRegistered input origin current roster width with
    | blocked failures =>
      have impossible : False := by
        obtain ⟨offered, listed, period⟩ := available
        obtain ⟨index, inside, equal⟩ := List.getElem_of_mem listed
        apply (failures ⟨index, inside⟩).refutes _ _ _ _ _
        change Period input origin current roster (sourceWords input current width)[index]
        rwa [equal]
      exact impossible.elim
    | paid position paid earlier =>
      let word := (sourceWords input current width)[position]
      have bounds := (sourceWords_complete input current width word).mp (List.getElem_mem position.isLt)
      refine .paid word bounds.2 paid (fun other registered valid => bounds.1.trans ?_)
      exact Nat.find_min' existsWidth ⟨other,
        (sourceWords_complete input current other.length other).mpr ⟨le_rfl, registered⟩, valid⟩
  · refine .blocked fun width => ?_
    cases selectRegistered input origin current roster width with
    | blocked all => exact all
    | paid position paid earlier =>
      exact (existsWidth ⟨width, _, List.getElem_mem position.isLt, paid⟩).elim

namespace Search

variable {input origin current roster}

def chosen (result : Search input origin current roster) :
    List (RawEvent Party Good Port Technology Instrument) :=
  match result with
  | .paid word _ _ _ => [word]
  | .blocked _ => []

theorem every_chosen_word_is_registered (result : Search input origin current roster)
    (word : RawEvent Party Good Port Technology Instrument) (listed : word ∈ result.chosen) :
    Registered input current word := by
  cases result with
  | paid original registered paid _ =>
    rcases List.mem_singleton.mp listed with rfl
    exact registered
  | blocked _ => exact (List.not_mem_nil listed).elim

theorem a_registered_paid_word_forces_a_chosen_word (result : Search input origin current roster)
    (word : RawEvent Party Good Port Technology Instrument)
    (registered : Registered input current word) (paid : Period input origin current roster word) :
    ∃ selected ∈ result.chosen, Period input origin current roster selected := by
  cases result with
  | paid original _ witness _ => exact ⟨original, List.mem_singleton_self _, witness⟩
  | blocked failures =>
    have listed := (sourceWords_complete input current word.length word).mpr ⟨le_rfl, registered⟩
    obtain ⟨position, inside, same⟩ := List.getElem_of_mem listed
    have impossible := (failures word.length ⟨position, inside⟩).refutes _ _ _ _ _
    exfalso
    apply impossible
    change Period input origin current roster (sourceWords input current word.length)[position]
    rwa [same]

end Search

/-- The due word is listed first. Every original person is also offered
the shortest available personal word selected at this very inventory. -/
def generatedMenu : List (RawEvent Party Good Port Technology Instrument) :=
  (search input origin current roster).chosen ++
    roster.flatMap (fun person => (search input origin current [person]).chosen)

theorem generated_menu_contains_an_actual_period_iff
    (people : List Party) (included : people = roster ∨ ∃ person ∈ roster, people = [person]) :
    (∃ word ∈ generatedMenu input origin current roster, Period input origin current people word) ↔
      ∃ word, Registered input current word ∧ Period input origin current people word := by
  constructor
  · rintro ⟨word, listed, paid⟩
    refine ⟨word, ?_, paid⟩
    unfold generatedMenu at listed
    rcases List.mem_append.mp listed with due | exits
    · exact Search.every_chosen_word_is_registered _ word due
    · obtain ⟨person, _, personal⟩ := List.mem_flatMap.mp exits
      exact Search.every_chosen_word_is_registered (search input origin current [person]) word personal
  · rintro ⟨word, registered, paid⟩
    rcases included with rfl | ⟨person, listed, rfl⟩
    · obtain ⟨selected, member, witness⟩ :=
        Search.a_registered_paid_word_forces_a_chosen_word _ word registered paid
      exact ⟨selected, List.mem_append_left _ member, witness⟩
    · obtain ⟨selected, member, witness⟩ :=
        Search.a_registered_paid_word_forces_a_chosen_word _ word registered paid
      exact ⟨selected, List.mem_append_right _ (List.mem_flatMap.mpr ⟨person, listed, member⟩), witness⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply
