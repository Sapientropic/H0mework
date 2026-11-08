import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Execution
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold.Selection
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice.Frontier

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

abbrev Admitted (source : C) := {word : Word // Paid source word}

def admit (source : C) (word : Word) : Option (Admitted source) :=
  match inspect source word with
  | .paid paid => some ⟨word, paid⟩
  | .rejected _ => none

def admitted (source : C) (proposals : List Word) : List (Admitted source) :=
  proposals.filterMap (admit source)

theorem admit_of_paid {source : C} {word : Word} (paid : Paid source word) :
    admit source word = some ⟨word, paid⟩ := by
  have passes := (inspect_accepts_iff source word).mpr paid
  unfold admit
  cases observed : inspect source word with
  | paid proof => exact congrArg some (Subtype.ext rfl)
  | rejected failed => simp [observed, Decision.accepted] at passes

theorem mem_admitted {source : C} {proposals : List Word} {row : Admitted source} :
    row ∈ admitted source proposals ↔ row.val ∈ proposals := by
  rw [admitted, List.mem_filterMap]
  constructor
  · rintro ⟨word, member, selected⟩
    unfold admit at selected
    split at selected
    · have same := congrArg Subtype.val (Option.some.inj selected)
      exact same ▸ member
    · contradiction
  · intro member
    exact ⟨row.val, member, admit_of_paid row.property⟩

def value (source : C) (read : C → ℚ) (row : Admitted source) : ℚ :=
  read (terminal source row.val)

/-- The same readout is used in both source menus; every row keeps its own
original execution and successor. -/
def pressure (source : C) (read : C → ℚ) (war peace : List Word) : Option ℚ :=
  Threshold.gap (value source read) (value source read) (admitted source war) (admitted source peace)

theorem pressure_of_two_paid_words {source : C} (read : C → ℚ) {war peace : Word}
    (warPaid : Paid source war) (peacePaid : Paid source peace) :
    pressure source read [war] [peace] =
      some (read (terminal source war) - read (terminal source peace)) := by
  simp only [pressure, admitted, List.filterMap_cons, admit_of_paid warPaid,
    admit_of_paid peacePaid, List.filterMap_nil]
  rfl

theorem pressure_is_the_gap_between_the_best_paid_alternatives
    (source : C) (read : C → ℚ) (war peace : List Word) (margin : ℚ)
    (computed : pressure source read war peace = some margin) :
    ∃ conflict ∈ war, ∃ settlement ∈ peace,
      Paid source conflict ∧ Paid source settlement ∧
      margin = read (terminal source conflict) - read (terminal source settlement) ∧
      (∀ word ∈ war, Paid source word → read (terminal source word) ≤ read (terminal source conflict)) ∧
      (∀ word ∈ peace, Paid source word → read (terminal source word) ≤ read (terminal source settlement)) := by
  obtain ⟨first, firstIn, second, secondIn, exactGap, warBest, peaceBest⟩ := Threshold.gap_exact computed
  exact ⟨first.val, mem_admitted.mp firstIn, second.val, mem_admitted.mp secondIn,
    first.property, second.property, exactGap,
    fun word member paid => warBest ⟨word, paid⟩ (mem_admitted.mpr member),
    fun word member paid => peaceBest ⟨word, paid⟩ (mem_admitted.mpr member)⟩

theorem pressure_is_absent_iff_a_menu_has_no_paid_word
    (source : C) (read : C → ℚ) (war peace : List Word) :
    pressure source read war peace = none ↔
      (∀ word ∈ war, ¬ Paid source word) ∨ (∀ word ∈ peace, ¬ Paid source word) := by
  have empty (words : List Word) :
      admitted source words = [] ↔ ∀ word ∈ words, ¬ Paid source word := by
    rw [List.eq_nil_iff_forall_not_mem]
    constructor
    · exact fun absent word member paid => absent ⟨word, paid⟩ (mem_admitted.mpr member)
    · exact fun absent entry member => absent entry.val (mem_admitted.mp member) entry.property
  rw [pressure, Threshold.gap_eq_none, empty war, empty peace]

/-- Open candidate families are read through the same original acceptance
predicate. Class membership is supplied by the source's proposal class. -/
def sourceMenu (source : C) (read : C → ℝ) (classifies : Set Word) : Choice.Menu Word where
  executable := {word | word ∈ classifies ∧ Paid source word}
  score := fun word => read (terminal source word)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
