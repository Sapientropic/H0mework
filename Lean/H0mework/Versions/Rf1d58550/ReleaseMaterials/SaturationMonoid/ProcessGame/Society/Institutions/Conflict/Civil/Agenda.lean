import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Menus

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

def noAttack (source : C) (front : Word) (war : List Word) : Prop :=
  ∀ word ∈ war, ¬ Root.Paid source (front ++ word)

abbrev Refused (source : C) (word : Word) :=
  {failure : Root.Failure source word // Root.inspect source word = .rejected failure}

inductive Agenda (source : C) (front : Word) (war : List Word)
  | blocked (original : ∀ word ∈ war, Refused source (front ++ word))
  | bypass (word : Word) (original : word ∈ war) (actual : Root.Paid source (front ++ word))

/-- Test every proposed continuation after the very same intervention.
Each failure retains the original request and its own material or authority cut. -/
def inspectAgenda (source : C) (front : Word) : (war : List Word) → Agenda source front war
  | [] => .blocked (fun _ inside => (List.not_mem_nil inside).elim)
  | first :: tail =>
      match found : Root.inspect source (front ++ first) with
      | .paid actual => .bypass first List.mem_cons_self actual
      | .rejected issue =>
          match inspectAgenda source front tail with
          | .bypass word original actual => .bypass word (List.mem_cons_of_mem _ original) actual
          | .blocked other => .blocked (by
              intro word listed
              classical
              by_cases same : word = first
              · subst word
                exact ⟨issue, found⟩
              · exact other word ((List.mem_cons.mp listed).resolve_left same))

def Agenda.stops {source : C} {front : Word} {war : List Word} : Agenda source front war → Bool
  | .blocked _ => true
  | .bypass .. => false

theorem refused_word_is_not_paid {source : C} {word : Word} (failure : Refused source word) :
    ¬ Root.Paid source word := by
  intro paid
  have admitted := (Root.inspect_accepts_iff source word).mpr paid
  rw [failure.property] at admitted
  cases admitted

theorem the_intervention_stops_exactly_when_no_paid_attack_bypasses
    (source : C) (front : Word) (war : List Word) :
    (inspectAgenda source front war).stops = true ↔ noAttack source front war := by
  cases inspectAgenda source front war with
  | blocked denied =>
      exact ⟨fun _ word listed => refused_word_is_not_paid (denied word listed), fun _ => rfl⟩
  | bypass word listed paid =>
      constructor
      · intro impossible
        cases impossible
      · exact fun stopped => (stopped word listed paid).elim

theorem covering_the_original_attack_class_prevents_every_executable_bypass
    (source : C) (front : Word) (war : List Word) (attack : Word → Prop)
    (complete : ∀ word, attack word → Root.Paid source (front ++ word) → word ∈ war)
    (stopped : noAttack source front war) :
    ∀ word, attack word → ¬ Root.Paid source (front ++ word) :=
  fun word original paid => stopped word (complete word original paid) paid

def afterPressure (source : C) (read : C → ℚ) (front : Word) (war peace : List Word) : Option ℚ :=
  Root.pressure source read (war.map (front ++ ·)) (peace.map (front ++ ·))

theorem a_hard_stop_leaves_no_comparable_attack
    (source : C) (read : C → ℚ) (front : Word) (war peace : List Word)
    (stopped : noAttack source front war) : afterPressure source read front war peace = none := by
  apply (Root.pressure_is_absent_iff_a_menu_has_no_paid_word _ _ _ _).mpr
  left
  intro word listed
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp listed
  exact stopped original present

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil
