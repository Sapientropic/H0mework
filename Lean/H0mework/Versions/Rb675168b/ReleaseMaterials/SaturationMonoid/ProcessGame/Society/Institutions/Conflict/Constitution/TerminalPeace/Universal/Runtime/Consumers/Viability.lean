import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Consumers.WordReplay
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Region

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Reparation.Actual (StateAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (prior : StateAt seed community cut)
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)

def RegisteredRun (menus : Menus Party Good Port Technology Instrument) : Prop :=
  ∀ n word, word ∈ (eventAt prior input origin roster menus n).offers →
    Supply.Registered input (eventAt prior input origin roster menus n).before.raw word

def trajectoryMenus (route : Viability.Trajectory input origin roster cut.raw) :
    Menus Party Good Port Technology Instrument :=
  replayMenus input origin roster (fun n => (route.move n).word)

private theorem exact_word_replay (route : Viability.Trajectory input origin roster cut.raw) (n : Nat) :
    wordReplay input (fun i => (route.move i).word) cut.raw n = route.state n := by
  induction n with
  | zero => exact route.initial.symm
  | succ n same =>
    rw [wordReplay, same, route.next_eq]
    rfl

theorem the_live_trajectory_executes_on_the_original_root
    (route : Viability.Trajectory input origin roster cut.raw) :
    let menus := trajectoryMenus input origin roster route
    RegisteredRun prior input origin roster menus ∧
      (∃ ready time, classify prior input origin roster menus = .live ready time) := by
  let wordAt := fun n => (route.move n).word
  have paid (n : Nat) : Supply.Period input origin (wordReplay input wordAt cut.raw n) roster (wordAt n) := by
    rw [exact_word_replay input origin roster route n]
    exact (route.move n).paid
  have exactRaw (n : Nat) :
      (eventAt prior input origin roster (trajectoryMenus input origin roster route) n).before.raw = route.state n :=
    (replay_of_each_checked_word_is_the_same_actual_material_current input origin roster wordAt prior paid n).trans
      (exact_word_replay input origin roster route n)
  refine ⟨?_, a_cofinal_paid_word_replay_produces_the_original_live_runtime input origin roster wordAt prior paid ?_ ?_⟩
  · intro n word inMenu
    rw [the_original_root_records_each_new_menu] at inMenu
    change word ∈ (route.move n).word :: _ at inMenu
    rcases List.mem_cons.mp inMenu with first | personal
    · subst word
      rw [exactRaw]
      exact (route.move n).registered
    · obtain ⟨person, _, selected⟩ := List.mem_flatMap.mp personal
      exact Supply.Search.every_chosen_word_is_registered
        (Supply.search input origin (eventAt prior input origin roster (trajectoryMenus input origin roster route) n).before.raw
          [person]) word selected
  · intro n person listed
    rw [exact_word_replay input origin roster route n]
    exact (route.move n).personal person listed
  · intro start bound
    obtain ⟨n, later, past⟩ := route.cofinal start bound
    refine ⟨n, later, ?_⟩
    rw [exact_word_replay input origin roster route n]
    exact past

variable (menus : Menus Party Good Port Technology Instrument)
  (registered : RegisteredRun prior input origin roster menus)
  (ready : ∀ n, ReadyAt prior input origin roster menus n)

private def realizedPosition (n : Nat) : Fin (eventAt prior input origin roster menus n).offers.length :=
  Classical.choose ((eventAt prior input origin roster menus n).accepted_effect (ready n).1)

private def realizedMove (n : Nat) :
    Viability.Move input origin roster (eventAt prior input origin roster menus n).before.raw where
  word := (eventAt prior input origin roster menus n).offers[realizedPosition prior input origin roster menus ready n]
  registered := registered n _ (List.getElem_mem (realizedPosition prior input origin roster menus ready n).isLt)
  paid := (Classical.choose_spec ((eventAt prior input origin roster menus n).accepted_effect (ready n).1)).1
  personal := by
    intro person listed
    obtain ⟨position, paid, _, _⟩ := (ready n).2 person listed
    exact ⟨(eventAt prior input origin roster menus n).offers[position],
      registered n _ (List.getElem_mem position.isLt), paid⟩

def trajectoryOfActualRoot (time : ClockCofinal prior input origin roster menus) :
    Viability.Trajectory input origin roster cut.raw where
  state := fun n => (eventAt prior input origin roster menus n).before.raw
  initial := rfl
  move := realizedMove prior input origin roster menus registered ready
  next_eq := by
    intro n
    rw [the_next_attempt_reads_the_same_generated_physical_current]
    exact congrArg (fun current : Native Party Good Port Technology Instrument => current.raw)
      (Classical.choose_spec ((eventAt prior input origin roster menus n).accepted_effect (ready n).1)).2.2
  cofinal := time

include registered ready in
theorem every_actual_registered_live_root_starts_in_the_viable_region
    (time : ClockCofinal prior input origin roster menus) :
    Viability.Live input origin roster cut.raw :=
  (trajectoryOfActualRoot prior input origin roster menus registered ready time).initial_is_live

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime
