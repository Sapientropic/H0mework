import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Production
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Consumers.Viability
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Strategy
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Productive.Prepend

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual (ReceiptAnswers Script)
open Runtime.Viability (Live Move Trajectory)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (registered : Script Party Good Port Technology Instrument → Prop)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "Offers" => ProductionMenu Party Good Port Technology Instrument

def ViableEntry (word : Word) (offers : Offers := ProductionMenu.empty) : Prop :=
  Occurrence.Unbounded.Allowed answers loss registered word ∧ ReadyEntry loss word ∧
    ∃ choice : ProductionChoice offers, ProductionApproved seed loss word choice ∧
      ∃ first : Move (productionInput seed loss word choice) (originalRaw loss) (productionRoster seed loss word choice)
          (endAt seed (Occurrence.history loss ++ word)).raw,
        ProductionStartsWith choice first.word ∧
          Live (productionInput seed loss word choice) (originalRaw loss) (productionRoster seed loss word choice) first.next

/-- The selected production proposal is realized by the same first paid
physical visit that installs the new material face on the original stack. -/
structure Realization (word : Word) (offers : Offers := ProductionMenu.empty) where
  allowed : Occurrence.Unbounded.Allowed answers loss registered word
  originalEntry : ReadyEntry loss word
  choice : ProductionChoice offers
  approved : ProductionApproved seed loss word choice
  trajectory : Trajectory (productionInput seed loss word choice) (originalRaw loss) (productionRoster seed loss word choice)
    (endAt seed (Occurrence.history loss ++ word)).raw
  pilot : ProductionStartsWith choice (trajectory.move 0).word

variable {loss answers registered} {word : Script Party Good Port Technology Instrument}
  {offers : ProductionMenu Party Good Port Technology Instrument}

namespace Realization

variable (run : Realization loss answers registered word offers)

abbrev programme := productionInput seed loss word run.choice

abbrev people := productionRoster seed loss word run.choice

def menus : Runtime.Menus Party Good Port Technology Instrument :=
  Runtime.trajectoryMenus run.programme (originalRaw loss) run.people run.trajectory

private theorem execution :
    Runtime.RegisteredRun (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus ∧
    (∃ ready clock, Runtime.classify (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus = .live ready clock) :=
  Runtime.the_live_trajectory_executes_on_the_original_root
    (Occurrence.reached answers loss word) run.programme (originalRaw loss) run.people run.trajectory

theorem registeredRun :
    Runtime.RegisteredRun (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus :=
  run.execution.1

private theorem completion :
    (∀ n, Runtime.ReadyAt (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus n) ∧
    Runtime.ClockCofinal (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus :=
  (Runtime.a_living_terminal_is_generated_exactly_on_a_paid_cofinal_source
    (Occurrence.reached answers loss word) run.programme (originalRaw loss)
    run.people run.menus).mp run.execution.2

theorem ready (n : Nat) :
    Runtime.ReadyAt (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus n :=
  run.completion.1 n

theorem clock :
    Runtime.ClockCofinal (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus :=
  run.completion.2

/-- The first paid visit executes the actual production word in its
original order, including the material debits at its own positions. -/
theorem pilot_writes_the_actual_material_items :
    let before := (endAt seed (Occurrence.history loss ++ word)).raw
    let first := Runtime.eventAt (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus 0
    first.items = run.programme.law.rawItems before (run.trajectory.move 0).word ∧
    first.after.raw = run.trajectory.state 1 := by
  let first := Runtime.eventAt (Occurrence.reached answers loss word) run.programme
    (originalRaw loss) run.people run.menus 0
  have effects := first.first_paid_word_controls_the_actual_effect
    run.trajectory.firstMove.word _ rfl run.trajectory.firstMove.paid
  exact ⟨effects.2.2, effects.2.1.trans run.trajectory.firstMove_next⟩

end Realization

def realize (viable : ViableEntry loss answers registered word offers) :
    Realization loss answers registered word offers := by
  let choice := Classical.choose viable.2.2
  have prepared := Classical.choose_spec viable.2.2
  let first := Classical.choose prepared.2
  have paid := Classical.choose_spec prepared.2
  exact ⟨viable.1, viable.2.1, choice, prepared.1,
    Trajectory.prepend first (Runtime.Viability.strategy paid.2), paid.1⟩

theorem realization_has_an_exactly_viable_source
    (run : Realization loss answers registered word offers) :
    ViableEntry loss answers registered word offers := by
  refine ⟨run.allowed, run.originalEntry, run.choice, run.approved, run.trajectory.firstMove, run.pilot, ?_⟩
  rw [run.trajectory.firstMove_next]
  exact run.trajectory.every_actual_state_is_live 1

theorem viable_entry_of_original_live
    (allowed : Occurrence.Unbounded.Allowed answers loss registered word) (ready : ReadyEntry loss word)
    (live : Live seed.native.input (originalRaw loss) (originalBearers loss)
      (endAt seed (Occurrence.history loss ++ word)).raw) :
    ViableEntry loss answers registered word offers :=
  realization_has_an_exactly_viable_source
    ⟨allowed, ready, none, trivial, Runtime.Viability.strategy live, trivial⟩

theorem viable_entry_iff_actual_terminal :
    ViableEntry loss answers registered word offers ↔ Nonempty (Realization loss answers registered word offers) :=
  ⟨fun viable => ⟨realize viable⟩, fun ⟨actual⟩ => realization_has_an_exactly_viable_source actual⟩

theorem retain_viable_entry (viable : ViableEntry loss answers registered word) :
    ViableEntry loss answers registered word offers := by
  obtain ⟨allowed, ready, choice, approved, first, pilot, live⟩ := viable
  cases choice with
  | none => exact ⟨allowed, ready, none, approved, first, pilot, live⟩
  | some absent => exact Fin.elim0 absent

theorem Realization.every_paid_visit_keeps_the_origin_address
    (run : Realization loss answers registered word offers) (n : Nat) :
    let actual := Runtime.run (Occurrence.reached answers loss word) run.programme
      (originalRaw loss) run.people run.menus n
    ∃ row, actual.state.read row = .inr (loss, Occurrence.balance answers loss word) := by
  apply Reparation.Actual.StateAt.every_balance_is_a_row_of_the_current
  rw [Runtime.every_actual_visit_keeps_the_original_rows]
  exact Occurrence.balance_is_in_the_reached_rows answers loss word

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal
