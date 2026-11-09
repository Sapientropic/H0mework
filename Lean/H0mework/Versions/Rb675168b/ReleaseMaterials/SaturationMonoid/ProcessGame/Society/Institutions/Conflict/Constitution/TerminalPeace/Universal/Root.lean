import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Minimum
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Projection

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Quantities.Execution (endAt)
open Reparation.Actual (ReceiptAnswers Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (loss : Reparation.Actual.Occurrence seed community)

def originalBearers : List Party :=
  ExposureGuard.bearers seed community (Occurrence.history loss)

theorem the_original_victim_is_always_in_the_protected_roster :
    loss.key.1 ∈ originalBearers loss :=
  ExposureGuard.every_original_victim_is_a_bearer seed community (Occurrence.history loss)
    loss (Occurrence.origin_in_material_history loss)

def originalRaw : RawCurrent Party Good Technology Instrument :=
  (endAt seed (Occurrence.history loss)).raw

variable (answers : ReceiptAnswers seed) (payments : List (Script Party Good Port Technology Instrument))
  (menus : Runtime.Menus Party Good Port Technology Instrument)

/-- Compile the original reparation, then start the living dispatcher at
that very ledger successor. Inputs are literal submissions and the
original personal answers, with no supplied safety family. -/
def compile :
    (selected : Occurrence.MenuChoice answers loss payments) ×
      Runtime.Outcome selected.state seed.native.input (originalRaw loss) (originalBearers loss) menus :=
  let selected := Occurrence.choose answers loss payments
  ⟨selected, Runtime.classify selected.state seed.native.input (originalRaw loss) (originalBearers loss) menus⟩

theorem an_arbitrary_actual_war_generates_its_accounted_original_future :
    let selected := (compile loss answers payments menus).1
    (∃ row, selected.state.read row = .inr (loss, Occurrence.balance answers loss selected.word)) ∧
    (∀ candidate, (candidate = [] ∨ candidate ∈ payments) → Occurrence.Eligible answers loss candidate →
      selected.minimum ≤ (Occurrence.balance answers loss candidate).remaining) ∧
    ∀ n,
      let installed := Runtime.run selected.state seed.native.input (originalRaw loss) (originalBearers loss) menus n
      installed.state.stack.balances = selected.state.stack.balances ∧
      (∃ row, installed.state.read row = .inr (loss, Occurrence.balance answers loss selected.word)) ∧
      ∀ item ∈ installed.read.items, ∀ key, Reparation.loss seed.native.input.law community item key = 0 := by
  let selected := Occurrence.choose answers loss payments
  change (∃ row, selected.state.read row = .inr (loss, Occurrence.balance answers loss selected.word)) ∧
    (∀ candidate, (candidate = [] ∨ candidate ∈ payments) → Occurrence.Eligible answers loss candidate →
      selected.minimum ≤ (Occurrence.balance answers loss candidate).remaining) ∧ _
  have original := Occurrence.balance_is_in_the_reached_rows answers loss selected.word
  refine ⟨selected.chosen_keeps_the_original_row_on_its_recorded_successor.2, selected.least, fun n => ?_⟩
  let installed := Runtime.run selected.state seed.native.input (originalRaw loss) (originalBearers loss) menus n
  have retained := Runtime.every_actual_visit_keeps_the_original_rows selected.state
    seed.native.input (originalRaw loss) (originalBearers loss) menus n
  refine ⟨retained, installed.state.every_balance_is_a_row_of_the_current _ ?_, ?_⟩
  · rw [retained]
    exact original
  · exact Runtime.no_actual_service_or_refusal_causes_new_war_damage selected.state
      seed.native.input (originalRaw loss) (originalBearers loss) menus n

def auditExternal (external : External.Trace Runtime.Current (Runtime.Write Party Good Port Technology Instrument)) :=
  let selected := (compile loss answers payments menus).1
  Runtime.auditExternal selected.state seed.native.input (originalRaw loss) (originalBearers loss) menus external

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal
