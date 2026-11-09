import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Runtime.Selection
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts.Preservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_append)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument

/-- The original live state with its inherited exposure cut and the
safety of its actual continuation. -/
structure Visit (seed : C) (community : Party → Community) (anchor : Word) (viable : Word → Prop) where
  history : Word
  original : anchor.IsPrefix history
  state : Reparation.Actual.State seed community history
  origins : state.stack.balances.map Prod.fst = Reparation.Actual.originalLosses seed community history
  continues : viable history

namespace Visit

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port Technology Instrument}
  {viable : Reparation.Actual.Script Party Good Port Technology Instrument → Prop}

def start (state : Reparation.Actual.State seed community anchor)
    (origins : state.stack.balances.map Prod.fst = Reparation.Actual.originalLosses seed community anchor)
    (live : viable anchor) :
    Visit seed community anchor viable :=
  ⟨anchor, List.prefix_rfl, state, origins, live⟩

variable (prior : Visit seed community anchor viable)

def roster : List Party :=
  bearers seed community anchor ++ bearers seed community prior.history

theorem every_original_loss_has_an_exact_live_row
    (origin : Reparation.Actual.Occurrence seed community)
    (opened : origin ∈ Reparation.Actual.originalLosses seed community prior.history) :
    ∃ balance, ∃ row, prior.state.read row = .inr (origin, balance) := by
  rw [← prior.origins] at opened
  obtain ⟨⟨found, balance⟩, listed, rfl⟩ := List.mem_map.mp opened
  obtain ⟨row, exactRow⟩ := prior.state.every_balance_is_a_row_of_the_current _ listed
  exact ⟨balance, row, exactRow⟩

variable (answers : OwnerAnswers seed)
  (extension : Rule seed) [DecidableRule extension]
  (check : Probe viable)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

def verdict := select prior.roster answers extension viable check prior.history input

def advance (chosen : Selection prior.roster answers extension viable check prior.history input) :
    Visit seed community anchor viable :=
  ⟨prior.history ++ chosen.emitted, prior.original.trans (List.prefix_append _ _),
    Receipts.writeAfter answers prior.state chosen.emitted,
    Receipts.writeAfter_origins answers prior.history chosen.emitted prior.state prior.origins,
    chosen.next_keeps_the_required_continuation prior.continues⟩

def step : Visit seed community anchor viable :=
  prior.advance answers extension check input (prior.verdict answers extension check input)

theorem step_writes_only_the_selected_original_suffix :
    let chosen := prior.verdict answers extension check input
    let reached := prior.step answers extension check input
    Quantities.Recorded seed reached.history ∧
      reached.state = Receipts.writeAfter answers prior.state chosen.emitted :=
  ⟨Quantities.record _ _, rfl⟩

variable (person : Party)

theorem a_rival_visit_cannot_reduce_the_stock_of_the_refusing_original_bearer
    (exposed : person ∈ bearers seed community anchor) (good : Good) :
    (endAt seed prior.history).raw.stock person good ≤
      (endAt seed (prior.step (withhold answers person) extension check input).history).raw.stock person good := by
  let chosen := prior.verdict (withhold answers person) extension check input
  have standing : person ∈ prior.roster := List.mem_append_left _ exposed
  change _ ≤ (endAt seed (prior.history ++ chosen.emitted)).raw.stock person good
  rw [endAt_append]
  generalize chosen = selected
  cases selected with
  | retained => exact le_rfl
  | accepted lawful _ _ =>
    exact each_admitted_rival_input_preserves_the_refusers_original_stock prior.roster answers prior.history input
      person standing lawful good
  | stopped _ empty _ =>
    exact each_admitted_rival_input_preserves_the_refusers_original_stock prior.roster answers prior.history stop
      person standing (no_material_is_admitted prior.roster (withhold answers person) prior.history stop empty) good

theorem a_rival_visit_preserves_the_refusing_victims_exact_balance
    (origin : Reparation.Actual.Occurrence seed community) (balance : Reparation.Actual.Balance)
    (same : origin.key.1 = person) (old : (origin, balance) ∈ prior.state.stack.balances) :
    ∃ row, (prior.step (withhold answers person) extension check input).state.read row = .inr (origin, balance) := by
  subst person
  exact Receipts.the_exact_withheld_balance_is_read_on_the_original_successor answers prior.history
    (prior.verdict (withhold answers origin.key.1) extension check input).emitted prior.state origin balance old

end Visit

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
