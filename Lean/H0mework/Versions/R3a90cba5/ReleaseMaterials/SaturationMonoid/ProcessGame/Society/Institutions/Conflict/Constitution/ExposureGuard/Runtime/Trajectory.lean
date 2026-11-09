import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Runtime.Visit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument

inductive Lane
  | personal
  | rival

/-- Scheduling can interleave the two streams. Selecting the personal
lane reads its own source programme, even when rivals choose their input
using the entire already executed history. -/
structure Scheduler (Party Good Port Technology Instrument : Type) where
  lane : Nat → Reparation.Actual.Script Party Good Port Technology Instrument → Lane
  personal : Nat → Reparation.Actual.Script Party Good Port Technology Instrument →
    Reparation.Actual.Input Party Good Port Technology Instrument
  rival : Nat → Reparation.Actual.Script Party Good Port Technology Instrument →
    Reparation.Actual.Input Party Good Port Technology Instrument
  offer : Nat → Reparation.Actual.Script Party Good Port Technology Instrument →
    Reparation.Actual.Script Party Good Port Technology Instrument →
    Reparation.Actual.Script Party Good Port Technology Instrument

namespace Scheduler

variable (schedule : Scheduler Party Good Port Technology Instrument)

def proposal (tick : Nat) (past : Word) : Input :=
  match schedule.lane tick past with
  | .personal => schedule.personal tick past
  | .rival => schedule.rival tick past

variable {seed : Root.Cut Party Good Port Technology Instrument}
  (answers : OwnerAnswers seed) (person : Party)

def replies (tick : Nat) (past : Word) : OwnerAnswers seed :=
  match schedule.lane tick past with
  | .personal => answers
  | .rival => withhold answers person

theorem rival_inputs (tick : Nat) (past : Word) (rival : schedule.lane tick past = .rival) :
    schedule.replies answers person tick past = withhold answers person ∧
      schedule.proposal tick past = schedule.rival tick past := by
  unfold replies proposal
  rw [rival]
  exact ⟨rfl, rfl⟩

variable {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port Technology Instrument}
  {viable : Reparation.Actual.Script Party Good Port Technology Instrument → Prop}
  (extension : Rule seed) [DecidableRule extension]
  (check : Nat → Reparation.Actual.Script Party Good Port Technology Instrument → Probe viable)
  (initial : Visit seed community anchor viable)

def run : Nat → Visit seed community anchor viable
  | 0 => initial
  | tick + 1 =>
    let prior := run tick
    prior.step (schedule.replies answers person tick prior.history) extension
      (check tick prior.history)
      (schedule.proposal tick prior.history)

theorem every_scheduled_prefix_keeps_the_original_whole_state (tick : Nat) :
    let prior := schedule.run answers person extension check initial tick
    let replies := schedule.replies answers person tick prior.history
    let proposed := schedule.proposal tick prior.history
    let emitted := (prior.verdict replies extension (check tick prior.history) proposed).emitted
    let reached := schedule.run answers person extension check initial (tick + 1)
    Quantities.Recorded seed reached.history ∧
      reached.state = Receipts.writeAfter replies prior.state emitted ∧ viable reached.history :=
  ⟨Quantities.record _ _, rfl, (schedule.run answers person extension check initial (tick + 1)).continues⟩

theorem any_adaptive_coalition_visit_preserves_the_refusing_bearers_stock
    (exposed : person ∈ bearers seed community anchor) (tick : Nat) (good : Good)
    (rival : schedule.lane tick (schedule.run answers person extension check initial tick).history = .rival) :
    (endAt seed (schedule.run answers person extension check initial tick).history).raw.stock person good ≤
      (endAt seed (schedule.run answers person extension check initial (tick + 1)).history).raw.stock person good := by
  let prior := schedule.run answers person extension check initial tick
  have selected := schedule.rival_inputs answers person tick prior.history rival
  change _ ≤ (endAt seed (prior.step (schedule.replies answers person tick prior.history) extension
    (check tick prior.history)
    (schedule.proposal tick prior.history)).history).raw.stock person good
  rw [selected.1, selected.2]
  exact prior.a_rival_visit_cannot_reduce_the_stock_of_the_refusing_original_bearer
    answers extension (check tick prior.history) (schedule.rival tick prior.history) person exposed good

theorem any_adaptive_coalition_visit_preserves_the_refusing_victims_reparation
    (tick : Nat) (origin : Reparation.Actual.Occurrence seed community) (balance : Reparation.Actual.Balance)
    (victim : origin.key.1 = person)
    (old : (origin, balance) ∈ (schedule.run answers person extension check initial tick).state.stack.balances)
    (rival : schedule.lane tick (schedule.run answers person extension check initial tick).history = .rival) :
    ∃ row, (schedule.run answers person extension check initial (tick + 1)).state.read row = .inr (origin, balance) := by
  let prior := schedule.run answers person extension check initial tick
  have selected := schedule.rival_inputs answers person tick prior.history rival
  change ∃ row, (prior.step (schedule.replies answers person tick prior.history) extension
    (check tick prior.history)
    (schedule.proposal tick prior.history)).state.read row = .inr (origin, balance)
  rw [selected.1, selected.2]
  exact prior.a_rival_visit_preserves_the_refusing_victims_exact_balance answers extension (check tick prior.history)
    (schedule.rival tick prior.history) person origin balance victim old

end Scheduler

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
