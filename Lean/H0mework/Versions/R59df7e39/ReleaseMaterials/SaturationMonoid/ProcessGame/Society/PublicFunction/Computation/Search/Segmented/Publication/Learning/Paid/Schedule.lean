import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.History

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Schedule
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {baseline : Program model.source.code (horizon domain)} {actualHorizon : Nat}

/-- The task load is source-generated; its registered tariff is per batch.
Neither this load nor the tariff asserts hardware instruction counts. -/
structure Load where
  localCases : Nat
  retainedCells : Nat
  reviewRows : Nat

def load (state : State model domain original baseline actualHorizon) : Load :=
  ⟨state.beliefs.length, state.past.length + state.programme.controls.length,
    (Replanning.rows model domain).length⟩

def request (state : State model domain original baseline actualHorizon)
    (unit : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) : Charge.Quote
      (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  if state.beliefs.isEmpty then ⟨[],unit.selection⟩ else unit

def requests (state : State model domain original baseline actualHorizon)
    (reader : Fin model.source.code.sites)
    (point : View (code := model.source.code)) (rival : Opponent model.source.code)
    (unit : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) : Nat →
      Paid.Requests (Party := Party) (Good := Good) (Port := Port)
        (Technology := Technology) (Instrument := Instrument)
  | 0 => []
  | fuel+1 =>
      let quoted := request state unit
      quoted :: requests (Paid.turn state reader quoted point rival).next reader point rival unit fuel

theorem every_next_resource_request_is_generated_from_the_actual_last_cache
    (state : State model domain original baseline actualHorizon)
    (reader : Fin model.source.code.sites) (point : View (code := model.source.code))
    (rival : Opponent model.source.code)
    (unit : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (fuel : Nat) :
    requests state reader point rival unit (fuel+1) = request state unit ::
      requests (Paid.turn state reader (request state unit) point rival).next reader point rival unit fuel := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Schedule
