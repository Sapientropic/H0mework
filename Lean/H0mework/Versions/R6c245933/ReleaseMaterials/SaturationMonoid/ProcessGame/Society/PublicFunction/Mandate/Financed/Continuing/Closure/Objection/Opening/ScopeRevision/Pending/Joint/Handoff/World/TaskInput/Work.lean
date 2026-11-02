import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work
open Institutions.Capitalism.Universal.Source.Program
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Input.Recovery.Metering.Assessment.Relation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {law : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}

def model (source : Native.Authority.Sources law scope) : Native.Authority.Bound
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨law,scope,source.val,source.property.1,source.property.2⟩

def units (input : TaskInput law scope) (source : Native.Authority.Sources law scope)
    (domain : List (Cursor source.val.code))
    (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)) : Nat := by
  cases input with
  | actual inventory => exact Feed.Work.units (model source) domain requested

  | received inventory _origin => exact Feed.Work.units (model source) domain requested

def Batch (input : TaskInput law scope) (source : Native.Authority.Sources law scope)
    (domain : List (Cursor source.val.code)) (original : Rule source.val.code)
    (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (tariff : Native.Future.Recovery.Pricing
      (Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument)) : Type := by
  cases input with
  | actual inventory => exact Feed.Work.Batch (model source) domain original requested inventory tariff

  | received inventory _origin => exact Feed.Work.Batch (model source) domain original requested inventory tariff

def execute (input : TaskInput law scope) (source : Native.Authority.Sources law scope)
    (domain : List (Cursor source.val.code)) (original : Rule source.val.code)
    (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (tariff : Native.Future.Recovery.Pricing
      (Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument)) :
    Batch input source domain original requested tariff := by
  cases input with
  | actual inventory => exact Feed.Work.execute (model source) domain original requested inventory tariff

  | received inventory _origin => exact Feed.Work.execute (model source) domain original requested inventory tariff

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work
