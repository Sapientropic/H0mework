import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work.Prefix
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
  (input : TaskInput law scope) (source : Native.Authority.Sources law scope)
  (domain : List (Cursor source.val.code)) (original : Rule source.val.code)
  (past : List (Rule source.val.code)) (reference : Whole.Program source.val.code (horizon domain))
  (requested : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
  (tariff : Native.Future.Recovery.Pricing
    (Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument))

def Outcome : Type := by
  cases input with
  | actual inventory => exact Feed.Prefix.Outcome inventory (model source) domain original past reference tariff requested

  | received inventory _origin => exact Feed.Prefix.Outcome inventory (model source) domain original past reference tariff requested

def compile (batch : Batch input source domain original requested tariff) :
    Outcome input source domain original past reference requested tariff := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.compile inventory (model source) domain original past reference tariff requested batch

  | received inventory _origin => exact Feed.Work.Prefix.compile inventory (model source) domain original past reference tariff requested batch

/-- The original candidate is retained with its original complete verification. -/
def candidate? (outcome : Outcome input source domain original past reference requested tariff) :
    Option (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := tariff) (requested := requested) (model source) domain original past reference) := by
  cases input with
  | actual inventory =>
      cases outcome with
      | selected candidate => exact some candidate.previous
      | blocked _ => exact none


  | received inventory _origin =>
      cases outcome with
      | selected candidate => exact some candidate.previous
      | blocked _ => exact none


/-- Independent logical review retains the original typed failure and every admitted row. -/
def Reviewed (outcome : Outcome input source domain original past reference requested tariff) : Prop := by
  cases input with
  | actual inventory => exact Feed.Prefix.review outcome = true

  | received inventory _origin => exact Feed.Prefix.review outcome = true

theorem reviewed (outcome : Outcome input source domain original past reference requested tariff) :
    Reviewed input source domain original past reference requested tariff outcome := by
  cases input with
  | actual inventory => exact Feed.Prefix.every_generated_outcome_has_its_raw_source_review outcome

  | received inventory _origin => exact Feed.Prefix.every_generated_outcome_has_its_raw_source_review outcome

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work.Prefix
