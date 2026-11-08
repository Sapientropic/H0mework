import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedRetryProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenDeliverySource
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active)
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
abbrev State := FundedRetrySource.State old instructions
structure Command where
  supply : FundedRetrySource.Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  network : Opponent (Active old instructions)
abbrev Controller := State old instructions → Command old instructions
variable (start : Cursor (Active old instructions))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := Active old instructions)) (law : StageReception.Law (Active old instructions))
abbrev prepared (state : State old instructions) (command : Command old instructions) :=
  FundedRetrySource.prepared old instructions start state command.supply
abbrev plan (state : State old instructions) (command : Command old instructions) :=
  TimedRetry.produce start (prepared old instructions start state command) vocabulary encoding law
abbrev schedule (past : List (EventHistory.Stage (code := Active old instructions)))
    (answer : TimedRetry.Ready start past vocabulary encoding law) (network : Opponent (Active old instructions)) :=
  TimedRetry.sent start past vocabulary encoding law answer.overdue answer.supported ++ [(SilentWindow.quiet,network)]

-- The send is committed before the real callback; the callback sees its new history and packet.
def after (state : State old instructions) (command : Command old instructions) : State old instructions :=
  ⟨match plan old instructions start vocabulary encoding law state command with
    | .ready answer => schedule old instructions start vocabulary encoding law _ answer command.network
    | _ => prepared old instructions start state command,
    (FundedRetrySource.supplied old instructions start state command.supply).pending⟩
structure Attempt where
  state : State old instructions
  command : Command old instructions
inductive Kind where | confirmed | unconfirmed | blocked | idle deriving DecidableEq

-- Transport history equalities before unfolding the dependent receipt decision.
def confirmationKind (past : List (EventHistory.Stage (code := Active old instructions)))
    (emission : StageDuty.Emission start vocabulary encoding) : Kind :=
  if TimedDuty.Confirmed start past vocabulary encoding law emission then .confirmed else .unconfirmed

def kind (entry : Attempt old instructions) : Kind :=
  match plan old instructions start vocabulary encoding law entry.state entry.command with
  | .idle => .idle
  | .blocked _ => .blocked
  | .ready answer =>
    confirmationKind old instructions start vocabulary encoding law
      (schedule old instructions start vocabulary encoding law _ answer entry.command.network) answer.overdue.emission
structure Result where
  state : State old instructions
  attempts : List (Attempt old instructions)
  arrivals : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  retired : RawEvent Party Good Port (Mandate.State Party Technology) Instrument

-- Idle ends no world or input stream. Every observation queries the actual successor again.
def run (initial : State old instructions) (control : Controller old instructions) : Nat → Result old instructions :=
  Nat.rec ⟨initial,[],[],[]⟩ fun _ previous =>
    let command := control previous.state
    ⟨after old instructions start vocabulary encoding law previous.state command,
      previous.attempts ++ [⟨previous.state,command⟩],
      previous.arrivals ++ (FundedRetrySource.feed old instructions start previous.state command.supply).arrivals,
      previous.retired ++ (FundedRetrySource.feed old instructions start previous.state command.supply).retired⟩
theorem run_zero (initial : State old instructions) (control : Controller old instructions) :
    run old instructions start vocabulary encoding law initial control 0 = ⟨initial,[],[],[]⟩ := rfl
theorem run_succ (initial : State old instructions) (control : Controller old instructions) (count : Nat) :
    run old instructions start vocabulary encoding law initial control (count + 1) =
      let previous := run old instructions start vocabulary encoding law initial control count
      let command := control previous.state
      ⟨after old instructions start vocabulary encoding law previous.state command,
        previous.attempts ++ [⟨previous.state,command⟩],
        previous.arrivals ++ (FundedRetrySource.feed old instructions start previous.state command.supply).arrivals,
        previous.retired ++ (FundedRetrySource.feed old instructions start previous.state command.supply).retired⟩ := rfl
def confirmedCount (entries : List (Attempt old instructions)) : Nat :=
  (entries.map fun entry => if kind old instructions start vocabulary encoding law entry = .confirmed then 1 else 0).sum
abbrev confirmations := FundedRetrySource.confirmations old instructions start vocabulary encoding law
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenDeliverySource
