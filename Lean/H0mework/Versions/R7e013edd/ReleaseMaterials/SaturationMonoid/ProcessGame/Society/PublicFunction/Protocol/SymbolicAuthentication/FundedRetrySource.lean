import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenInletProgress
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedRetrySource
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active)
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)

structure State where
  history : List (EventHistory.Stage (code := Active old instructions))
  pending : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
abbrev Command := InletOmissionSource.Command (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
abbrev Controller := State old instructions → Command (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

variable (start : Cursor (Active old instructions))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := Active old instructions)) (law : StageReception.Law (Active old instructions))
abbrev cursor (state : State old instructions) := EventHistory.execute start state.history
abbrev inlet (state : State old instructions) : InletClockedSource.State old instructions := ⟨cursor old instructions start state,state.pending⟩
abbrev feed (state : State old instructions) (command : Command (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :=
  OpenInletSource.run old instructions (inlet old instructions start state) (fun _ => command) 1
abbrev supplied (state : State old instructions) (command : Command (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :=
  OpenInletSource.next old instructions (inlet old instructions start state) (fun _ => command) 1
abbrev prepared (state : State old instructions) (command : Command (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :=
  state.history ++ OpenInletSource.joinedStages old instructions (inlet old instructions start state) (fun _ => command) 1
abbrev plan (state : State old instructions) (command : Command (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :=
  TimedRetry.produce start (prepared old instructions start state command) vocabulary encoding law
abbrev after (state : State old instructions) (command : Command (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : State old instructions :=
  ⟨TimedRetry.stages start (prepared old instructions start state command) vocabulary encoding law,
    (supplied old instructions start state command).pending⟩

structure Attempt where
  state : State old instructions
  command : Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
inductive Kind where | ready | blocked | idle deriving DecidableEq

def kind (entry : Attempt old instructions) : Kind :=
  match plan old instructions start vocabulary encoding law entry.state entry.command with
  | .ready _ => .ready | .blocked _ => .blocked | .idle => .idle
inductive Status where | noOverdue | observationLimit deriving DecidableEq
structure Result where
  state : State old instructions
  attempts : List (Attempt old instructions)
  arrivals : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  retired : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  status : Status

-- Stop this communication observation at idle; pending input and the whole cursor remain live.
-- Explicit Nat.rec avoids unsafe generated execution helpers in the whole-module kernel audit.
def run (control : Controller old instructions) : Nat → State old instructions → Result old instructions :=
  Nat.rec (fun state => ⟨state,[],[],[],.observationLimit⟩) fun _ previous state =>
    let command := control state
    let successor := after old instructions start vocabulary encoding law state command
    let entry : Attempt old instructions := ⟨state,command⟩
    if kind old instructions start vocabulary encoding law entry = .idle then
      ⟨successor,[entry],(feed old instructions start state command).arrivals,
        (feed old instructions start state command).retired,.noOverdue⟩
    else
      let tail := previous successor
      ⟨tail.state,entry :: tail.attempts,(feed old instructions start state command).arrivals ++ tail.arrivals,
        (feed old instructions start state command).retired ++ tail.retired,tail.status⟩

theorem run_zero (control : Controller old instructions) (state : State old instructions) :
    run old instructions start vocabulary encoding law control 0 state = ⟨state,[],[],[],.observationLimit⟩ := rfl

theorem run_succ (control : Controller old instructions) (count : Nat) (state : State old instructions) :
    run old instructions start vocabulary encoding law control (count+1) state =
    let command := control state
    let successor := after old instructions start vocabulary encoding law state command
    let entry : Attempt old instructions := ⟨state,command⟩
    if kind old instructions start vocabulary encoding law entry = .idle then
      ⟨successor,[entry],(feed old instructions start state command).arrivals,
        (feed old instructions start state command).retired,.noOverdue⟩
    else
      let tail := run old instructions start vocabulary encoding law control count successor
      ⟨tail.state,entry :: tail.attempts,(feed old instructions start state command).arrivals ++ tail.arrivals,
        (feed old instructions start state command).retired ++ tail.retired,tail.status⟩ := rfl

def tally (tag : Kind) (entries : List (Attempt old instructions)) : Nat :=
  (entries.map fun entry => if kind old instructions start vocabulary encoding law entry = tag then 1 else 0).sum
abbrev confirmations (state : State old instructions) := (DutyConfirmation.contents start vocabulary encoding law state.history).card
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedRetrySource
