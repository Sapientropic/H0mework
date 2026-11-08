import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenInletSource
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active State prepared delay)
open InletOmissionSource (Command Controller Attempt after observe attempt)
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
local notation "Word" => RawEvent Party Good Port (Mandate.State Party Technology) Instrument
local notation "Cmd" => Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)

def retired (state : State old instructions) (command : Cmd) : Word :=
  if observe old instructions state command = some .executed then (state.pending ++ command.incoming).take 1 else []

structure Result where
  state : State old instructions
  stages : List (EventHistory.Stage (code := Active old instructions))
  arrivals : Word
  retired : Word
  attempts : List (Attempt old instructions)

-- No initial queue-length counter stops later input from reaching the original interpreter.
def run (initial : State old instructions) (control : Controller old instructions) : Nat → Result old instructions :=
  Nat.rec ⟨initial,[],[],[],[]⟩ fun _ previous =>
    let command := control previous.state
    ⟨after old instructions previous.state command,
      previous.stages ++ InletOmissionSource.stages old instructions previous.state command,
      previous.arrivals ++ command.incoming,
      previous.retired ++ retired old instructions previous.state command,
      previous.attempts ++ [attempt old instructions previous.state command]⟩

def isWithheld (entry : Attempt old instructions) : Nat := if entry.observation = some .withheld then 1 else 0
def isGap (entry : Attempt old instructions) : Nat := if entry.observation = none then 1 else 0
def isObstructed (entry : Attempt old instructions) : Nat :=
  if entry.observation = some .executed ∨ entry.observation = some .withheld ∨ entry.observation = none then 0 else 1

def omissions (result : Result old instructions) := (result.attempts.map (isWithheld old instructions)).sum
def gaps (result : Result old instructions) := (result.attempts.map (isGap old instructions)).sum
def obstructions (result : Result old instructions) := (result.attempts.map (isObstructed old instructions)).sum

-- Re-offer an unpaid first-delivery obligation. Prior failed attempts remain in the source history.
def offer (cursor : Cursor (Active old instructions)) : Move (Active old instructions) :=
  match (NativeDeliveryJournal.pending cursor).head? with
  | none => none
  | some serial => if admitted : .deliver serial ∈ (Active old instructions).eventAlphabet then
      some ⟨.deliver serial,admitted⟩ else none

def recoveryStages (state : State old instructions) : List (EventHistory.Stage (code := Active old instructions)) :=
  SilentWindow.stages (delay old instructions state) ++
    [(SilentWindow.quiet,EventStep.fixed (offer old instructions (prepared old instructions state)))]

def recover (state : State old instructions) : State old instructions :=
  ⟨EventHistory.execute state.cursor (recoveryStages old instructions state),state.pending⟩

def joinedStages (initial : State old instructions) (control : Controller old instructions) (count : Nat) :=
  (run old instructions initial control count).stages ++ recoveryStages old instructions (run old instructions initial control count).state
abbrev next (initial : State old instructions) (control : Controller old instructions) (count : Nat) :=
  recover old instructions (run old instructions initial control count).state

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OpenInletSource
