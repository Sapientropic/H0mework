import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletSource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)

def catalogue : CatalogueHandoffSource.Catalogue old :=
  ⟨[],0,[],0,instructions.map Event.adversary⟩
abbrev code := CatalogueHandoffSource.code old (catalogue old instructions)
abbrev start (saved : Cursor old) := CatalogueHandoffSource.cursor old (catalogue old instructions) saved

-- Admission extends only the future interface. Resource validity is decided by actual execution.
def request (instruction : Request Party Good Port (Mandate.State Party Technology) Instrument) : Move (code old instructions) :=
  if admitted : .adversary instruction ∈ (code old instructions).eventAlphabet then
    some ⟨.adversary instruction,admitted⟩ else none

def rival (enabled : Bool) (instruction : Request Party Good Port (Mandate.State Party Technology) Instrument) :
    Opponent (code old instructions) := EventStep.fixed (if enabled then request old instructions instruction else none)
abbrev row (saved : Cursor (code old instructions)) (protocol : Rule (code old instructions))
    (enabled : Bool) (instruction : Request Party Good Port (Mandate.State Party Technology) Instrument) :=
  StageTrace.material saved protocol (rival old instructions enabled instruction)
abbrev next (saved : Cursor (code old instructions)) (protocol : Rule (code old instructions))
    (enabled : Bool) (instruction : Request Party Good Port (Mandate.State Party Technology) Instrument) :=
  saved.after protocol (rival old instructions enabled instruction)

inductive Verdict where
  | stopped | owned | withheld | unadmitted | refused | executed
  deriving DecidableEq

def assess (saved : Cursor (code old instructions)) (protocol : Rule (code old instructions))
    (enabled : Bool) (instruction : Request Party Good Port (Mandate.State Party Technology) Instrument) : Verdict :=
  match (row old instructions saved protocol enabled instruction).call with
  | .stopped => .stopped
  | .external attempt => match attempt with
    | none => if enabled then .unadmitted else .withheld
    | some _ => if ∀ item ∈ StageTrace.items (row old instructions saved protocol enabled instruction),
        old.law.Valid item.before item.request then .executed else .refused
  | _ => .owned

theorem admitted_request_is_the_source_instruction
    (instruction : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (chosen : Choice (code old instructions))
    (found : request old instructions instruction = some chosen) : chosen.val = .adversary instruction := by
  unfold request at found
  split at found <;> try contradiction
  cases Option.some.inj found
  rfl

-- Incoming data are raw proposals. Only the admitted actual event can change stocks; a refusal keeps its head.
structure State where
  cursor : Cursor (code old instructions)
  pending : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
structure Command where
  protocol : Rule (code old instructions)
  enabled : Bool
  incoming : RawEvent Party Good Port (Mandate.State Party Technology) Instrument

def stage (state : State old instructions) (command : Command old instructions) :
    EventHistory.Stage (code := code old instructions) :=
  (command.protocol,match state.pending ++ command.incoming with
    | [] => EventStep.fixed none
    | instruction :: _ => rival old instructions command.enabled instruction)

def step (state : State old instructions) (command : Command old instructions) : State old instructions :=
  ⟨state.cursor.after (stage old instructions state command).1 (stage old instructions state command).2,
    match state.pending ++ command.incoming with
    | [] => []
    | instruction :: tail =>
      if assess old instructions state.cursor command.protocol command.enabled instruction = .executed
        then tail else state.pending ++ command.incoming⟩
abbrev Controller := State old instructions → Command old instructions
def run (initial : State old instructions) (controller : Controller old instructions) : Nat → State old instructions :=
  Nat.rec initial fun _ state => step old instructions state (controller state)

def trace (initial : State old instructions) (controller : Controller old instructions) :
    Nat → List (EventHistory.Stage (code := code old instructions))
  := Nat.rec [] fun count past => past ++
    [stage old instructions (run old instructions initial controller count)
      (controller (run old instructions initial controller count))]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletSource
