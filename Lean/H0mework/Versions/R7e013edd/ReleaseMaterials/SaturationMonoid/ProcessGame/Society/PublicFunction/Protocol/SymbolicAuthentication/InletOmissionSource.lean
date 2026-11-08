import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionSource
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active State queued prepared delay strip ClockFree)
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
local notation "Word" => RawEvent Party Good Port (Mandate.State Party Technology) Instrument

structure Command where
  enabled : Bool
  incoming : Word
abbrev Controller := State old instructions → Command (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
variable (state : State old instructions)
  (command : Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
abbrev localCommand : LiveProductionInletSource.Command old instructions := ⟨SilentWindow.quiet,command.enabled,[]⟩
abbrev stage := LiveProductionInletSource.stage old instructions
  (queued old instructions state command.incoming) (localCommand old instructions command)
abbrev row := StageTrace.material (prepared old instructions state) SilentWindow.quiet (stage old instructions state command).2
abbrev after := LiveProductionInletSource.step old instructions
  (queued old instructions state command.incoming) (localCommand old instructions command)
def observe : Option LiveProductionInletSource.Verdict :=
  match state.pending ++ command.incoming with
  | [] => none
  | head :: _ => some (LiveProductionInletSource.assess old instructions (prepared old instructions state) SilentWindow.quiet command.enabled head)
def stages : List (EventHistory.Stage (code := Active old instructions)) :=
  SilentWindow.stages (delay old instructions state) ++ [stage old instructions state command]

structure Attempt where
  state : State old instructions
  command : Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  row : StageTrace.Record (code := Active old instructions)
  observation : Option LiveProductionInletSource.Verdict

def attempt : Attempt old instructions := ⟨state,command,row old instructions state command,observe old instructions state command⟩

structure Result where
  unserved : Nat
  state : State old instructions
  stages : List (EventHistory.Stage (code := Active old instructions))
  submitted : Word
  arrivals : Word
  withheld : Nat
  attempts : List (Attempt old instructions)

def idle (remaining : Nat) : Result old instructions := ⟨remaining,state,[],[],[],0,[]⟩
-- Counts change only after the original interpreter reports executed/withheld.
-- In particular a refusal neither retires the head nor spends the withholding allowance.
def run (control : Controller old instructions) : Nat → Nat → State old instructions → Result old instructions :=
  Nat.rec (fun remaining state => idle old instructions state remaining) fun _ previous remaining state =>
    if remaining = 0 then idle old instructions state 0 else
      let command := control state
      let observation := observe old instructions state command
      let tail := previous (remaining - if observation = some .executed then 1 else 0)
        (after old instructions state command)
      ⟨tail.unserved,tail.state,stages old instructions state command ++ tail.stages,
        (row old instructions state command).submitted ++ tail.submitted,
        command.incoming ++ tail.arrivals,
        (if observation = some .withheld then 1 else 0) + tail.withheld,
        attempt old instructions state command :: tail.attempts⟩
abbrev produce (control : Controller old instructions) (attempts : Nat) :=
  run old instructions control attempts state.pending.length state

-- An allowance enlarges the original opportunity check; it never changes control requests.
def funded (allowance : Nat) : Bool := decide (
  state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length ∧
  2 * (state.pending.length + allowance) ≤ (EventStep.seed state.cursor).remaining ∧
  (∀ instruction ∈ state.pending,instruction ∈ instructions) ∧
  (∀ item ∈ old.law.rawItems (strip (EventStep.seed state.cursor).current) state.pending,
    old.law.Valid item.before item.request))

theorem stopped (control : Controller old instructions) (count : Nat) :
    run old instructions control count 0 state = idle old instructions state 0 := by
  cases count <;> rfl

theorem active (control : Controller old instructions) (count remaining : Nat) (live : remaining ≠ 0) :
    run old instructions control (count+1) remaining state =
      let command := control state
      let observation := observe old instructions state command
      let tail := run old instructions control count (remaining - if observation = some .executed then 1 else 0)
        (after old instructions state command)
      ⟨tail.unserved,tail.state,stages old instructions state command ++ tail.stages,
        (row old instructions state command).submitted ++ tail.submitted,
        command.incoming ++ tail.arrivals,
        (if observation = some .withheld then 1 else 0) + tail.withheld,
        attempt old instructions state command :: tail.attempts⟩ := by
  change (if remaining = 0 then _ else _) = _
  rw [if_neg live]
  rfl

theorem one_block_is_the_original_execution :
    (after old instructions state command).cursor = EventHistory.execute state.cursor (stages old instructions state command) := by
  rw [stages,OriginQueue.execute_append,SilentWindow.execution_is_the_actual_cursor]
  rfl

theorem every_run_is_the_original_execution (control : Controller old instructions) (count remaining : Nat) :
    (run old instructions control count remaining state).state.cursor =
      EventHistory.execute state.cursor (run old instructions control count remaining state).stages := by
  induction count generalizing remaining state with
  | zero => rfl
  | succ count ih =>
    by_cases empty : remaining = 0
    · subst remaining;rw [stopped];rfl
    · rw [active old instructions state control count remaining empty]
      change (run old instructions control count _ _).state.cursor =
        EventHistory.execute state.cursor (stages old instructions state (control state) ++
          (run old instructions control count _ _).stages)
      rw [OriginQueue.execute_append,← one_block_is_the_original_execution,ih]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionSource
