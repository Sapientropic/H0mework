import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedSource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveProductionInletSource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
abbrev Active := LiveProductionInletSource.code old instructions
abbrev State := LiveProductionInletSource.State old instructions
abbrev Word := RawEvent Party Good Port (Mandate.State Party Technology) Instrument

def strip (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) :=
  {current with clock := 0,round := 0}
def ClockFree : Prop := ∀ current instruction, instruction ∈ instructions →
  (old.law.Valid current instruction ↔ old.law.Valid (strip current) instruction)

def delay (state : State old instructions) : Nat :=
  if Distributed.Recall.Information.Agency.ownerAt (Active old instructions) state.cursor.ownerStart
    (EventStep.seed state.cursor).history.length = none then 0 else 1
abbrev prepared (state : State old instructions) := SilentWindow.cursorAt state.cursor (delay old instructions state)
def queued (state : State old instructions) (incoming : Word (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : State old instructions :=
  ⟨prepared old instructions state,state.pending ++ incoming⟩
abbrev command : LiveProductionInletSource.Command old instructions := ⟨SilentWindow.quiet,true,[]⟩
abbrev after (state : State old instructions) (incoming : Word (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :=
  LiveProductionInletSource.step old instructions (queued old instructions state incoming) (command old instructions)
def stages (state : State old instructions) (incoming : Word (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : List (EventHistory.Stage (code := Active old instructions)) :=
  SilentWindow.stages (delay old instructions state) ++
    [LiveProductionInletSource.stage old instructions (queued old instructions state incoming) (command old instructions)]
def submitted (state : State old instructions) (incoming : Word (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Word (Party := Party) (Good := Good)
      (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  (StageTrace.material (queued old instructions state incoming).cursor
    (command old instructions).protocol (LiveProductionInletSource.stage old instructions
      (queued old instructions state incoming) (command old instructions)).2).submitted

abbrev Incoming := State old instructions → Word (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
structure Result where
  state : State old instructions
  stages : List (EventHistory.Stage (code := Active old instructions))
  submitted : Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
-- Only the next source state is queried for new proposals; no future outcome table is stored.
def run (incoming : Incoming old instructions) : Nat → State old instructions → Result old instructions :=
  Nat.rec (fun state => ⟨state,[],[]⟩) fun _ previous state =>
    let arrival := incoming state
    let tail := previous (after old instructions state arrival)
    ⟨tail.state,stages old instructions state arrival ++ tail.stages,
      submitted old instructions state arrival ++ tail.submitted⟩

def ready (state : State old instructions) : Bool :=
  decide (state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length ∧
    2 * state.pending.length ≤ (EventStep.seed state.cursor).remaining ∧
    (∀ instruction ∈ state.pending,instruction ∈ instructions) ∧
    (∀ item ∈ old.law.rawItems (strip (EventStep.seed state.cursor).current) state.pending,
      old.law.Valid item.before item.request))

theorem one_block_is_the_original_execution (state : State old instructions) (incoming : Word
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    (after old instructions state incoming).cursor = EventHistory.execute state.cursor (stages old instructions state incoming) := by
  rw [stages,OriginQueue.execute_append,SilentWindow.execution_is_the_actual_cursor]
  rfl

theorem every_run_is_the_original_execution (incoming : Incoming old instructions) (count : Nat)
    (state : State old instructions) :
    (run old instructions incoming count state).state.cursor =
      EventHistory.execute state.cursor (run old instructions incoming count state).stages := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    change (run old instructions incoming count (after old instructions state (incoming state))).state.cursor =
      EventHistory.execute state.cursor (stages old instructions state (incoming state) ++
        (run old instructions incoming count (after old instructions state (incoming state))).stages)
    rw [OriginQueue.execute_append,← one_block_is_the_original_execution,ih]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedSource
