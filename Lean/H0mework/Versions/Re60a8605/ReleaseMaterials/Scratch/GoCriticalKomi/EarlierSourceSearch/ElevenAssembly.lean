import H0mework.Versions.Re60a8605.ReleaseMaterials.Scratch.GoCriticalKomi.EarlierSourceSearch.ElevenOuter
import H0mework.Versions.Re60a8605.ReleaseMaterials.Scratch.GoCriticalKomi.EarlierSourceSearch.Extracted
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridge
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenW02
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenW32
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgramCache
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.CriticalKomi.RegionalDAGLoader

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.EarlierSourceSearch.ElevenAssembly

open Lean

abbrev Row (frame : Frame 19) :=
  (port : Fin (scoringExpansion frame).length) ×
    Certificate .positive (-345) ((scoringExpansion frame).get port).2

def read? {frame : Frame 19} (rows : Array (Row frame))
    (port : Fin (scoringExpansion frame).length) :
    Option (Certificate .positive (-345) ((scoringExpansion frame).get port).2) :=
  rows.findSome? (fun ⟨stored, certificate⟩ =>
    if same : stored = port then some (same ▸ certificate) else none)

private def collect? : (count : Nat) → (family : Fin count → Type) →
    ((port : Fin count) → Option (family port)) → Option ((port : Fin count) → family port)
  | 0, _, _ => some (fun port => Fin.elim0 port)
  | count + 1, family, read => do
      let first ← read 0
      let rest ← collect? count (fun port => family port.succ) (fun port => read port.succ)
      pure (fun port => match port with
        | ⟨0, _⟩ => first
        | ⟨later + 1, bound⟩ => rest ⟨later, Nat.lt_of_succ_lt_succ bound⟩)

def finish? {frame : Frame 19} (rows : Array (Row frame)) :
    Option (Certificate .positive (-345) frame) :=
  if playing : frame.visible.status = .playing then
    if opponent : frame.visible.toMove ≠ .positive then
      (collect? (scoringExpansion frame).length
        (fun port => Certificate .positive (-345) ((scoringExpansion frame).get port).2)
        (read? rows)).map (Certificate.all playing opponent)
    else none
  else none

def current? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  Eleven.after31? frame <|> ElevenLeftBridge.recognize? frame

/-- The observed original event selects an already compiled source program.
Every returned child is still indexed by the complete actual successor frame. -/
def child? (regional : RegionalDAGCache.Provider RegionalDAGLoader.region)
    (observed : Move 19) (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  if observed = .play (0,2) then ElevenW02.certificate? frame
  else if observed = .play (3,1) then regional.at? frame
  else if observed = .play (3,2) then ElevenW32.certificate? frame
  else current? frame

private def validate {frame : Frame 19} (certificate : Certificate .positive (-345) frame) : Bool :=
  match certificate with
  | .choose _ reply (.all _ _ _) =>
      let material := BufferedReplay.restore (BufferedReplay.capture frame)
      nativeStep? (Law.positionalSuperko 0) material reply.move == some reply.target
  | _ => false

private def emit (value : Json) : IO Unit := do
  IO.println value.compress
  (← IO.getStdout).flush

def assemble (regional : RegionalDAGCache.Provider RegionalDAGLoader.region) (frame : Frame 19) :
    IO (Option (Certificate .positive (-345) frame)) := do
  let started ← IO.monoMsNow
  let expansion := scoringExpansion frame
  let mut rows : Array (Row frame) := #[]
  let mut pending : Array String := #[]
  for port in List.finRange expansion.length do
    let observed := expansion.get port
    match child? regional observed.1 observed.2 with
    | none => pending := pending.push (reprStr observed.1)
    | some certificate =>
        unless validate certificate do throw (IO.userError "a retained child lost its original action/history")
        rows := rows.push ⟨port, certificate⟩
    if port.val % 25 == 0 then
      emit (Json.mkObj [("stage", toJson ("assembling" : String)),
        ("checked", toJson (port.val + 1)), ("original_ports", toJson expansion.length),
        ("retained_children", toJson rows.size),
        ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
  let complete := finish? rows
  unless complete.isSome == pending.isEmpty do
    throw (IO.userError "dependent all assembly disagrees with the actual pending rows")
  emit (Json.mkObj [("stage", toJson ("assembled_current_producers" : String)),
    ("source_plies", toJson (11 : Nat)), ("history_length", toJson frame.positionHistory.length),
    ("original_white_ports", toJson expansion.length), ("retained_children", toJson rows.size),
    ("outstanding_source_ports", toJson pending), ("complete_certificate", toJson complete.isSome),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
  pure complete

/-- The checked source package remains in this continuation while the complete
eleven-ply certificate is immediately consumed by its actual earlier Black step. -/
def run (regional : RegionalDAGCache.Provider RegionalDAGLoader.region) : IO Unit := do
  let some source := Extracted.cases.find? (fun entry => entry.name == "hook")
    | throw (IO.userError "the retained actual source is absent")
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 (source.moves.take 11)
    | throw (IO.userError "the original eleven-ply replay failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  unless (scoringExpansion frame).length == 351 && frame.positionHistory.length == 12 do
    throw (IO.userError "the original source or opponent inventory changed")
  let some certificate ← assemble regional frame
    | throw (IO.userError "the original eleven-ply source still has a pending White port")
  let some prior := BufferedReplay.generate? (Law.positionalSuperko 0) 19 (source.moves.take 10)
    | throw (IO.userError "the actual ten-ply source failed")
  let before := BufferedReplay.restore (BufferedReplay.capture prior.final)
  let some predecessor := Corridor.choose? before (2,1) (fun target =>
      if same : frame = target then some (same ▸ certificate) else none)
    | throw (IO.userError "the generated all did not feed its exact original Black predecessor")
  unless validate predecessor do
    throw (IO.userError "the original predecessor lost its Black step or full history")
  emit (Json.mkObj [("stage", toJson ("actual_predecessor" : String)),
    ("source_plies", toJson (10 : Nat)), ("history_length", toJson before.positionHistory.length),
    ("black_reply", toJson (reprStr (Move.play (2,1) : Move 19))),
    ("complete_certificate", toJson true)])

def loadProgram (file : String) : IO (RegionalDAGCache.Provider RegionalDAGLoader.region) := do
  let loaded ← RegionalDAGLoader.load file
  unless loaded.complete do throw (IO.userError "the raw program stream is incomplete")
  let some connected := ExteriorSource.recognize? RegionalDAGLoader.region
    | throw (IO.userError "the original exterior is not connected")
  let checked ← RegionalDAGCache.compile RegionalDAGLoader.region connected loaded.nodes loaded.root
  emit (Json.mkObj [("stage", toJson ("original_program_checked" : String)),
    ("raw_nodes", toJson loaded.nodes.size), ("statistics", toJson (reprStr checked.stats))])
  pure (RegionalDAGCache.provider checked.compiled)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.EarlierSourceSearch.ElevenAssembly

def main (args : List String) : IO Unit := do
  let file := args[0]?.getD
    "scratch/GoCriticalKomi/EarlierSourceSearch/.cache/retained-w31-y2oi1paf/strategy_dag.json.gz"
  let program ← SaturationMonoid.ProcessGame.Go.CriticalKomi.EarlierSourceSearch.ElevenAssembly.loadProgram file
  SaturationMonoid.ProcessGame.Go.CriticalKomi.EarlierSourceSearch.ElevenAssembly.run program
