import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawTerminalPeaceInstance
import Lean.Data.Json

set_option autoImplicit false

open Lean
open SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

private def addressJson (address : Nat × Nat × SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Key Bool Bool) : Json :=
  let (birth, item, victim, payer, good) := address
  Json.mkObj [("birth", toJson birth), ("item", toJson item), ("victim", toJson victim),
    ("payer", toJson payer), ("good", toJson good)]

private def record (cursor : Nat) (kind : String) (clock remaining : ℚ) : Json :=
  Json.mkObj [("source", toJson ("terminal-peace/original-six" : String)), ("cursor", toJson cursor),
    ("kind", toJson kind), ("clock", toJson (toString clock)),
    ("address", addressJson Stage.address), ("remaining", toJson (toString remaining))]

private def readStage (cursor : Nat) (stage : Stage) : Json :=
  let observed := publicRead stage
  record cursor stage.label observed.clock observed.remaining

private def readLive (cursor : Nat) (position : Ingress.Position) : Json :=
  record cursor position.label position.clock position.remaining

private def failure (reason : String) (cursor : Nat) : Json :=
  Json.mkObj [("error", toJson reason), ("cursor", toJson cursor)]

private inductive WireCommand
  | advance
  | submit (input : Ingress.Input)

private inductive Request
  | inspect
  | change (cursor : Nat) (command : WireCommand)

private def request (line : String) : Except String Request := do
  let json ← Json.parse line
  let obj ← json.getObj?
  let op ← (← json.getObjVal? "op").getStr?
  match op with
  | "inspect" =>
    if obj.size = 1 then pure .inspect else throw "unexpected field"
  | "advance" =>
    if obj.size = 2 then
      pure (.change (← (← json.getObjVal? "cursor").getNat?) .advance)
    else throw "unexpected field"
  | "submit" =>
    if obj.size = 3 then
      let event ← (← json.getObjVal? "event").getStr?
      match Ingress.Input.parse event with
      | none => throw "unregistered source input"
      | some input => pure (.change (← (← json.getObjVal? "cursor").getNat?) (.submit input))
    else throw "unexpected field"
  | _ => throw "unknown operation"

private partial def serve {Position : Type} (read : Nat → Position → Json)
    (activate : Position → WireCommand → Option Position)
    (input : IO.FS.Stream) (output : IO.FS.Stream) (cursor : Nat) (position : Position) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  let (reply, cursor', position') :=
    match request line with
    | .error _ => (failure "invalid-request" cursor, cursor, position)
    | .ok .inspect => (read cursor position, cursor, position)
    | .ok (.change expected command) =>
      if expected = cursor then
        match activate position command with
        | some next => (read (cursor + 1) next, cursor + 1, next)
        | none => (failure "inadmissible-event" cursor, cursor, position)
      else (failure "stale-cursor" cursor, cursor, position)
  output.putStrLn reply.compress
  output.flush
  serve read activate input output cursor' position'

private def stageNext (stage : Stage) : WireCommand → Option Stage
  | .advance => some stage.next
  | .submit _ => none

private def liveNext (position : Ingress.Position) : WireCommand → Option Ingress.Position
  | .advance => none
  | .submit event => Ingress.consume position event

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--worker"] =>
    serve readStage stageNext (← IO.getStdin) (← IO.getStdout) 0 .source
    return 0
  | ["--live"] =>
    serve readLive liveNext (← IO.getStdin) (← IO.getStdout) 0 Ingress.start
    return 0
  | ["--fuel", literal] =>
    if let some fuel := literal.toNat? then
      if fuel ≤ 1000 then
        for (cursor, stage) in (readPrefix fuel).zipIdx.map (fun (stage, cursor) => (cursor, stage)) do
          IO.println (readStage cursor stage).compress
        return 0
    IO.eprintln "fuel must be a natural number at most 1000"
    return 2
  | _ =>
    IO.eprintln "usage: terminal-peace --fuel N | --worker | --live"
    return 2
