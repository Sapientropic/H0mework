import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenW02

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.Regression.RunElevenW02

open Lean

private def emit (value : Json) : IO Unit := do
  IO.println value.compress
  (← IO.getStdout).flush

private def inspect {frame : Frame 19} (certificate : Certificate .positive (-345) frame) : IO (Move 19) := do
  match certificate with
  | .choose _ reply _ =>
      let material := BufferedReplay.restore (BufferedReplay.capture frame)
      let some actual := nativeStep? (Law.positionalSuperko 0) material reply.move
        | throw (IO.userError "a W02 source reply is not original-legal")
      unless actual == reply.target do throw (IO.userError "a W02 source reply lost its full original target/history")
      pure reply.move
  | _ => throw (IO.userError "expected an original W02 source choice")

def run (allPorts : Bool := true) : IO Unit := do
  let started ← IO.monoMsNow
  let moves : List (Move 19) := [.play (1,1), .play (18,18), .play (1,2), .play (18,16),
    .play (1,3), .play (18,14), .play (1,0), .play (0,1),
    .play (2,3), .play (18,12), .play (2,1), .play (0,2)]
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 moves
    | throw (IO.userError "the actual W02 twelve-ply source failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  emit (Json.mkObj [("stage", toJson ("source" : String)), ("plies", toJson moves.length),
    ("history_length", toJson frame.positionHistory.length)])
  let some certificate := ElevenW02.certificate? frame
    | throw (IO.userError "the W02 source program has an unresolved original branch")
  let first ← inspect certificate
  emit (Json.mkObj [("stage", toJson ("generated" : String)),
    ("first_black", toJson (reprStr first)), ("elapsed_ms", toJson ((← IO.monoMsNow)-started))])
  match certificate with
  | .choose _ reply (.all _ _ children) =>
      let expansion := scoringExpansion reply.target
      let mut checked := 0
      let mut controls : Array Json := #[]
      let selected := if allPorts then List.finRange expansion.length
        else (List.finRange expansion.length).filter (fun port =>
          (expansion.get port).1 ∈ ([.play (0,0), .play (0,3), .play (3,0), .play (3,2),
            .play (1,4), .play (2,0), .play (2,2), .pass] : List (Move 19)))
      for port in selected do
        let observed := (expansion.get port).1
        let some actual := nativeStep? (Law.positionalSuperko 0) reply.target observed
          | throw (IO.userError "a retained W02 White event is not originally legal")
        unless actual == (expansion.get port).2 do
          throw (IO.userError "a retained W02 White event lost its complete frame/history")
        let response ← inspect (frame := (expansion.get port).2) (children port)
        checked := checked + 1
        if observed ∈ ([.play (0,0), .play (0,3), .play (3,0), .play (3,2),
            .play (1,4), .play (2,0), .play (2,2), .pass] : List (Move 19)) then
          controls := controls.push (Json.mkObj [("white", toJson (reprStr observed)),
            ("black", toJson (reprStr response))])
        if checked % 50 == 0 then
          emit (Json.mkObj [("stage", toJson ("ports" : String)),
            ("checked", toJson checked), ("total", toJson expansion.length),
            ("elapsed_ms", toJson ((← IO.monoMsNow)-started))])
      emit (Json.mkObj [("stage", toJson ("complete" : String)),
        ("original_white_ports", toJson expansion.length), ("inspected_ports", toJson checked),
        ("complete_certificate", toJson true),
        ("controls", Json.arr controls), ("elapsed_ms", toJson ((← IO.monoMsNow)-started))])
  | _ => throw (IO.userError "the W02 program lost the original complete White layer")

end SaturationMonoid.ProcessGame.Go.CriticalKomi.Regression.RunElevenW02

def main (args : List String) : IO Unit :=
  SaturationMonoid.ProcessGame.Go.CriticalKomi.Regression.RunElevenW02.run
    (!args.contains "--generated")
