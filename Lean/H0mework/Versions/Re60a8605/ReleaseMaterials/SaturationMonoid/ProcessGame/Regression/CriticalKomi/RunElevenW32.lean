import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenW32

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.Regression.RunElevenW32

open ElevenW32

def sourceMoves : List (Move 19) :=
  [.play (1,1), .play (18,18), .play (1,2), .play (18,16),
   .play (1,3), .play (18,14), .play (1,0), .play (0,1),
   .play (2,3), .play (18,12), .play (2,1), .play (3,2)]

private def sameFrame (left right : Frame 19) : Bool :=
  let left := BufferedReplay.capture left
  let right := BufferedReplay.capture right
  left.signature == right.signature && left.toMove == right.toMove &&
    left.consecutivePasses == right.consecutivePasses && left.status == right.status &&
    left.positionHistory == right.positionHistory

private def checkStep {frame : Frame 19} (certificate : Certificate .positive (-345) frame) : IO (Move 19) := do
  match certificate with
  | .choose _ reply _ =>
      let before := BufferedReplay.restore (BufferedReplay.capture frame)
      let some actual := nativeStep? (Law.positionalSuperko 0) before reply.move
        | throw (IO.userError "generated Black response is not originally legal")
      unless sameFrame actual reply.target do
        throw (IO.userError "generated response changed the full original frame/history")
      pure reply.move
  | _ => throw (IO.userError "expected an actual Black choose node")

def run (allPorts : Bool := true) : IO Unit := do
  let started ← IO.monoMsNow
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 sourceMoves
    | throw (IO.userError "original twelve-ply W32 source replay failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  unless frame.positionHistory.length == 13 do
    throw (IO.userError "original source lost retained history")
  IO.println "original twelve-ply W32 source replay retained; compiling vertical source program"
  (← IO.getStdout).flush
  let some certificate := certificate? frame
    | throw (IO.userError "W32 source program has an unresolved original port")
  let first ← checkStep certificate
  IO.println s!"original Certificate positive (-345) emitted; first {repr first}; {(← IO.monoMsNow)-started} ms"
  (← IO.getStdout).flush
  match certificate with
  | .choose _ reply (.all _ _ children) =>
      let expansion := scoringExpansion reply.target
      let ports := if allPorts then List.finRange expansion.length
        else (List.finRange expansion.length).filter (fun port =>
          (expansion.get port).1 ∈ ([.play (0,0), .play (0,2), .play (0,3), .play (2,0),
            .play (3,0), .play (4,1), .pass] : List (Move 19)))
      for port in ports do
        let observed := (expansion.get port).1
        let some actual := nativeStep? (Law.positionalSuperko 0) reply.target observed
          | throw (IO.userError "retained original White event was rejected")
        unless sameFrame actual (expansion.get port).2 do
          throw (IO.userError "retained White event changed original frame/history")
        let response ← checkStep (children port)
        if observed ∈ ([.play (0,0), .play (0,2), .play (0,3), .play (2,0), .play (3,0),
            .play (4,1), .pass] : List (Move 19)) then
          IO.println s!"{repr observed} -> {repr response}; original history retained"
          (← IO.getStdout).flush
      IO.println s!"checked {ports.length} of {expansion.length} original first White ports and Black responses; {(← IO.monoMsNow)-started} ms"
  | _ => throw (IO.userError "W32 certificate lost its original choose/all constructors")


/-- Replay the actual sequence of contested seals to the physical bottom edge.
This focused reader does not reconstruct the root's complete predecessor. -/
def bottomControl : IO Unit := do
  let started ← IO.monoMsNow
  let extension := (List.range 15).flatMap (fun k =>
    [Move.play (Corridor.point (k+3) 0), Move.play (Corridor.point (k+4) 1)])
  let moves := sourceMoves ++ [.play (3,1)] ++ extension
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 moves
    | throw (IO.userError "original bottom-edge path rejected")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  let some certificate := miai? 18 frame
    | throw (IO.userError "actual bottom-edge miai rejected")
  IO.println s!"original {moves.length} plies / history {frame.positionHistory.length}: row18 miai generated"
  (← IO.getStdout).flush
  match certificate with
  | .all _ _ children =>
      let expansion := scoringExpansion frame
      for observed in ([.pass, .play (0,2), .play (18,0)] : List (Move 19)) do
        let some port := (List.finRange expansion.length).find? (fun p => (expansion.get p).1 == observed)
          | throw (IO.userError "original bottom test port missing")
        match children port with
        | .choose _ reply (.vitalChambers detected _ _) =>
            let some actual := nativeStep? (Law.positionalSuperko 0) (expansion.get port).2 reply.move
              | throw (IO.userError "bottom miai emitted an illegal original Black response")
            unless sameFrame actual reply.target &&
                decide (VitalChambers.Holds detected.geometry .positive reply.target.visible.board) &&
                (VitalChambers.points detected.geometry).card ≥ 8 do
              throw (IO.userError "bottom miai lost original history/Holds/area")
            IO.println s!"{repr observed} -> {repr reply.move}; native/history/Holds; area {(VitalChambers.points detected.geometry).card}"
            (← IO.getStdout).flush
        | _ => throw (IO.userError "bottom miai lost its original choose/vital form")
      IO.println s!"bottom original ports {expansion.length}; focused runtime {(← IO.monoMsNow)-started} ms"
  | _ => throw (IO.userError "bottom source lost its original all")


end SaturationMonoid.ProcessGame.Go.CriticalKomi.Regression.RunElevenW32

def main (args : List String) : IO Unit := do
  match args with
  | [] => SaturationMonoid.ProcessGame.Go.CriticalKomi.Regression.RunElevenW32.run true
  | ["--generated"] => SaturationMonoid.ProcessGame.Go.CriticalKomi.Regression.RunElevenW32.run false
  | ["--bottom"] => SaturationMonoid.ProcessGame.Go.CriticalKomi.Regression.RunElevenW32.bottomControl
  | _ => throw (IO.userError "usage: ElevenW32Control.lean [--generated | --bottom]")
