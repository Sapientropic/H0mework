import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.MaterializedStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.MaterializedStep

private def sameFrame (left right : Frame 19) : Bool :=
  let left := BufferedReplay.capture left
  let right := BufferedReplay.capture right
  left.signature == right.signature && left.toMove == right.toMove &&
    left.consecutivePasses == right.consecutivePasses && left.status == right.status &&
    left.positionHistory == right.positionHistory

def run : IO Unit := do
  let word : List (Move 19) := [.play (1,1), .play (18,18), .play (1,2), .play (18,16),
    .play (1,3), .play (18,14), .play (1,0), .play (0,1),
    .play (2,3), .play (18,12), .play (2,1), .play (0,2)] ++ [.play (3,1)]
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 word
    | throw (IO.userError "the original thirteen-ply replay failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  let sourceRef ← IO.mkRef frame
  let outputRef ← IO.mkRef ([] : List (Move 19 × Frame 19))
  let start ← IO.monoNanosNow
  let current ← sourceRef.get
  outputRef.set (scoringExpansion current)
  let originalNanos := (← IO.monoNanosNow) - start
  let original ← outputRef.get
  let originalCount := original.length
  IO.println s!"original ports={originalCount} nanos={originalNanos}"
  (← IO.getStdout).flush
  let start ← IO.monoNanosNow
  let current ← sourceRef.get
  outputRef.set (scoring current)
  let materialNanos := (← IO.monoNanosNow) - start
  let material ← outputRef.get
  let materialCount := material.length
  IO.println s!"materialized ports={materialCount} nanos={materialNanos}"
  (← IO.getStdout).flush
  unless originalCount == 349 && originalCount == materialCount do
    throw (IO.userError "the complete original port count changed")
  for ((move, target), (otherMove, otherTarget)) in original.zip material do
    unless move == otherMove && sameFrame target otherTarget do
      throw (IO.userError "materialization changed an original event or its full frame/history")
  let played : Move 19 := .play (0,3)
  let some target := step? (Law.positionalSuperko 0) frame played
    | throw (IO.userError "the chosen original control move is not legal")
  let repeated : Frame 19 := {frame with positionHistory := frame.positionHistory ++ [target.visible.situation]}
  unless (step? (Law.positionalSuperko 0) repeated played).isNone do
    throw (IO.userError "actual positional repetition was admitted")
  unless (step? (Law.positionalSuperko 0) repeated .pass).isSome do
    throw (IO.userError "original pass exemption was lost")
  IO.println "all 349 original events, full targets/history, PSK rejection and pass exemption passed"

end SaturationMonoid.ProcessGame.Go.CriticalKomi.MaterializedStep

def main : IO Unit := SaturationMonoid.ProcessGame.Go.CriticalKomi.MaterializedStep.run
