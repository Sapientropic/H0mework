import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.SourceLeaf

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSourceControl

def moves : List (Move 19) :=
  [.play (1,1), .play (18,18), .play (1,2), .play (18,16),
   .play (1,3), .play (18,14), .play (1,0), .play (0,1),
   .play (2,3), .play (18,12), .play (2,1), .play (18,10), .play (3,1)]

inductive Mode where
  | focused
  | all
  | installed

def Mode.events : Mode → List (Move 19)
  | .focused => [.play (3,0), .play (0,0), .play (0,3), .play (2,0)]
  | .all => [.play (3,0), .play (0,0), .play (0,2), .play (0,3), .play (2,0),
      .play (2,2), .play (3,2), .pass, .play (18,6)]
  | .installed => [.play (2,0), .play (3,0)]

def Mode.label : Mode → String
  | .focused => "focused: 4 representative first events and 8 nested responses"
  | .all => "all: all 9 representative first events and 18 nested responses"
  | .installed => "installed: production settle?, W20 capture and W30 extension, 4 nested responses"

def sameFrame (left right : Frame 19) : Bool :=
  let left := BufferedReplay.capture left
  let right := BufferedReplay.capture right
  left.signature == right.signature && left.toMove == right.toMove &&
    left.consecutivePasses == right.consecutivePasses && left.status == right.status &&
    left.positionHistory == right.positionHistory

def checkLeaf {frame : Frame 19} (certificate : Certificate .positive (-341) frame) :
    IO (Move 19) := do
  match certificate with
  | .choose _ reply (.vitalChambers detected _ _) =>
      let before := BufferedReplay.restore (BufferedReplay.capture frame)
      let some actual := nativeStep? (Law.positionalSuperko 0) before reply.move
        | throw (IO.userError "nested original Black reply rejected")
      unless sameFrame actual reply.target &&
          decide (VitalChambers.Holds detected.geometry .positive reply.target.visible.board) &&
          acceptsMargin .positive (-341) (VitalChambers.bound detected.geometry .positive) &&
          10 ≤ (VitalChambers.points detected.geometry).card do
        throw (IO.userError "nested reply lost original state/history, Holds, or ten-area guarantee")
      return reply.move
  | _ => throw (IO.userError "nested response lost choose/vitalChambers")

def checkFirst {frame : Frame 19} (observed : Move 19)
    (certificate : Certificate .positive (-341) frame) : IO Unit := do
  match certificate with
  | .choose _ reply (.all _ _ nested) =>
      let before := BufferedReplay.restore (BufferedReplay.capture frame)
      let some actual := nativeStep? (Law.positionalSuperko 0) before reply.move
        | throw (IO.userError "first original Black reply rejected")
      let expected : Move 19 := if observed == .play (3,0) then .play (3,2) else .play (3,0)
      unless reply.move == expected && sameFrame actual reply.target do
        throw (IO.userError "first native response or complete target/history changed")
      if observed == .play (2,0) then
        unless before.visible.board (2,0) == some .negative &&
            reply.target.visible.board (2,0) == none do
          throw (IO.userError "actual B30 did not capture the original W20 stone")
      let expansion := scoringExpansion reply.target
      let ports := List.finRange expansion.length
      let some passPort := ports.find? (fun p => (expansion.get p).1 == .pass)
        | throw (IO.userError "nested original pass is missing")
      let first ← checkLeaf (frame := (expansion.get passPort).2) (nested passPort)
      let some hitPort := ports.find? (fun p => (expansion.get p).1 == first)
        | throw (IO.userError "the first generated completion has no original challenge port")
      let second ← checkLeaf (frame := (expansion.get hitPort).2) (nested hitPort)
      unless first != second do
        throw (IO.userError "challenging the first completion did not select its distinct miai")
      IO.println s!"{repr observed} -> {repr reply.move}; miai {repr first}/{repr second}; original steps/history/Holds/area passed"
      (← IO.getStdout).flush
  | _ => throw (IO.userError "source response lost choose/all")

def checkCertificate {frame : Frame 19} (certificate : Certificate .positive (-341) frame)
    (events : List (Move 19)) : IO Unit := do
  match certificate with
  | .all _ _ children =>
      let expansion := scoringExpansion frame
      unless expansion.length == 349 do
        throw (IO.userError "the source no longer retains 349 original opponent ports")
      for move in events do
        let some port := (List.finRange expansion.length).find? (fun p => (expansion.get p).1 == move)
          | throw (IO.userError "an original representative first event is missing")
        let observed := expansion.get port
        let some actual := nativeStep? (Law.positionalSuperko 0) frame observed.1
          | throw (IO.userError "retained original opponent event was rejected")
        unless sameFrame actual observed.2 do
          throw (IO.userError "opponent event lost the complete original target/history")
        checkFirst (frame := observed.2) observed.1 (children port)
  | _ => throw (IO.userError "source certificate lost its original all constructor")

def run (mode : Mode) : IO Unit := do
  let started ← IO.monoMsNow
  IO.println mode.label
  (← IO.getStdout).flush
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 moves
    | throw (IO.userError "the original thirteen-ply source replay failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  unless frame.positionHistory.length == 14 do
    throw (IO.userError "the original thirteen-ply source lost its full history")
  if source : HookSource.Source frame then
    let certificate ← match mode with
      | .installed =>
          match settle? frame (-342) (.inl source.playing) with
          | some (.black certificate) => pure certificate
          | _ => throw (IO.userError "production settle? did not consume HookSource at threshold -342")
      | .focused | .all =>
          match HookSource.certificate? source with
          | some certificate => pure certificate
          | none => throw (IO.userError "the fixed HookSource geometries did not compile")
    IO.println s!"original 13-ply Black S >= -341 certificate emitted; {(← IO.monoMsNow)-started} ms"
    (← IO.getStdout).flush
    checkCertificate certificate mode.events
    match mode with
    | .installed =>
        unless (settle? frame 0 (.inl source.playing)).isNone &&
            (settle? (Frame.initial 19) (-342) (.inl rfl)).isNone &&
            (settle? (Frame.initial 19) 0 (.inl rfl)).isNone do
          throw (IO.userError "production threshold 0 or initial-board negative was accepted")
        IO.println "production threshold 0 and initial-board (-342, 0) negatives passed"
    | .focused | .all => pure ()
    IO.println s!"349 original ports retained; checked {mode.events.length} representative first events and {2 * mode.events.length} nested responses; {(← IO.monoMsNow)-started} ms"
  else throw (IO.userError "the original thirteen-ply replay does not satisfy HookSource.Source")

end SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSourceControl

def main (args : List String) : IO Unit := do
  let mode ← match args with
    | [] => pure SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSourceControl.Mode.focused
    | ["--all"] => pure .all
    | ["--installed"] => pure .installed
    | _ => throw (IO.userError "usage: RunHookSource19.lean [--all | --installed]; --all checks all 9 representatives, not all 349 ports")
  SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSourceControl.run mode
