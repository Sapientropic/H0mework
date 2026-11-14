import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.SourceLeaf

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridgeControl

def sourceMoves : List (Move 19) :=
  [.play (1,1), .play (18,18), .play (1,2), .play (18,16),
   .play (1,3), .play (18,14), .play (1,0), .play (0,1),
   .play (2,3), .play (18,12), .play (2,1)]

open Lean

private def emit (value : Json) : IO Unit := do
  IO.println value.compress
  (← IO.getStdout).flush

private def oneStep {frame : Frame 19} (certificate : Certificate .positive (-345) frame) : IO Json := do
  match certificate with
  | .choose _ reply child =>
      let before := BufferedReplay.restore (BufferedReplay.capture frame)
      let some actual := nativeStep? (Law.positionalSuperko 0) before reply.move
        | throw (IO.userError "the source program emitted an illegal original action")
      let expected := BufferedReplay.capture reply.target
      let actual := BufferedReplay.capture actual
      unless actual.signature == expected.signature && actual.toMove == expected.toMove &&
          actual.consecutivePasses == expected.consecutivePasses && actual.status == expected.status &&
          actual.positionHistory == expected.positionHistory do
        throw (IO.userError "the original action lost its actual target/history")
      let childKind := match child with
        | .all _ _ _ => "all"
        | .vitalChambers _ _ _ => "vitalChambers"
        | _ => "other"
      let final := BufferedReplay.restore expected
      let captured := (RegionAction.stones before.visible.board .negative).card -
        (RegionAction.stones final.visible.board .negative).card
      pure (Json.mkObj [("move", toJson (reprStr reply.move)), ("child", toJson childKind),
        ("white_captured", toJson captured)])
  | _ => throw (IO.userError "expected an original choose node")

private def nextReads {frame : Frame 19} (certificate : Certificate .positive (-345) frame)
    (moves : List (Move 19)) (requireLeaf : Bool) : IO (Array Json) := do
  match certificate with
  | .choose _ reply (.all _ _ children) =>
      let expansion := scoringExpansion reply.target
      let mut reads : Array Json := #[]
      for observed in moves do
        match (List.finRange expansion.length).find? (fun port => (expansion.get port).1 == observed) with
        | none => reads := reads.push (Json.mkObj [("white", toJson (reprStr observed)),
            ("originally_legal", toJson false)])
        | some port =>
            let child := children port
            let response ← oneStep child
            let area := match child with
              | .choose _ action (.vitalChambers detected _ _) =>
                  let final := BufferedReplay.restore (BufferedReplay.capture action.target)
                  if decide (VitalChambers.Holds detected.geometry .positive final.visible.board) then
                    some (VitalChambers.points detected.geometry).card else none
              | _ => none
            if requireLeaf then
              unless area.isSome do throw (IO.userError "the bridge did not generate a vital closure")
            if let some value := area then
              unless value ≥ 8 do throw (IO.userError "the closure has insufficient counted area")
            reads := reads.push (Json.mkObj [("white", toJson (reprStr observed)),
              ("originally_legal", toJson true), ("response", response), ("secured_area", toJson area)])
      pure reads
  | _ => throw (IO.userError "a branch did not retain the next original all-node")

def full (invader : Point 19) : IO Unit := do
  let started ← IO.monoMsNow
  let moves := sourceMoves ++ [.play invader]
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 moves
    | throw (IO.userError "original source replay failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  let some certificate := ElevenLeftBridge.certificate? frame
    | throw (IO.userError s!"left-room/bridge/corridor program failed after {repr invader}")
  let first ← oneStep certificate
  emit (Json.mkObj [("stage", toJson ("generated" : String)), ("invader", toJson (reprStr invader)),
    ("first", first), ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
  match certificate with
  | .choose _ reply (.all _ _ children) =>
      let expansion := scoringExpansion reply.target
      let mut controls : Array Json := #[]
      for observed in ([.pass, .play (2,2), .play (3,1)] : List (Move 19)) do
        match (List.finRange expansion.length).find? (fun port => (expansion.get port).1 == observed) with
        | none => pure ()
        | some port =>
            let readings ← nextReads (children port)
              (if observed = .play (3,1) then [.play (0,3), .play (0,4), .pass]
               else [.play (3,1), .play (3,3), .pass])
              (observed != .play (3,1))
            emit (Json.mkObj [("stage", toJson ("next_native_reads" : String)),
              ("first_white", toJson (reprStr observed)), ("reads", Json.arr readings),
              ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
      for port in List.finRange expansion.length do
        let observed := (expansion.get port).1
        let result ← oneStep (children port)
        if observed ∈ ([.play (3,1), .play (3,2), .play (3,3), .play (0,0), .play (0,1), .play (2,2), .pass] : List (Move 19)) then
          controls := controls.push (Json.mkObj [("white", toJson (reprStr observed)), ("response", result)])
        if port.val % 50 = 0 then
          emit (Json.mkObj [("stage", toJson ("ports" : String)), ("checked", toJson (port.val + 1)),
            ("total", toJson expansion.length), ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
      emit (Json.mkObj [("stage", toJson ("complete" : String)), ("invader", toJson (reprStr invader)),
        ("original_white_ports", toJson expansion.length), ("threshold", toJson (-345 : Int)),
        ("controls", Json.arr controls), ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
  | _ => throw (IO.userError "expected choose/all at the original source")

def goal (complete : Bool) : IO Unit := do
  let extra : List (Move 19) := if complete then
    [.play (0,3), .play (3,1), .play (3,0), .play (0,2), .pass, .play (3,2)]
    else [.play (3,0), .play (0,2), .pass, .play (3,2)]
  let moves := sourceMoves ++ extra
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 moves
    | throw (IO.userError "the original bridge source failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  let some geometry := ElevenLeftBridge.geometry? (3,1)
    | throw (IO.userError "the shared bridge geometry failed")
  let freshCandidate := ElevenLeftBridge.candidate? frame (CoalitionBirth.retained frame .positive) (3,1) geometry
  let some certificate := ElevenLeftBridge.miai? frame
    | throw (IO.userError "the original bridge reader rejected the source")
  let kind ← match certificate with
    | .vitalChambers detected _ _ =>
        unless complete && freshCandidate.isNone &&
            (VitalChambers.points detected.geometry).card == 10 do
          throw (IO.userError "the completed-bridge control did not consume the existing ten-area closure")
        pure "vitalChambers"
    | .all _ _ _ =>
        unless !complete && freshCandidate.isSome do
          throw (IO.userError "the floating bridge changed its original miai behavior")
        pure "all"
    | _ => throw (IO.userError "unexpected bridge reader result")
  IO.println ((Json.mkObj [("completed_bridge", toJson complete), ("source_plies", toJson moves.length),
    ("history_length", toJson frame.positionHistory.length), ("original_replay", toJson true),
    ("new_bridge_candidate", toJson freshCandidate.isSome), ("certificate", toJson kind)]).compress)


def installed : IO Unit := do
  let started ← IO.monoMsNow
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19
      (sourceMoves ++ [.play (3,0)])
    | throw (IO.userError "original W30 source replay failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  unless frame.positionHistory.length == 13 do
    throw (IO.userError "the source lost its complete original history")
  if playing : frame.visible.status = .playing then
    let some (.black found) := settle? frame (-346) (.inl playing)
      | throw (IO.userError "production settle? did not consume the original left-bridge source")
    let certificate : Certificate .positive (-345) frame :=
      (by decide : (-346 : Int) + 1 = -345) ▸ found
    let first ← oneStep certificate
    match certificate with
    | .choose _ reply (.all _ _ children) =>
        let expansion := scoringExpansion reply.target
        unless reply.move == .play (0,2) && expansion.length == 348 do
          throw (IO.userError "installed program changed its first original move or opponent inventory")
        let mut responses : Array Json := #[]
        for observed in ([.pass, .play (3,1)] : List (Move 19)) do
          let some port := (List.finRange expansion.length).find?
              (fun port => (expansion.get port).1 == observed)
            | throw (IO.userError "a selected original opponent event is absent")
          let result ← oneStep (children port)
          let expected : Move 19 := if observed == .pass then .play (3,2) else .play (1,4)
          match children port with
          | .choose _ action (.all _ _ _) =>
              unless action.move == expected do
                throw (IO.userError "the installed bridge/corridor routing changed")
          | _ => throw (IO.userError "an installed response lost its original continuation")
          responses := responses.push (Json.mkObj [
            ("white", toJson (reprStr observed)), ("response", result)])
        emit (Json.mkObj [("stage", toJson ("installed" : String)),
          ("source_plies", toJson (12 : Nat)), ("history_length", toJson frame.positionHistory.length),
          ("first", first), ("original_white_ports", toJson expansion.length),
          ("checked_first_ports", toJson (2 : Nat)), ("responses", Json.arr responses),
          ("guaranteed_margin", toJson (-345 : Int)),
          ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
    | _ => throw (IO.userError "production settle? did not emit the original choose/all program")
    unless (SourceLeaf.elevenLeftBridgeAnswer? frame (-345)).isNone &&
        (SourceLeaf.elevenLeftBridgeAnswer? frame 0).isNone do
      throw (IO.userError "the fixed -345 producer accepted an unsupported stronger threshold")
    let some missingReplay := BufferedReplay.generate? (Law.positionalSuperko 0) 19
        (sourceMoves.take 10)
      | throw (IO.userError "missing-core original replay failed")
    let missing := BufferedReplay.restore (BufferedReplay.capture missingReplay.final)
    unless (SourceLeaf.elevenLeftBridgeAnswer? missing (-346)).isNone &&
        (SourceLeaf.elevenLeftBridgeAnswer? (Frame.initial 9) (-346)).isNone &&
        (settle? (Frame.initial 19) (-346) (.inl rfl)).isNone &&
        (settle? (Frame.initial 19) 0 (.inl rfl)).isNone do
      throw (IO.userError "missing-core, size, or original initial-board guard failed")
    emit (Json.mkObj [("stage", toJson ("guards" : String)),
      ("stronger_thresholds_rejected", toJson true), ("missing_core_rejected", toJson true),
      ("other_size_rejected", toJson true), ("original_initial_rejected", toJson true),
      ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
    let some (.black relaxed) := SourceLeaf.elevenLeftBridgeAnswer? frame (-347)
      | throw (IO.userError "explicit weaker threshold did not retain the generated source program")
    match relaxed with
    | .choose _ reply (.all _ _ _) =>
        unless reply.move == .play (0,2) do
          throw (IO.userError "weakening changed the generated original first move")
    | _ => throw (IO.userError "explicit weaker threshold lost its choose/all program")
    emit (Json.mkObj [("stage", toJson ("relaxed_override" : String)),
      ("threshold", toJson (-347 : Int)), ("certificate", toJson ("choose/all" : String)),
      ("elapsed_ms", toJson ((← IO.monoMsNow) - started))])
  else throw (IO.userError "the original source is not playing")

end SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridgeControl

def main (args : List String) : IO Unit := do
  let run := SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridgeControl.full
  match args with
  | [] | ["--installed"] =>
      SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridgeControl.installed
  | ["--goal"] =>
      SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridgeControl.goal true
      SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridgeControl.goal false
  | ["--full", "00"] => run (0,0)
  | ["--full", "03"] => run (0,3)
  | ["--full", "20"] => run (2,0)
  | ["--full", "22"] => run (2,2)
  | ["--full", "30"] => run (3,0)
  | _ => throw (IO.userError "usage: RunElevenLeftBridge19.lean [--installed | --goal | --full 00/03/20/22/30]")
