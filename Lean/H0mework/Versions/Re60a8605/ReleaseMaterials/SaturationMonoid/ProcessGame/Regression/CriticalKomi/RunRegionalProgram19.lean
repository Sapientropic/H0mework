import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram

open RegionProjection RegionAction

attribute [local instance 2000] List.decidableBAll
attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

namespace Control

open Lean

def region : Finset (Point 19) :=
  Finset.univ.filter (fun point => point.1.val < 7 ∧ point.2.val < 7)

def maskPoints (mask : Nat) : Finset (Point 19) :=
  region.filter (fun point => mask.testBit (7 * point.1.val + point.2.val) = true)

@[noinline] def rawBoard (black white : Nat) : Board 19 :=
  let blackPoints := maskPoints black
  let whitePoints := maskPoints white
  fun point => if point ∈ blackPoints then some .positive
    else if point ∈ whitePoints then some .negative else none

def point? (address : Nat) : Option (Point 19) :=
  if row : address / 7 < 19 then
    if column : address % 7 < 19 then some (⟨address / 7, row⟩, ⟨address % 7, column⟩)
    else none
  else none

def moves : List (Move 19) :=
  [.play (1, 1), .play (18, 18), .play (1, 2), .play (18, 16),
   .play (1, 3), .play (18, 14), .play (1, 0), .play (0, 1),
   .play (2, 3), .play (18, 12), .play (2, 1), .play (3, 1)]

def sameFrame (left right : Frame 19) : Bool :=
  let left := BufferedReplay.capture left
  let right := BufferedReplay.capture right
  left.signature == right.signature && left.toMove == right.toMove &&
    left.consecutivePasses == right.consecutivePasses && left.status == right.status &&
    left.positionHistory == right.positionHistory

def natField (value : Json) (key : String) : IO Nat :=
  match value.getObjValAs? Nat key with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

def parseMask (value : Nat) : Except String (Finset (Point 19)) :=
  if value < 2 ^ 49 then pure (maskPoints value) else throw "mask exceeds the 7x7 observation"

def parsePort (value : Nat) : Except String PortCode :=
  if value = 49 then pure .environment
  else if value = 50 then pure .pass
  else if value < 49 then
    match point? value with | some point => pure (.play point) | none => throw "invalid point"
  else throw "invalid regional port"

/-- Only raw states, actions, geometry and references are decoded. The external
claim/result labels are not inputs to the Lean validity judgment. -/
def parseDAG (value : Json) : Except String (Array RawNode × Nat × List Nat) := do
  unless (← value.getObjValAs? String "schema") = "corner-birth-dag/v1" do throw "wrong DAG schema"
  let historyRows ← value.getObjValAs? (Array Json) "history_shapes"
  let histories ← historyRows.foldlM (fun histories row => do
    let id ← row.getObjValAs? Nat "id"
    if histories.contains id then throw "duplicate historical row"
    let masks ← row.getObjValAs? (List Nat) "maxima"
    let points ← masks.mapM parseMask
    pure (histories.insert id points)) ({} : Std.HashMap Nat (List (Finset (Point 19))))
  let rawNodes ← value.getObjValAs? (Array Json) "nodes"
  let nodes ← (List.finRange rawNodes.size).foldlM (fun nodes index => do
    let raw := rawNodes[index]
    unless (← raw.getObjValAs? Nat "id") = index.val do throw "noncanonical raw node index"
    let source ← raw.getObjVal? "state"
    unless (← source.getObjValAs? Nat "mask_stride") = 7 do throw "wrong raw stride"
    let black ← source.getObjValAs? Nat "black"
    let white ← source.getObjValAs? Nat "white"
    let blackPoints ← parseMask black
    let whitePoints ← parseMask white
    unless Disjoint blackPoints whitePoints do throw "overlapping raw colours"
    let historyId ← source.getObjValAs? Nat "history_id"
    let some history := histories[historyId]? | throw "missing historical row"
    let turnText ← source.getObjValAs? String "turn"
    let turn ← if turnText = "black" then pure Polarity.positive
      else if turnText = "white" then pure Polarity.negative else throw "invalid control polarity"
    let remaining ← source.getObjValAs? Nat "remaining"
    let state : Snapshot := ⟨rawBoard black white, history, turn, remaining⟩
    let rawEdges ← raw.getObjValAs? (List Json) "edges"
    let edges ← rawEdges.mapM (fun edge => do
      let port ← parsePort (← edge.getObjValAs? Nat "move")
      pure (port, ← edge.getObjValAs? Nat "to"))
    let reason ← raw.getObjValAs? String "reason"
    let body ← if reason = "source_shared_eye_coalition" then
        if edges.isEmpty then pure RawBody.coalition else throw "coalition leaf has edges"
      else if reason = "source_vital_chambers" then do
        unless edges.isEmpty do throw "vital leaf has edges"
        let geometry ← raw.getObjVal? "vital_chambers"
        let core ← parseMask (← geometry.getObjValAs? Nat "core")
        let rooms ← (← geometry.getObjValAs? (List Nat) "rooms").mapM parseMask
        pure (RawBody.vital core rooms.toFinset)
      else if turn = .positive then
        match edges with
        | [(.play point, child)] => pure (RawBody.own point child)
        | _ => throw "Black row must have one original placement edge"
      else pure (RawBody.white edges)
    pure (nodes.push ⟨state, body⟩)) (#[] : Array RawNode)
  let root ← value.getObjValAs? Nat "root"
  let sourcePath ← value.getObjValAs? (List Json) "source_path"
  let word ← sourcePath.mapM (fun edge => edge.getObjValAs? Nat "move")
  pure (nodes, root, word)

def originalWord (source : List Nat) : Except String (List (Move 19)) := do
  let outside := (allPoints 19).filter (fun point => point.1.val = 18)
  let mut used := 0
  let mut word : List (Move 19) := [.play (1, 1)]
  for address in source do
    let move ← match ← parsePort address with
      | .play point => pure (Move.play point)
      | .pass => pure Move.pass
      | .environment =>
          match outside[used]? with
          | none => throw "source needs more original exterior events"
          | some point => do used := used + 1; pure (.play point)
    word := word ++ [move]
  pure word

def runDAG : IO Unit := do
  let started ← IO.monoMsNow
  let file := "scratch/GoCriticalKomi/EarlierSourceSearch/.cache/w01-wide-core-b12-2-ecraabvz/vital_birth_witness.json.gz"
  let unpacked ← IO.Process.output {cmd := "gzip", args := #["-dc", file]}
  unless unpacked.exitCode = 0 do throw (IO.userError "small retained DAG failed to decompress")
  let .ok json := Json.parse unpacked.stdout | throw (IO.userError "small retained DAG failed to parse")
  let .ok (nodes, root, source) := parseDAG json | throw (IO.userError "raw DAG schema/state decoding failed")
  let some connected := ExteriorSource.recognize? region | throw (IO.userError "exterior connectivity failed")
  let .ok compiled := compileDAG region connected nodes root
    | throw (IO.userError "raw DAG node or edge was not certified")
  IO.println s!"raw DAG compiled: {nodes.size} rows; {(← IO.monoMsNow)-started} ms"
  (← IO.getStdout).flush
  let .ok word := originalWord source | throw (IO.userError "raw source word did not decode")
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 word
    | throw (IO.userError "raw source word failed the original 19x19 compiler")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  let some certificate := compiled.at? frame | throw (IO.userError "compiled DAG rejected its actual original source")
  unless (compiled.at? (Frame.initial 19)).isNone do throw (IO.userError "DAG accepted an unmatched initial source")
  let damaged := nodes.map (fun node => match node.body with
    | .white edges => {node with body := .white edges.dropLast}
    | _ => node)
  unless (compileDAG? region connected damaged root).isNone do throw (IO.userError "missing White coverage was accepted")
  let brokenRank := nodes.map (fun node => {node with state := {node.state with remaining := 0}})
  unless (compileDAG? region connected brokenRank root).isNone do throw (IO.userError "broken rank descent was accepted")
  match certificate with
  | .all _ _ children =>
      let expansion := scoringExpansion frame
      let mut checked := 0
      let mut vital := 0
      let mut coalition := 0
      for port in List.finRange expansion.length do
        let observed := expansion.get port
        let before := BufferedReplay.restore (BufferedReplay.capture observed.2)
        match children port with
        | .choose _ reply leaf =>
            let some actual := nativeStep? (Law.positionalSuperko 0) before reply.move
              | throw (IO.userError "DAG Black reply failed original legality")
            unless sameFrame actual reply.target do throw (IO.userError "DAG Black reply lost full original history")
            match leaf with
            | .vitalChambers detected _ _ =>
                unless decide (VitalChambers.Holds detected.geometry .positive reply.target.visible.board) &&
                    8 ≤ (VitalChambers.points detected.geometry).card do throw (IO.userError "DAG vital leaf failed")
                vital := vital + 1
            | .eyeCoalition detected _ _ =>
                unless decide (EyeCoalition.Holds detected.geometry .positive reply.target.visible.board) &&
                    8 ≤ (EyeCoalition.points detected.geometry).card do throw (IO.userError "DAG coalition leaf failed")
                coalition := coalition + 1
            | _ => throw (IO.userError "small DAG emitted an unexpected continuation")
        | _ => throw (IO.userError "small DAG omitted a Black source response")
        checked := checked + 1
        if checked % 50 == 0 then
          IO.println s!"compiled small DAG: {checked}/{expansion.length} original White ports; {(← IO.monoMsNow)-started} ms"
          (← IO.getStdout).flush
      IO.println s!"compiled {nodes.size}-row DAG -> original {word.length}-ply Certificate positive(-345); {checked} actual White/Black replies, {vital} vital and {coalition} coalition leaves; missing coverage/rank/source negatives rejected; {(← IO.monoMsNow)-started} ms"
  | _ => throw (IO.userError "small DAG did not retain its original full White layer")

def run (historyOnly : Bool) : IO Unit := do
  let started ← IO.monoMsNow
  let .ok lookup := Json.parse (← IO.FS.readFile
      "scratch/GoCriticalKomi/EarlierSourceSearch/results/retained-w31/lookup.json")
    | throw (IO.userError "retained W31 lookup did not parse")
  let .ok state := lookup.getObjVal? "state"
    | throw (IO.userError "retained W31 source state is absent")
  let black ← natField state "black"
  let white ← natField state "white"
  let choice ← natField lookup "choice"
  unless (← natField lookup "source_plies") == 12 &&
      (← natField lookup "new_branch_expansions") == 0 &&
      (← natField state "mask_stride") == 7 && (← natField state "history_id") == 85 &&
      black < 2 ^ 49 && white < 2 ^ 49 && choice < 49 &&
      decide (Disjoint (maskPoints black) (maskPoints white)) do
    throw (IO.userError "retained W31 source metadata changed")
  let some played := point? choice
    | throw (IO.userError "retained Black address is outside the original board")
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 moves
    | throw (IO.userError "original W31 twelve-ply source failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  -- Shape 85 is the singleton [165760] in the retained DAG header. Its exact
  -- relation to every original historical board is checked by ownStep?.
  let history := [maskPoints 165760]
  unless decide (HistoryMatches frame .positive history) &&
      !(decide (HistoryMatches frame .positive [])) do
    throw (IO.userError "the raw maximal footprint does not match the complete original history")
  IO.println s!"W31: {frame.positionHistory.length} original history rows match retained shape 85; missing-history negative rejected; {(← IO.monoMsNow)-started} ms"
  (← IO.getStdout).flush
  if historyOnly then return
  let some connected := ExteriorSource.recognize? region
    | throw (IO.userError "original 7x7 exterior did not generate its connectivity witness")
  let board := BufferedReplay.signatureBoard (boardSignature (rawBoard black white))
  let some first := ownStep? region connected frame .positive board history played
    | throw (IO.userError "retained W31 raw action failed original regional/history checks")
  let some actual := nativeStep? (Law.positionalSuperko 0) frame first.reply.move
    | throw (IO.userError "compiled W31 Black move failed original native legality")
  unless sameFrame actual first.reply.target &&
      (ownStep? region connected frame .positive board [] played).isNone &&
      (ownStep? region connected frame .positive board history (1, 1)).isNone &&
      (ownStep? region connected frame .positive board history (6, 6)).isNone do
    throw (IO.userError "raw Black reply/history or source negatives failed")
  let nextHistory := CoreHistory.insertFootprint (postCore region frame.visible.board .positive played) history
  let parent := first.reply.target
  let expansion := scoringExpansion parent
  if recorded : CoreHistory.covered nextHistory (stones parent.visible.board .positive) = true then
    if opponent : parent.visible.toMove = Polarity.positive.other then
      if passes : parent.visible.consecutivePasses = 0 then
        let mut regional := 0
        let mut environments := 0
        let mut passed := 0
        let mut checked := 0
        for port in List.finRange expansion.length do
          let observed := expansion.get port
          let target := BufferedReplay.restore (BufferedReplay.capture observed.2)
          have targetSame : target = observed.2 := BufferedReplay.restore_capture observed.2
          have native := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
          have step : LegalStep (Law.positionalSuperko 0) parent observed.1 target := by
            rw [targetSame]
            exact native.1
          let represented := whiteStep region (frame := parent) (target := target) .positive nextHistory
            first.history_matches recorded first.confined first.interior opponent passes native.2 step
          let some actual := nativeStep? (Law.positionalSuperko 0) parent observed.1
            | throw (IO.userError "original White enumeration contained an illegal move")
          unless sameFrame actual target && whitePort? region observed.1 == some represented.port &&
              decide (represented.port.Admitted (restrict region parent.visible.board) .positive) &&
              decide (restrict region target.visible.board =
                represented.port.nextBoard (restrict region parent.visible.board) .positive) &&
              decide (HistoryMatches target .positive nextHistory) &&
              target.visible.consecutivePasses == represented.port.nextPasses do
            throw (IO.userError "original White event failed its regional/history transport")
          match represented.port with
          | .play _ => regional := regional + 1
          | .environment => environments := environments + 1
          | .pass => passed := passed + 1
          checked := checked + 1
          if checked % 50 == 0 then
            IO.println s!"W31 one-step regional interpreter: {checked}/{expansion.length} original White ports; {(← IO.monoMsNow)-started} ms"
            (← IO.getStdout).flush
        IO.println s!"W31 raw choice {choice} -> original {repr first.reply.move}; {checked} White ports = {regional} regional + {environments} environment + {passed} pass; full history and phase checked; {(← IO.monoMsNow)-started} ms"
      else throw (IO.userError "original Black play did not reset pass phase")
    else throw (IO.userError "original Black play did not yield White control")
  else throw (IO.userError "the generated joint footprint was not retained")

end Control

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram

def main (args : List String) : IO Unit :=
  if args == ["--dag"] then
    SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram.Control.runDAG
  else SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram.Control.run (args == ["--history-only"])
