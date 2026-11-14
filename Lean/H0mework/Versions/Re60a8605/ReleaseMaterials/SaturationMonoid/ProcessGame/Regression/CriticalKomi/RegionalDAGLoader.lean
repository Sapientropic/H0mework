import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalDAGLoader

open Lean RegionalProgram

attribute [local instance 2000] List.decidableBAll
attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def region : Finset (Point 19) :=
  Finset.univ.filter (fun point => point.1.val < 7 ∧ point.2.val < 7)

def maskPoints (mask : Nat) : Finset (Point 19) :=
  region.filter (fun point => mask.testBit (7 * point.1.val + point.2.val) = true)

@[noinline] def rawBoard (black white : Nat) : Board 19 :=
  fun point =>
    if point.1.val < 7 ∧ point.2.val < 7 then
      if black.testBit (7 * point.1.val + point.2.val) then some .positive
      else if white.testBit (7 * point.1.val + point.2.val) then some .negative else none
    else none

theorem rawBoard_eq_mask (black white : Nat) (point : Point 19) :
    rawBoard black white point =
      if point ∈ maskPoints black then some .positive
      else if point ∈ maskPoints white then some .negative else none := by
  by_cases inside : point.1.val < 7 ∧ point.2.val < 7
  · simp [rawBoard, maskPoints, region, inside]
  · simp [rawBoard, maskPoints, region, inside]

def point? (address : Nat) : Option (Point 19) :=
  if row : address / 7 < 19 then
    if column : address % 7 < 19 then some (⟨address / 7, row⟩, ⟨address % 7, column⟩)
    else none
  else none

def parseMask (value : Nat) : Except String (Finset (Point 19)) :=
  if value < 2 ^ 49 then pure (maskPoints value) else throw "mask exceeds the 7x7 observation"

def parsePort (value : Nat) : Except String PortCode :=
  if value = 49 then pure .environment
  else if value = 50 then pure .pass
  else if value < 49 then
    match point? value with | some point => pure (.play point) | none => throw "invalid point"
  else throw "invalid regional port"

abbrev Histories := Std.HashMap Nat (List (Finset (Point 19)))

def parseHistory (histories : Histories) (row : Json) : Except String Histories := do
  let id ← row.getObjValAs? Nat "id"
  if histories.contains id then throw "duplicate historical row"
  let masks ← row.getObjValAs? (List Nat) "maxima"
  let points ← masks.mapM parseMask
  pure (histories.insert id points)

/-- Same raw fields as the original decoder; external win/claim labels are not read. -/
def parseNode (histories : Histories) (index : Nat) (raw : Json) : Except String RawNode := do
  unless (← raw.getObjValAs? Nat "id") = index do throw "noncanonical raw node index"
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
  pure ⟨state, body⟩

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

structure Loaded where
  nodes : Array RawNode
  root : Nat
  source : List Nat
  complete : Bool
  streamSummary : Json
  jsonNanos : Nat
  historyNanos : Nat
  nodeNanos : Nat
  elapsedNanos : Nat

def require {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

/-- Transient JSON is bounded to one record by the producer. Only the typed
graph and its shared historical rows remain resident for compileDAG. -/
def load (file : String) (maxNodes : Nat := 0) : IO Loaded := do
  let started ← IO.monoNanosNow
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["scripts/go/regional_dag_stream.py", file, "--max-nodes", toString maxNodes]
    stdin := .null
    stdout := .piped
    stderr := .inherit }
  try
    let mut histories : Histories := {}
    let mut nodes : Array RawNode := #[]
    let mut root := 0
    let mut source : List Nat := []
    let mut gotHeader := false
    let mut done := false
    let mut complete := false
    let mut summary := Json.null
    let mut jsonNanos := 0
    let mut historyNanos := 0
    let mut nodeNanos := 0
    while !done do
      let line ← child.stdout.getLine
      if line.isEmpty then throw (IO.userError "record stream ended without a completion record")
      let tick ← IO.monoNanosNow
      let record ← require (Json.parse line)
      let kind ← require (record.getObjValAs? String "kind")
      jsonNanos := jsonNanos + (← IO.monoNanosNow) - tick
      match kind with
      | "header" =>
          if gotHeader then throw (IO.userError "duplicate stream header")
          unless (← require (record.getObjValAs? String "schema")) == "corner-birth-dag/v1" do
            throw (IO.userError "wrong stream source schema")
          root ← require (record.getObjValAs? Nat "root")
          source ← require (record.getObjValAs? (List Nat) "source")
          gotHeader := true
      | "history" =>
          unless gotHeader do throw (IO.userError "history before stream header")
          let tick ← IO.monoNanosNow
          histories ← require (parseHistory histories record)
          historyNanos := historyNanos + (← IO.monoNanosNow) - tick
      | "node" =>
          unless gotHeader do throw (IO.userError "node before stream header")
          let tick ← IO.monoNanosNow
          let raw ← require (record.getObjVal? "value")
          let node ← require (parseNode histories nodes.size raw)
          nodes := nodes.push node
          nodeNanos := nodeNanos + (← IO.monoNanosNow) - tick
      | "end" =>
          summary ← require (record.getObjVal? "summary")
          complete ← require (summary.getObjValAs? Bool "complete")
          unless (← require (summary.getObjValAs? Nat "nodes")) == nodes.size do
            throw (IO.userError "stream node count differs from the typed graph")
          done := true
      | _ => throw (IO.userError "unknown record kind")
    let exitCode ← child.wait
    unless exitCode == 0 do throw (IO.userError s!"stream producer exited {exitCode}")
    pure ⟨nodes, root, source, complete, summary, jsonNanos, historyNanos, nodeNanos,
      (← IO.monoNanosNow) - started⟩
  catch error =>
    try child.kill catch _ => pure ()
    let _ ← child.wait
    throw error

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalDAGLoader
