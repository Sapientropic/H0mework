import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalDAGCache

open RegionalProgram

attribute [local instance 2000] List.decidableBAll
attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def keyPoints : List (Point 19) :=
  (allPoints 19).filter (fun point => point.1.val < 7 ∧ point.2.val < 7)

/-- A lookup hint only. Every hit separately checks the current board's Holds. -/
def blackKey (board : Board 19) : Nat :=
  keyPoints.foldl (fun result point =>
    if board point = some .positive then result + 2 ^ (7 * point.1.val + point.2.val)
    else result) 0

abbrev GeometryCache := Std.HashMap Nat (List (EyeCoalition.Geometry 19))

def coalitionAt? (region : Finset (Point 19)) (state : Snapshot)
    (geometry : EyeCoalition.Geometry 19) : Option (NodeProgram region state) :=
  if holds : EyeCoalition.Holds geometry .positive state.board then
    if accepted : acceptsMargin .positive (-345) (EyeCoalition.bound geometry .positive) = true then
      some ⟨fun frame source => VirginRegionAction.coalitionCertificate region frame .positive (-345)
        source.interior ⟨geometry, by rw [source.board_eq]; exact holds⟩ (.inl source.playing) accepted⟩
    else none
  else none

def firstCoalition? (region : Finset (Point 19)) (state : Snapshot) :
    List (EyeCoalition.Geometry 19) → Option (NodeProgram region state × Nat)
  | [] => none
  | geometry :: rest =>
      match coalitionAt? region state geometry with
      | some program => some (program, 1)
      | none => (firstCoalition? region state rest).map (fun (program, reads) => (program, reads + 1))

structure CachedCoalition (region : Finset (Point 19)) (state : Snapshot) where
  program : NodeProgram region state
  cache : GeometryCache
  hit : Bool
  reads : Nat

def compileCoalition? (region : Finset (Point 19)) (state : Snapshot) (cache : GeometryCache) :
    Option (CachedCoalition region state) :=
  let key := blackKey state.board
  let candidates := cache[key]?.getD []
  match firstCoalition? region state candidates with
  | some (program, reads) => some ⟨program, cache, true, reads⟩
  | none => do
      let detected ← EyeCoalition.recognize? state.board .positive
      let program ← coalitionAt? region state detected.geometry
      pure ⟨program, cache.insert key (detected.geometry :: candidates), false, candidates.length + 1⟩

abbrev VitalCache := Std.HashMap Nat (List (VitalChambers.Geometry 19))

def vitalAt? (region : Finset (Point 19)) (state : Snapshot)
    (geometry : VitalChambers.Geometry 19) : Option (NodeProgram region state) :=
  if roomsInside : ∀ room ∈ geometry.rooms, room ⊆ region then
    if holds : VitalChambers.Holds geometry .positive state.board then
      if accepted : acceptsMargin .positive (-345) (VitalChambers.bound geometry .positive) = true then
        some ⟨fun frame source => .vitalChambers
          ⟨geometry, vital_holds_lift region roomsInside (by rw [source.board_eq]; exact holds)⟩
          (.inl source.playing) accepted⟩
      else none
    else none
  else none

structure CachedVital (region : Finset (Point 19)) (state : Snapshot) where
  program : NodeProgram region state
  cache : VitalCache
  hit : Bool

def compileVital? (region : Finset (Point 19)) (state : Snapshot)
    (core : Finset (Point 19)) (rooms : Finset (Finset (Point 19))) (cache : VitalCache) :
    Option (CachedVital region state) :=
  let key := blackKey state.board
  let candidates := cache[key]?.getD []
  match candidates.find? (fun geometry => decide (geometry.core = core ∧ geometry.rooms = rooms)) with
  | some geometry => (vitalAt? region state geometry).map (fun program => ⟨program, cache, true⟩)
  | none => do
      let geometry ← VitalChambers.geometry? core rooms
      let program ← vitalAt? region state geometry
      pure ⟨program, cache.insert key (geometry :: candidates), false⟩

structure Stats where
  nodes : Nat := 0
  coalitionHits : Nat := 0
  coalitionCompiles : Nat := 0
  vitalHits : Nat := 0
  vitalCompiles : Nat := 0
  geometryReads : Nat := 0
  geometryKeys : Nat := 0
  ordinaryNanos : Nat := 0
  coalitionNanos : Nat := 0
  vitalNanos : Nat := 0
  elapsedNanos : Nat := 0
  deriving Repr

structure Result (region : Finset (Point 19)) (nodes : Array RawNode) where
  compiled : Compiled region nodes
  stats : Stats

/-- The original ascending-rank checker. Only the current coalition leaf
reader is shared; all own/White nodes still call production compileNode?. -/
def compile (region : Finset (Point 19)) (connected : ExteriorSource.Connected region)
    (nodes : Array RawNode) (root : Nat) (progressEvery : Nat := 10000) :
    IO (Result region nodes) := do
  let started ← IO.monoNanosNow
  let order := (List.finRange nodes.size).mergeSort
    (fun left right => nodes[left].state.rank ≤ nodes[right].state.rank)
  let mut rows : CheckedRows region nodes := Array.replicate nodes.size none
  let mut cache : GeometryCache := {}
  let mut vitalCache : VitalCache := {}
  let mut stats : Stats := {}
  for index in order do
    let tick ← IO.monoNanosNow
    let program ← match nodes[index].body with
      | .coalition => do
          let some produced := compileCoalition? region nodes[index].state cache
            | throw (IO.userError s!"coalition source rejected at row {index.val}")
          cache := produced.cache
          stats := {stats with
            coalitionHits := stats.coalitionHits + if produced.hit then 1 else 0
            coalitionCompiles := stats.coalitionCompiles + if produced.hit then 0 else 1
            geometryReads := stats.geometryReads + produced.reads
            coalitionNanos := stats.coalitionNanos + (← IO.monoNanosNow) - tick}
          pure produced.program
      | .vital core rooms => do
          let some produced := compileVital? region nodes[index].state core rooms vitalCache
            | throw (IO.userError s!"vital source rejected at row {index.val}")
          vitalCache := produced.cache
          stats := {stats with
            vitalHits := stats.vitalHits + if produced.hit then 1 else 0
            vitalCompiles := stats.vitalCompiles + if produced.hit then 0 else 1
            vitalNanos := stats.vitalNanos + (← IO.monoNanosNow) - tick}
          pure produced.program
      | _ => do
          let some produced := compileNode? region connected nodes rows index
            | throw (IO.userError s!"original node checker rejected row {index.val}")
          stats := {stats with ordinaryNanos := stats.ordinaryNanos + (← IO.monoNanosNow) - tick}
          pure produced
    rows := rows.set! index.val (some ⟨index, program⟩)
    stats := {stats with nodes := stats.nodes + 1}
    if progressEvery != 0 && stats.nodes % progressEvery == 0 then
      IO.println s!"DAG checked={stats.nodes}/{nodes.size} coalitionHit={stats.coalitionHits} geometryCompile={stats.coalitionCompiles} vitalHit={stats.vitalHits} vitalCompile={stats.vitalCompiles} elapsedMs={((← IO.monoNanosNow)-started)/1000000}"
      (← IO.getStdout).flush
  if bounded : root < nodes.size then
    let index : Fin nodes.size := ⟨root, bounded⟩
    let some program := checkedRow? rows index | throw (IO.userError "checked root absent")
    pure ⟨⟨index, program⟩, {stats with geometryKeys := cache.size, elapsedNanos := (← IO.monoNanosNow)-started}⟩
  else throw (IO.userError "raw root outside graph")

/-- The already generated source program, without the raw graph array. -/
structure Provider (region : Finset (Point 19)) where
  state : Snapshot
  program : NodeProgram region state

@[noinline] def provider {region : Finset (Point 19)} {nodes : Array RawNode}
    (compiled : Compiled region nodes) : Provider region :=
  ⟨nodes[compiled.root].state, compiled.program⟩

def Provider.at? {region : Finset (Point 19)} (supplied : Provider region)
    (frame : Frame 19) : Option (Certificate .positive (-345) frame) := do
  let source ← sourceAt? region supplied.state frame
  pure (supplied.program.run frame source.valid)

theorem provider_at_eq {region : Finset (Point 19)} {nodes : Array RawNode}
    (compiled : Compiled region nodes) (frame : Frame 19) :
    (provider compiled).at? frame = compiled.at? frame := rfl

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalDAGCache
