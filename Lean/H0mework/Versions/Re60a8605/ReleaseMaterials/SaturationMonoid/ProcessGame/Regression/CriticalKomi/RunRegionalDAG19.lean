import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgramCache
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.CriticalKomi.RegionalDAGLoader

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalDAGRun

open RegionalProgram RegionalDAGLoader RegionalDAGCache

def w31Word : List (Move 19) :=
  [.play (1, 1), .play (18, 18), .play (1, 2), .play (18, 16),
   .play (1, 3), .play (18, 14), .play (1, 0), .play (0, 1),
   .play (2, 3), .play (18, 12), .play (2, 1), .play (3, 1)]

def sameFrame (left right : Frame 19) : Bool :=
  let left := BufferedReplay.capture left
  let right := BufferedReplay.capture right
  left.signature == right.signature && left.toMove == right.toMove &&
    left.consecutivePasses == right.consecutivePasses && left.status == right.status &&
    left.positionHistory == right.positionHistory

def resources (stage : String) : IO Unit := do
  let pid ← IO.Process.getPID
  let stats ← IO.Process.output {cmd := "ps", args := #["-o", "rss=,time=", "-p", toString pid]}
  IO.println s!"RESOURCES {stage}: rssKiB/cpu={stats.stdout.trimAscii}"
  (← IO.getStdout).flush

def cacheControls (nodes : Array RawNode) : IO Unit := do
  for node in nodes do
    if let .coalition := node.body then
      let some first := compileCoalition? region node.state {}
        | throw (IO.userError "cache control first leaf rejected")
      unless !first.hit do throw (IO.userError "empty geometry cache reported a hit")
      let some repeated := compileCoalition? region node.state first.cache
        | throw (IO.userError "cache control repeated leaf rejected")
      unless repeated.hit do throw (IO.userError "same current leaf was not reused")
      let some geometry := (first.cache[blackKey node.state.board]?.getD []).head?
        | throw (IO.userError "generated geometry was not retained")
      let invadedBoard : Board 19 := fun point =>
        if point ∈ geometry.eyes then some Polarity.negative else node.state.board point
      let invaded : Snapshot := {node.state with board := invadedBoard}
      unless (coalitionAt? region invaded geometry).isNone do
        throw (IO.userError "cache hit assumed White-occupied eyes were empty")
      if let some fallback := compileCoalition? region invaded first.cache then
        unless !fallback.hit do throw (IO.userError "blocked geometry was accepted as a cache hit")
      IO.println "CACHE_CONTROLS fresh/reuse passed; White-filled eyes rejected as a hit"
      (← IO.getStdout).flush
      return
  throw (IO.userError "sample has no coalition control")

def vitalControls (nodes : Array RawNode) : IO Unit := do
  for node in nodes do
    if let .vital core rooms := node.body then
      let some first := compileVital? region node.state core rooms {}
        | throw (IO.userError "vital cache first geometry rejected")
      let some repeated := compileVital? region node.state core rooms first.cache
        | throw (IO.userError "vital cache repeated geometry rejected")
      unless !first.hit && repeated.hit do throw (IO.userError "vital cache did not compile then reuse")
      unless (compileVital? region node.state core ∅ first.cache).isNone do
        throw (IO.userError "vital cache ignored the supplied raw rooms")
      let roomPoints := rooms.biUnion id
      let occupiedBoard : Board 19 := fun point =>
        if point ∈ roomPoints then some Polarity.negative else node.state.board point
      let occupied := {node.state with board := occupiedBoard}
      unless (compileVital? region occupied core rooms first.cache).isNone do
        throw (IO.userError "vital cache assumed a White-filled room retained an empty point")
      IO.println "VITAL_CONTROLS fresh/reuse passed; wrong raw rooms and all-White rooms rejected"
      (← IO.getStdout).flush
      return
  throw (IO.userError "sample has no vital control")

def run (file : String) (originalW31 : Bool) : IO Unit := do
  resources "before-load"
  let loaded ← load file
  unless loaded.complete do throw (IO.userError "incomplete raw stream")
  IO.println s!"LOADED nodes={loaded.nodes.size} ms={loaded.elapsedNanos / 1000000} complete=true"
  resources "after-load"
  let some connected := ExteriorSource.recognize? region
    | throw (IO.userError "original exterior disconnected")
  if !originalW31 then
    cacheControls loaded.nodes
    vitalControls loaded.nodes
  let result ← RegionalDAGCache.compile region connected loaded.nodes loaded.root
  IO.println s!"CHECKED_STATS {repr result.stats}"
  resources "after-check"
  let supplied := provider result.compiled
  let word ← if originalW31 then pure w31Word else require (originalWord loaded.source)
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 word
    | throw (IO.userError "original source replay failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  let some certificate := supplied.at? frame
    | throw (IO.userError "compiled program rejected the actual original source")
  unless (supplied.at? (Frame.initial 19)).isNone do
    throw (IO.userError "unmatched initial source accepted")
  match certificate with
  | .choose _ reply child =>
      let some actual := nativeStep? (Law.positionalSuperko 0) frame reply.move
        | throw (IO.userError "generated original Black response illegal")
      unless sameFrame actual reply.target do
        throw (IO.userError "generated original Black response lost complete history")
      let shape := match child with | .all _ _ _ => "all" | _ => "other"
      IO.println s!"CERTIFICATE positive(-345) actualOriginalPly={word.length} move={repr reply.move} child={shape} historyRows={frame.positionHistory.length} rawNodes={loaded.nodes.size}"
  | .all _ _ _ =>
      IO.println s!"CERTIFICATE positive(-345) actualOriginalPly={word.length} root=all rawNodes={loaded.nodes.size}"
  | _ => throw (IO.userError "unexpected original root shape")
  resources "finished"

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalDAGRun

def main (args : List String) : IO Unit := do
  let file := args[0]?.getD
    "scratch/GoCriticalKomi/EarlierSourceSearch/.cache/w01-wide-core-b12-2-ecraabvz/vital_birth_witness.json.gz"
  SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalDAGRun.run file (args.contains "--w31")
