import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeKeyDecoder
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeMetrics
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeSourceReadout

set_option autoImplicit false
namespace FlyCNS.C3NativeKeyActor
open Lean C3FiniteOccurrence C3NativeMinimum
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open ContentReentryIO ContentReentryRoot

def directory : System.FilePath := "Lean/scratch/FlyCNS/.cache/C3/native-key-source600"
def original500 : System.FilePath := C3NativeSourceReadout.directory/"generated-5"

def writeJson (path : System.FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.compress++"\n")

def resourceSample : IO Json := do
  let text ← C3NativeMetrics.sample
  return match Json.parse text with
    | .ok measured => measured
    | .error why => Json.mkObj [("measurement_parse_error",toJson why),("raw",toJson text)]

structure Phase where
  name : String
  start_ns : Nat
  start_heartbeats : Nat
  before : Json

def begin (name : String) : IO Phase := do
  writeJson (directory/"stage.json") (Json.mkObj [("stage",toJson name),("running",toJson true)])
  return ⟨name,← IO.monoNanosNow,← IO.getNumHeartbeats,← resourceSample⟩

def finish (phase : Phase) : IO Unit := do
  let stopped ← IO.monoNanosNow
  let allocations ← IO.getNumHeartbeats
  writeJson (directory/(phase.name++"-metrics.json")) (Json.mkObj [
    ("phase",toJson phase.name),("elapsed_ns",toJson (stopped-phase.start_ns)),
    ("small_allocation_heartbeats",toJson (allocations-phase.start_heartbeats)),
    ("before",phase.before),("after",← resourceSample),
    ("memory_scope",toJson "process RSS and malloc-zone counters; not Lean semantic live heap")])

structure Recorded500 (source : ContentReentryIO.Source) where
  private mk ::
  current : Current source.material
  traces : Vector ByteArray 3
  rows : Array Json
  visit : current.visit=5
  tick : current.tick=500
  physics : physicsTick source.material current.words=5000

def recordedRows (before after : Nat) (beforeNN afterNN physical : Nat) : Array Json :=
  (List.finRange 6).toArray.map fun r => Json.mkObj [
    ("source_responsibility",toJson r.val),("destination_responsibility",toJson r.val),
    ("before_visit",toJson before),("after_visit",toJson after),
    ("before_tick",toJson beforeNN),("after_tick",toJson afterNN),("after_physics",toJson physical)]

/-- Read only the held actor's already completed source record. This is a
Current/trace readout; it does not reconstruct a private PublishedAt proof. -/
def read500 (source : ContentReentryIO.Source) : IO (Recorded500 source) := do
  guard source.material
  let stage ← BodyIO.readJson (C3NativeSourceReadout.directory/"stage.json")
  if (← BodyIO.checkedResult (stage.getObjValAs? String "stage")) != "minimum-consumed-source-held" then
    throw (IO.userError "the original source500 has not completed its own consumer")
  let report ← BodyIO.readJson (C3NativeSourceReadout.directory/"published-successor.json")
  let schema : String ← BodyIO.checkedResult (report.getObjValAs? _ "schema")
  let rowCount : Nat ← BodyIO.checkedResult (report.getObjValAs? _ "whole_disposition_rows")
  let invocations : Nat ← BodyIO.checkedResult (report.getObjValAs? _ "original_source_invocations")
  let retained : Bool ← BodyIO.checkedResult (report.getObjValAs? _ "Source_and_installation_retained")
  let completed : Bool ← BodyIO.checkedResult (report.getObjValAs? _ "same_complete_source_publication_and_Root")
  if schema != "flycns-c3-resident-published-root-successor/v1" || rowCount != 6 || invocations != 0 || !retained || !completed then
    throw (IO.userError "the fixed source500 receipt is incomplete")
  let rows : Array Json ← BodyIO.checkedResult (report.getObjValAs? _ "whole_dispositions")
  let savedRows ← BodyIO.readJson (original500/"whole-dispositions.json")
  if rows != recordedRows 4 5 400 500 5000 || savedRows != Json.arr rows then
    throw (IO.userError "the actual source500 six destinations or clocks disagree")
  let current ← readCurrent source.material original500
  let events ← IO.FS.readBinFile (original500/"generated-events.npz")
  let learning ← IO.FS.readBinFile (original500/"learning-trace.npz")
  let physicsBytes ← IO.FS.readBinFile (original500/"physics-trace.npz")
  if visit:current.visit=5 then
    if tick:current.tick=500 then
      if physical:physicsTick source.material current.words=5000 then
        return ⟨current,⟨#[events,learning,physicsBytes],rfl⟩,rows,visit,tick,physical⟩
      else throw (IO.userError "the source record500 has another physical clock")
    else throw (IO.userError "the source record500 has another neural clock")
  else throw (IO.userError "the source record500 has another visit")

def recordImage {source : ContentReentryIO.Source} (recorded : Recorded500 source) : C3CompleteInventory.Image :=
  ⟨capture recorded.current,recorded.traces,C3CompleteInventory.sourceMetadata source⟩

def verifyImage {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (expected : C3CompleteInventory.Image) (state : C3NativeMinimum.Carrier boundary installed anchor) : IO Unit := do
  for observer in List.finRange 69 do
    let actual:=C3NativeMinimum.read observer state.val
    let wanted:=Except.ok (C3CompleteInventory.read (C3ReachableModel.reader observer) expected)
    if @decide (actual=wanted) (C3ReachableModel.outputEq observer actual wanted)==false then
      throw (IO.userError ("source key decoder changes original reader "++toString observer.val))

def verifyClocks {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : C3NativeMinimum.Carrier boundary installed anchor) (visit neural physical : Nat) : IO Unit := do
  let ready ← BodyIO.checkedResult (C3NativeMinimum.ready state)
  if ready.current.current.visit != visit || ready.current.current.tick != neural ||
      physicsTick boundary.source.material ready.current.current.words != physical then
    throw (IO.userError "source key decoder changes an original clock")

def saveEvent {boundary : Boundary} {installed : Installed boundary}
    {before : Current boundary.source.material}
    (event : PublishedAt boundary.source installed.material before) : IO Unit := do
  let path:=directory/"generated-6"
  writeCurrent event.original.next path
  IO.FS.writeBinFile (path/"generated-events.npz") event.original.reply.events
  IO.FS.writeBinFile (path/"learning-trace.npz") event.original.reply.learning
  IO.FS.writeBinFile (path/"physics-trace.npz") event.original.reply.physics
  writeJson (path/"whole-dispositions.json") (Json.arr (C3NativeSourceReadout.originalRows event))

def verifyActualRows {boundary : Boundary} {installed : Installed boundary}
    {before : Current boundary.source.material}
    (event : PublishedAt boundary.source installed.material before) : IO Unit := do
  let rows:=C3NativeSourceReadout.originalRows event
  let recorded ← BodyIO.readJson (directory/"generated-6/whole-dispositions.json")
  if recorded != Json.arr rows || rows.size != 6 then
    throw (IO.userError "source600 saved rows omit an actual destination")
  for responsibility in List.finRange 6 do
    let destination:=event.original.patch.toLedgerWriteEvolution.destination (ContentReentryRoot.entry boundary.source before responsibility)
    if destination.1.1.val != responsibility.val then
      throw (IO.userError "source600 actual patch destination differs from generated next")

structure HeldKey where
  private mk ::
  boundary : Boundary
  context : C3NativeCodec.Seal boundary
  installed : Installed boundary
  errors : C3NativeCodec.ErrorCache context installed
  bytes : ByteArray

/-- The comparison phase returns only the source context and its key.
Original500, event600 and decoded target Snapshots leave this scope. -/
def produce : IO HeldKey := do
  if (← directory.pathExists) then throw (IO.userError "source key consumer must have a fresh output directory")
  IO.FS.createDirAll directory
  let origin ← begin "same-source-reopen"
  let source ← reopenSource
  finish origin
  let initialization ← begin "context-install-anchor400"
  let boundary ← C3FiniteOccurrence.readBoundary source
  let restored ← C3NativeSourceReadout.restore boundary.source
  let context ← BodyIO.checkedResult (C3NativeCodec.at400 (boundary:=boundary) restored.original)
  let installed ← installPure boundary.source
  let bound ← BodyIO.checkedResult (C3FiniteOccurrence.bindInstallation boundary installed)
  let cache:=C3NativeCodec.emptyCache context bound
  if capture context.anchor.base.current != capture restored.current then
    throw (IO.userError "the Source-owned codec Anchor400 differs from its original complete occurrence")
  finish initialization
  let reading ← begin "existing-record500-key-save"
  let recorded ← read500 boundary.source
  let key : C3NativeCodec.Key context ← if within:recorded.current.visit<C3NativePrecision.stateBound boundary context.anchor then
    pure (.inl ⟨recorded.current.visit,within⟩)
    else throw (IO.userError "the actual source500 visit exceeds its original byte bound")
  let encoded:=C3NativeCodec.encode context key
  if encoded.size != 8 then throw (IO.userError "source500 success key does not have eight bytes")
  IO.FS.writeBinFile (directory/"source500.key") encoded
  finish reading
  let cold5 ← begin "cold-key-restore5-resident-context"
  let bytes5 ← IO.FS.readBinFile (directory/"source500.key")
  let decoded5 ← BodyIO.checkedResult (C3NativeCodec.restore context bound cache bytes5)
  finish cold5
  let validation5 ← begin "restore5-all69-three-clocks-existing-rows"
  verifyImage (recordImage recorded) decoded5
  verifyClocks decoded5 5 500 5000
  if recorded.rows != recordedRows context.anchor.base.current.visit 5 context.anchor.base.current.tick 500 5000 then
    throw (IO.userError "the decoded current does not continue the original six recorded destinations")
  let before ← BodyIO.checkedResult (C3NativeMinimum.ready decoded5)
  writeJson (directory/"source500-restored.json") (Json.mkObj [
    ("schema",toJson "flycns-c3-existing-source-record-key-reopen/v1"),
    ("source_identity",Json.mkObj [("instance_id",toJson boundary.source.material.instanceId),
      ("occurrence_id",toJson boundary.source.material.occurrenceId),("installation_sha256",toJson boundary.source.material.installationId)]),
    ("source_key_bytes",toJson encoded.size),("visit",toJson before.current.current.visit),
    ("NN",toJson before.current.current.tick),("physics",toJson (physicsTick boundary.source.material before.current.current.words)),
    ("all_original_readers_equal",toJson (69 : Nat)),("actual_existing_destinations",Json.arr recorded.rows),
    ("save_mode",toJson "existing source Current record readout; original PublishedAt remains in old actor"),
    ("Source_emit400_to500_calls",toJson (0 : Nat)),("pure_decoder_macro_visits",toJson (1 : Nat)),
    ("decode_context",toJson "Source, complete Anchor400 and fixed installation resident; complete validation reference500 resident; not an input to decoder"),
    ("new_subject_births",toJson (0 : Nat))])
  finish validation5
  let producing ← begin "one-original-emit500-to600"
  let event ← ContentReentryRoot.emitPublished boundary.source bound.material before.current.current
  finish producing
  let saving ← begin "same-event-savePublished-source600"
  let saved:=C3NativeCodec.savePublished context bound cache before event
  if saved.bytes.size != 8 then throw (IO.userError "actual same-event source600 key is not eight bytes")
  IO.FS.writeBinFile (directory/"source600.key") saved.bytes
  saveEvent (boundary:=boundary) (installed:=bound) event
  let actual:=C3CompleteInventory.fromActual event.original
  let existing:=C3NativeMinimum.consumePublished before event
  verifyImage actual existing
  verifyClocks existing 6 600 6000
  verifyActualRows (boundary:=boundary) (installed:=bound) event
  finish saving
  let cold6 ← begin "cold-key-restore6-resident-context"
  let bytes6 ← IO.FS.readBinFile (directory/"source600.key")
  let decoded6 ← BodyIO.checkedResult (C3NativeCodec.restore context bound saved.errors bytes6)
  finish cold6
  let validation6 ← begin "restore6-all69-three-clocks-whole-next"
  verifyImage actual decoded6
  verifyClocks decoded6 6 600 6000
  let after ← BodyIO.checkedResult (C3NativeMinimum.ready decoded6)
  if capture after.current.current != capture event.original.next then
    throw (IO.userError "source600 cold key decoder changes the whole generated next")
  writeJson (directory/"source600-restored.json") (Json.mkObj [
    ("schema",toJson "flycns-c3-same-published-event-key-reopen/v1"),
    ("source_key_bytes",toJson saved.bytes.size),("before_visit",toJson before.current.current.visit),
    ("after_visit",toJson event.original.next.visit),("before_NN",toJson before.current.current.tick),
    ("after_NN",toJson event.original.next.tick),("after_physics",toJson (physicsTick boundary.source.material event.original.next.words)),
    ("all_original_readers_equal",toJson (69 : Nat)),("actual_whole_destinations",Json.arr (C3NativeSourceReadout.originalRows event)),
    ("same_event_savePublished_additional_F_calls",toJson (0 : Nat)),("pure_decoder_macro_visits",toJson (2 : Nat)),
    ("one_actual_Source_emit500_to600",toJson true),("complete_anchor69_bytes",toJson (C3NativeSourceReadout.imageBytes (C3NativeMinimum.image context.anchor.base))),
    ("complete_source500_69_bytes",toJson (C3NativeSourceReadout.imageBytes (recordImage recorded))),
    ("complete_source600_69_bytes",toJson (C3NativeSourceReadout.imageBytes actual)),
    ("decode_context",toJson "Source, complete Anchor400 and fixed installation resident; complete validation reference600/event resident; not an input to decoder"),
    ("Source_reopen_calls",toJson (1 : Nat)),("new_subject_births",toJson (0 : Nat)),
    ("decodeScope",toJson "restore5 one pure macro; emit600 one Source macro; restore6 two pure macros from Anchor400")])
  finish validation6
  return ⟨boundary,context,bound,saved.errors,bytes6⟩

def run : IO Unit := do
  let held ← produce
  let isolated ← begin "encoded-key-only-held-context"
  writeJson (directory/"held-key-mode.json") (Json.mkObj [
    ("key_bytes",toJson held.bytes.size),
    ("mode",toJson "Source plus installation plus complete Anchor400 plus key; no target500/event600/decoded target retained"),
    ("context_anchor_visit",toJson held.context.anchor.base.current.visit),
    ("instance_id",toJson held.boundary.source.material.instanceId),
    ("occurrence_id",toJson held.boundary.source.material.occurrenceId),
    ("installation_sha256",toJson held.installed.material.identity.installationId),
    ("additional_F_or_decoder_calls",toJson (0 : Nat)),
    ("malloc_zone_counters",← resourceSample)])
  finish isolated
  writeJson (directory/"stage.json") (Json.mkObj [("stage",toJson "all-keys-complete-source-held"),("running",toJson false)])
  let output ← IO.getStdout
  output.putStrLn "all-keys-complete-source-held";output.flush
  let input ← IO.getStdin
  repeat
    let command:=(← input.getLine).trimAscii.toString
    if command=="quit" then break
    if command=="read" then
      output.putStrLn ((Json.mkObj [("key_bytes",toJson held.bytes.size),
        ("instance_id",toJson held.boundary.source.material.instanceId),
        ("installation_sha256",toJson held.installed.material.identity.installationId),
        ("Anchor_visit",toJson held.context.anchor.base.current.visit),
        ("recorded_errors",toJson held.errors.entries.length),
        ("semantic_Update",toJson false)]).compress)
      output.flush
    else throw (IO.userError "source key actor command is not registered")

end FlyCNS.C3NativeKeyActor

def main : IO Unit := FlyCNS.C3NativeKeyActor.run
