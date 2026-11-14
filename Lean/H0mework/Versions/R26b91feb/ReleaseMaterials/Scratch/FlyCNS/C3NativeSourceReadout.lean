import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PublishedRoot

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3NativeSourceReadout
open ContentReentryIO ContentReentryRoot Lean

def predecessorDirectory : System.FilePath :=
  "Lean/scratch/FlyCNS/.cache/C3/original-pure-root-successors-200"
def directory : System.FilePath :=
  "Lean/scratch/FlyCNS/.cache/C3/resident-published-root-400-attempt2"

structure RestoredAt (source : ContentReentryIO.Source) where
  private mk ::
  current : Current source.material
  originalBefore : Current source.material
  original : ContentReentryRoot.GeneratedAt source originalBefore
  complete : ContentFullPackedIO.Image
  sourceSame : capture current=complete
  originalSame : complete=capture original.next
  tick : current.tick=400
  visit : current.visit=4

/-- Fixed actual NN400 descendant is restored through the original source
material and checked against its original recorded continuation. No run,
caller-selected after or source birth occurs in this reader. -/
def restore (source : ContentReentryIO.Source) : IO (RestoredAt source) := do
  let report ← BodyIO.readJson (predecessorDirectory/"root-successors.json")
  let same : Bool ← BodyIO.checkedResult (report.getObjValAs? _ "complete_source_and_three_traces_equal")
  let count : Nat ← BodyIO.checkedResult (report.getObjValAs? _ "whole_disposition_rows")
  let invocations : Nat ← BodyIO.checkedResult (report.getObjValAs? _ "original_source_invocations")
  let visits : Array Nat ← BodyIO.checkedResult (report.getObjValAs? _ "generated_visits")
  if !same || count != 12 || invocations != 0 || visits != #[3,4] then
    throw (IO.userError "the original complete pure Root continuation is not settled")
  guard source.material
  let first ← ContentReentryRoot.readImplementation source source.initial
  let original ← ContentReentryRoot.readImplementationReopened source first.next
  let current ← readCurrent source.material (predecessorDirectory/"generated-4")
  let complete := capture current
  if originalSame:complete=capture original.next then
    for (name,bytes) in [("generated-events.npz",original.reply.events),
        ("learning-trace.npz",original.reply.learning),("physics-trace.npz",original.reply.physics)] do
      if (← IO.FS.readBinFile (predecessorDirectory/"generated-4"/name)) != bytes then
        throw (IO.userError "the same-source complete NN400 trace differs")
    if tick:current.tick=400 then
      if visit:current.visit=4 then
        return ⟨current,first.next,original,complete,rfl,originalSame,tick,visit⟩
      else throw (IO.userError "the actual pure source visit is not4")
    else throw (IO.userError "the actual pure source clock is not400")
  else throw (IO.userError "the actual complete pure descendant differs from its original source")

def originalRows {source : ContentReentryIO.Source} {installed : _root_.FlyCNS.C3BoundKernel.Installation}
    {before : Current source.material} (event : PublishedAt source installed before) : Array Json :=
  (List.finRange 6).toArray.map fun r =>
    let destination := event.original.patch.toLedgerWriteEvolution.destination (ContentReentryRoot.entry source before r)
    Json.mkObj [("source_responsibility",toJson r.val),("destination_responsibility",toJson destination.1.1.val),
      ("before_visit",toJson before.visit),("after_visit",toJson event.original.next.visit),
      ("before_tick",toJson before.tick),("after_tick",toJson event.original.next.tick),
      ("after_physics",toJson (physicsTick source.material event.original.next.words))]

def imageBytes (image : C3CompleteInventory.Image) : Nat :=
  image.physical.words.toArray.foldl (fun total word => total+word.bytes.size) 0 +
  image.physical.backend.toArray.foldl (fun total bytes => total+bytes.size) 0 +
  image.physical.header.size +
  (toString image.physical.visit).toUTF8.size +
  image.traces.toArray.foldl (fun total bytes => total+bytes.size) 0 +
  image.metadata.foldl (fun total file => total+file.1.toUTF8.size+file.2.size) 0


end C3NativeSourceReadout
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
