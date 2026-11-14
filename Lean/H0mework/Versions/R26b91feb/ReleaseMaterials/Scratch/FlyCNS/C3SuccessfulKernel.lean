import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3MacroKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3HistoryRegister
set_option autoImplicit false
namespace FlyCNS.C3Successful
open FlyCNS.C3Macro

structure Current where
  original : FlyCNS.C3Macro.Current
  history : FlyCNS.C3History.Slots
structure Result where
  current : Current
  generated : FlyCNS.C3Macro.Generated
  written : FlyCNS.C3Writer.Result
  events : ByteArray
  physics : Option ByteArray
  learning : Option (Array FlyCNS.C3TraceWriter.Member)

/-- Full source context is written from the same newly generated stock and
neural events. Original gate operations produce no physical/learning archive. -/
def finish (m : Material) (before : Current) (operation : FlyCNS.C3Native.Operation)
    (g : FlyCNS.C3Macro.Generated) : Except String Result := do
  let slots ← FlyCNS.C3History.capture g.current.programme.environmentHistory.toList
  let history := FlyCNS.C3History.events slots
  let document ← FlyCNS.C3Document.generate before.original.sourceDocument history
    g.current.programme.numerical.neural.plasticChanges
  let spikes := g.cycles.foldl (fun total c => total+c.events.fired.size) 0
  let inputs := g.cycles.foldl (fun total c => total+c.events.inputCells.size) 0
  let op := match operation with | .neural => "neural" | .damage => "damage" | .repair => "repair"
  let written := FlyCNS.C3Writer.generate m.catalogue.writer
    ⟨g.registers.toArray,before.original.visit,op,spikes,inputs,document⟩
  let nextProgramme := {g.current.programme with environmentHistory:=history}
  let current := {g.current with sourceDocument:=written.sourceDocument,programme:=nextProgramme}
  let events := FlyCNS.C3TraceWriter.generate (FlyCNS.C3Macro.eventMembers before.original operation g)
  let physics := match operation with
    | .neural => some (FlyCNS.C3TraceWriter.generate (FlyCNS.C3Macro.physicsMembers before.original g))
    | .damage | .repair => none
  let learning := match operation with
    | .neural => some (FlyCNS.C3Macro.learningMembers g)
    | .damage | .repair => none
  return ⟨⟨current,slots⟩,g,written,events,physics,learning⟩

/-- Successful storage keeps the original positive Python counters in their
installed signed dtype. No count is wrapped to manufacture a later Current. -/
def action (m : Material) (operation : FlyCNS.C3Native.Operation) (before : Current) : Except String Result := do
  if FlyCNS.C3Native.operationAt before.original.visit != operation then
    throw "operation not admitted at this source incidence"
  let physics := (before.original.bodyWords.get ⟨20,by decide⟩).bits 0 |>.toNat
  let later := physics+10*(FlyCNS.C3Macro.neuralTicks operation)
  if later>FlyCNS.C3Clock.signedLimit then
    throw "Python int too large to convert to C long"
  let start := {before.original with programme := {before.original.programme with
    environmentHistory:=FlyCNS.C3History.events before.history}}
  let g ← FlyCNS.C3Macro.generate m operation start
  finish m before operation g

def successor (m : Material) (before : Current) : Except String Result :=
  action m (FlyCNS.C3Native.operationAt before.original.visit) before

def word (m : Material) : List FlyCNS.C3Native.Operation → Current → Except String Current
  | [],current => .ok current
  | operation::rest,current => do
    let next ← action m operation current
    word m rest next.current

theorem stock_history_bounded (r : Result) :
    (FlyCNS.C3History.events r.current.history).size≤4 :=
  FlyCNS.C3History.events_bounded _

end FlyCNS.C3Successful
