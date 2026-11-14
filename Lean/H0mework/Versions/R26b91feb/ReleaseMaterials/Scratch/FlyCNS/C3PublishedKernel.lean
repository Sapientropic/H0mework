import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SuccessfulKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3CompressedTraceWriter

set_option autoImplicit false
namespace FlyCNS.C3Published

structure Result where
  numerical : FlyCNS.C3Successful.Result
  learning : ByteArray

/-- Publication receives only the newly generated seven PL members. Gate
operations retain the original empty receipt rather than an empty archive. -/
def publish (generated : FlyCNS.C3Successful.Result) : Except String Result := do
  let learning ← match generated.learning with
    | none => pure ByteArray.empty
    | some members => FlyCNS.C3CompressedTrace.generate members
  return ⟨generated,learning⟩

/-- Whole macro computation and all archive formatting are pure source
operations. No finished numerical state, trace or evaluator is an argument. -/
def action (material : FlyCNS.C3Macro.Material) (operation : FlyCNS.C3Native.Operation)
    (before : FlyCNS.C3Successful.Current) : Except String Result := do
  let generated ← FlyCNS.C3Successful.action material operation before
  publish generated

def successor (material : FlyCNS.C3Macro.Material) (before : FlyCNS.C3Successful.Current) :
    Except String Result :=
  action material (FlyCNS.C3Native.operationAt before.original.visit) before

def word (material : FlyCNS.C3Macro.Material) : List FlyCNS.C3Native.Operation →
    FlyCNS.C3Successful.Current → Except String FlyCNS.C3Successful.Current
  | [],current => .ok current
  | operation::rest,current => do
      let next ← action material operation current
      word material rest next.numerical.current

end FlyCNS.C3Published
