import Lean.Environment
import Lean.Declaration
import Lean.AddDecl
import Lean.Util.FoldConsts

open Lean
deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal

private def sameInfo (a b : ConstantInfo) : Bool :=
  match a,b with
  | .defnInfo x,.defnInfo y => x == y
  | .thmInfo x,.thmInfo y => x == y
  | .opaqueInfo x,.opaqueInfo y => x == y
  | .axiomInfo x,.axiomInfo y => x == y
  | .quotInfo x,.quotInfo y => x == y
  | .inductInfo x,.inductInfo y => x == y
  | .ctorInfo x,.ctorInfo y => x == y
  | .recInfo x,.recInfo y => x == y
  | _,_ => false

private def readParts (file : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let data ← readModuleData file
  if data.1.isModule then
    readModuleDataParts #[file,OLeanLevel.server.adjustFileName file,OLeanLevel.private.adjustFileName file]
  else return #[data]

private def compare (actual : Environment) (before after : System.FilePath) : IO (Nat × Nat) := do
  let oldParts ← readParts before
  let newParts ← readParts after
  let old := oldParts.foldl (fun all part => all ++ part.1.constants) #[]
  let fresh := newParts.foldl (fun all part => all ++ part.1.constants) #[]
  let safe := old.filter fun info => !info.isUnsafe && !info.isPartial
  let safeNew := fresh.filter fun info => !info.isUnsafe && !info.isPartial
  for info in safe do
    let next ← match safeNew.find? fun entry => entry.name == info.name with
      | some value => pure value
      | none =>
          let some value := actual.find? info.name
            | throw (IO.userError s!"missing original declaration {info.name}")
          -- On-demand congruence proofs may be generated in an earlier imported
          -- module. Their complete original ConstantInfo must still match below.
          pure value
    unless sameInfo info next do
      match info,next with
      | .defnInfo old,.defnInfo fresh =>
          unless old == {fresh with hints := old.hints} do
            throw (IO.userError s!"changed original definition {info.name}: type={old.type == fresh.type} value={old.value == fresh.value} metadataOnly={old == {fresh with hints := old.hints}}")
          match old.hints,fresh.hints with
          | .regular _,.regular _ => pure ()
          | _,_ => throw (IO.userError s!"changed original reducibility kind {info.name}")
      | _,_ => throw (IO.userError s!"changed original logical declaration {info.name}")
  return (safe.size,safeNew.size-safe.size)

def main (args : List String) : IO Unit := do
  let entries := args.toArray
  unless entries.size > 0 && entries.size % 2 == 0 do
    throw (IO.userError "expected nonempty original/candidate artifact pairs")
  let actual ← importModules #[{module := `PublicDefaultActualNative}] {} 0
  let mut exact := 0
  let mut added := 0
  for i in List.range (entries.size / 2) do
    let counts ← compare actual entries[2*i]! entries[2*i+1]!
    exact := exact + counts.1
    added := added + counts.2
  IO.println s!"INTEGRATED LOGICAL IDENTITY PASS: modules={entries.size/2}; unchangedOriginalBodiesAndTypes={exact}; additiveDeclarations={added}"
