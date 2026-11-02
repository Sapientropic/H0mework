import SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
private partial def calls (body : IR.FnBody) : List Name :=
  match body with
  | .vdecl _ _ value next =>
      (match value with | .fap name _ | .pap name _ => [name] | _ => []) ++ calls next
  | .jdecl _ _ value next => calls value ++ calls next
  | .case _ _ _ alternatives => alternatives.toList.flatMap fun alt => calls alt.body
  | _ => if body.isTerminal then [] else calls body.body
private partial def acyclic (graph : List (Name × List Name)) (name : Name) (path : NameSet := {}) : Bool :=
  if path.contains name then false
  else match graph.find? (fun pair => pair.1 == name) with
    | none => true
    | some pair => pair.2.all (fun next => acyclic graph next (path.insert name))
elab "#check_counted_ir" : command => do
  let env ← getEnv
  let scopeName := "SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning"
  let mut stageCalls : List Name := []
  let mut countedCalls : List Name := []
  let mut originalCalls : List Name := []
  let mut countedGraph : List (Name × List Name) := []
  for i in [:env.header.moduleNames.size] do
    for decl in IR.declMapExt.getModuleEntries env i ++ IR.declMapExt.getModuleIREntries env i do
      if let .fdecl name _ _ body _ := decl then
        if name.toString.startsWith (scopeName ++ ".stage") then stageCalls := calls body ++ stageCalls
        if name.toString.startsWith (scopeName ++ ".Accounting.runCounted") then
          countedCalls := calls body ++ countedCalls
          countedGraph := (name,calls body) :: countedGraph
        if name.toString == scopeName ++ ".Accounting.run" || name.toString.startsWith (scopeName ++ ".Accounting.run.") then originalCalls := calls body ++ originalCalls
  unless stageCalls.any (fun n => n.toString.startsWith (scopeName ++ ".Accounting.runCounted")) do
    throwError "original stage did not consume the counted implementation"
  unless countedCalls.any (fun n => n.toString == scopeName ++ ".Accounting.run" || n.toString.startsWith (scopeName ++ ".Accounting.run.")) do
    throwError "counted fallback lost original run"
  unless countedGraph.all (fun pair => acyclic countedGraph pair.1) do
    throwError "counted implementation contains a recursive IR call cycle"
  if originalCalls.any (fun n => n.toString.startsWith (scopeName ++ ".Accounting.runCounted")) then
    throwError "original fallback unexpectedly calls the counted implementation"
  logInfo "COUNTED IR PASS: original stage calls runCounted; runCounted falls back to original run; counted IR helpers are acyclic and original fallback never redirects back"
#check_counted_ir
