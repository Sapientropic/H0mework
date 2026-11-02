import SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy
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
elab "#check_seed_once_ir" : command => do
  let env ← getEnv
  let sourceName := "SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Source"
  let producer := `SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.produce._redArg
  let worker := `SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Source.seedOnce._redArg
  let some actual := IR.findEnvDecl env producer | throwError "missing original planner IR"
  let some body := IR.findEnvDecl env worker | throwError "missing source seedOnce IR"
  let rendered := toString body
  let head := (rendered.splitOn "case ").head!
  if (head.splitOn (sourceName ++ ".seed._redArg")).length != 1 then
    throwError "original checker eagerly executes before the actual counterexample scan"
  unless (head.splitOn "Initial.Failure.scan._redArg").length == 2 do
    throwError "source refusal must use precisely one original scan"
  unless (rendered.splitOn "Option.none →").length == 2 &&
      (rendered.splitOn "Option.some →").length == 2 do
    throwError "missing original optional-counterexample branches"
  let clean := ((rendered.splitOn "Option.none →")[1]!.splitOn "Option.some →").head!
  let failed := (rendered.splitOn "Option.some →")[1]!
  unless (clean.splitOn (sourceName ++ ".seed._redArg")).length == 2 do
    throwError "no-counterexample branch lost the complete original source checker"
  if (failed.splitOn (sourceName ++ ".seed._redArg")).length != 1 then
    throwError "counterexample branch redundantly invokes the original verifier"
  if let .fdecl _ _ _ code _ := actual then
    unless (calls code).any (fun name => name.toString.startsWith (sourceName ++ ".seedOnce")) do
      throwError "original GlobalPolicy.produce does not consume seedOnce"
  else throwError "original planner IR is not a function"
  logInfo "SEED ONCE IR PASS: original planner calls seedOnce; exactly one scan before branching; failed branch returns that counterexample; clean branch retains original checker"
#check_seed_once_ir
