import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Source
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
private def actualBody (env : Environment) (root : Name) : Term.TermElabM String := do
  let some index := env.getModuleIdxFor? root | throwError "missing grant source {root}"
  let entries := IR.declMapExt.getModuleEntries env index ++ IR.declMapExt.getModuleIREntries env index
  let actual := entries.filter fun decl => decl.name.toString.startsWith root.toString
  unless !actual.isEmpty do throwError "missing executable grant source {root}"
  return String.intercalate "\n" (actual.toList.map fun decl => toString decl)
set_option pp.maxSteps 100000
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime.actualGrants_eq_frame
run_elab do
  let env ← getEnv
  let mut output := #[]
  for name in [`SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime.actualGrantsFromFrame,
      `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.grant] do
    let rendered ← actualBody env name
    output := output.push <| Json.mkObj [("name",toJson name.toString),("body",toJson rendered)]
    if name.toString.endsWith "actualGrantsFromFrame" then
      for forbidden in ["ProgrammeHistory.visitAt", "OutstandingSource.currentAt", "OutstandingSource.actualExecution"] do
        if (rendered.splitOn forbidden).length != 1 then throwError "original root replay remains in grant reader: {forbidden}"
      unless (rendered.splitOn "OutstandingSource.frameAt").length > 1 do
        throwError "grant reader does not consume the complete original source frame: {rendered}"
    else
      unless (rendered.splitOn "actualGrantsFromFrame").length > 1 do
        throwError "original financed grant does not call the frame reader: {rendered}"
  let some target ← IO.getEnv "HW_GRANT_FRAME_IR" | throwError "missing output"
  IO.FS.writeFile target ((Json.arr output).pretty ++ "\n")
  logInfo "GRANT FRAME IR PASS: original financed grant calls frame reader; no root visit or actualExecution replay in that reader"
