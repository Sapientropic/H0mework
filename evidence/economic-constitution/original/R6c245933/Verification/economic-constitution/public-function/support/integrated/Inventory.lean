import PublicDefaultActualNative
import Lean.Compiler.Main
import Lean.Compiler.LCNF.EmitC
open Lean
set_option maxRecDepth 100000
run_elab do
  let env ← getEnv
  let mut pending : List Name := [`PublicDefaultActualNative]
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while let name::rest := pending do
    pending := rest
    unless seen.contains name do
      seen := seen.insert name
      let some index := env.getModuleIdx? name | throwError "missing original module {name}"
      let data := env.header.moduleData[index]!
      pending := data.imports.toList.map (·.module) ++ pending
      let package := env.getModulePackageByIdx? index
      rows := rows.push <| Json.mkObj [
        ("module",toJson name.toString),
        ("package",toJson package),
        ("imports",toJson (data.imports.map fun imp => imp.module.toString)),
        ("declarations",toJson data.constNames.size),
        ("extras",toJson data.extraConstNames.size),
        ("is_module",toJson data.isModule),
        ("initializer",toJson (mkModuleInitializationFunctionName name package)),
        ("runtime_initializer",toJson (mkModuleInitializationFunctionName name package .runtime)),
        ("comptime_initializer",toJson (mkModuleInitializationFunctionName name package .comptime)),
        ("import_initializers",toJson (data.imports.map fun imp =>
          mkModuleInitializationFunctionName imp.module (env.getModulePackageByIdx? (env.getModuleIdx? imp.module).get!)))]
  let some output ← IO.getEnv "HW_NATIVE_INVENTORY" | throwError "missing output"
  IO.FS.writeFile output (Json.pretty (Json.arr rows) ++ "\n")
  logInfo m!"ORIGINAL NATIVE IMPORT INVENTORY: modules={rows.size}"
