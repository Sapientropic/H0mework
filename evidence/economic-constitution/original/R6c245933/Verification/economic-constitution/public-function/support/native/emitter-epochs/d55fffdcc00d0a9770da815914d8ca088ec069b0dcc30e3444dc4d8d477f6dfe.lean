import PublicDefaultActualNative
import Lean.Compiler.Main
import Lean.Compiler.LCNF.EmitC
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open Lean
structure NativePlanRow where
  moduleName : String
  path : String
  deriving FromJson
run_elab do
  let some planPath ← IO.getEnv "HW_NATIVE_BATCH" | throwError "missing HW_NATIVE_BATCH"
  let text ← IO.FS.readFile planPath
  let parsed ← match Json.parse text with
    | .ok value => pure value
    | .error error => throwError "invalid native plan: {error}"
  let plan ← match fromJson? parsed (α := Array NativePlanRow) with
    | .ok value => pure value
    | .error error => throwError "invalid native rows: {error}"
  let originalEnv ← getEnv
  let imports : Array Import := #[{ module := `PublicDefaultActualNative },
    { module := `Lean.Compiler.Main },{ module := `Lean.Compiler.LCNF.EmitC }]
  Lean.enableInitializersExecution
  let (_, imported) ← (Lean.importModulesCore imports (arts := {})).run
  for row in plan do
    let moduleName := row.moduleName.toName
    let some index := originalEnv.getModuleIdx? moduleName
      | throwError "original module is not imported: {moduleName}"
    let data := originalEnv.header.moduleData[index]!
    IO.println s!"NATIVE CODEGEN START {moduleName}"
    (← IO.getStdout).flush
    let generated ← Lean.finalizeImport imported data.imports (← getOptions) 0
      (leakEnv := false) (loadExts := true) (isModule := data.isModule)
    for imp in data.imports do
      unless (generated.getModuleIdx? imp.module).isSome do
        throwError "base import state does not cover {moduleName} -> {imp.module}"
    let package := originalEnv.getModulePackageByIdx? index
    setEnv ((generated.setMainModule moduleName).setModulePackage package)
    let mut names := #[]
    for name in data.constNames do
      if (← Compiler.LCNF.getImpureSignature? name).isSome then
        if ← Compiler.LCNF.shouldGenerateCode name then
          names := names.push name
    setEnv originalEnv
    let repairName := `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Pricing.execute
    let mut originalMono := #[]
    for name in #[repairName, repairName ++ `_redArg] do
      if let some decl ← Compiler.LCNF.getMonoDecl? name then
        originalMono := originalMono.push decl
    unless originalMono.size == 2 do
      throwError "original Pricing.execute mono family is incomplete"
    setEnv ((generated.setMainModule moduleName).setModulePackage package)
    Compiler.compile names
    Compiler.LCNF.CompilerM.run do
      let manager ← Compiler.LCNF.getPassManager
      let mut state : (pu : Compiler.LCNF.Purity) × Array (Compiler.LCNF.Decl pu) := ⟨.pure, ← Compiler.LCNF.cleanup originalMono⟩
      let some boundary := manager.monoPassesNoLambda.findIdx? (fun pass => pass.name == `saveMono)
        | throwError "official saved-mono phase boundary is absent"
      for pass in manager.monoPassesNoLambda.extract (boundary+1) manager.monoPassesNoLambda.size ++ manager.impurePasses do
        let decls ← Compiler.LCNF.withPhase pass.phase do
          state.fst.withAssertPurity pass.phase.toPurity fun h => pass.run (h ▸ state.snd)
        state := ⟨_, decls⟩
        Compiler.LCNF.withPhase pass.phaseOut <|
          Compiler.LCNF.checkpoint pass.name state.snd true
    -- Imported specialization IR belongs to this original module but is not
    -- a kernel constant. Lower it with the official remaining mono/impure passes.
    let mut extras := #[]
    let mut lowered : NameSet := {}
    repeat
      let (_, used) ← Compiler.LCNF.collectUsedDecls (← Compiler.LCNF.getLocalImpureDecls)
      let mut needed := #[]
      for sig in used do
        if data.extraConstNames.contains sig.name || data.constNames.contains sig.name then
          let mut monoName := sig.name
          let mut saved ← Compiler.LCNF.getMonoDecl? monoName
          while saved.isNone && (monoName.getString! == "_redArg" || monoName.getString! == "_boxed") do
            monoName := monoName.getPrefix
            saved ← Compiler.LCNF.getMonoDecl? monoName
          if lowered.contains monoName then
            throwError "Already lowered original helper remains external: {sig.name} from {monoName}"
          let some decl ← Compiler.LCNF.getMonoDecl? monoName
            | throwError "Original helper has no checked mono IR: {sig.name} via {monoName}"
          unless needed.any (fun other => other.name == decl.name) do
            needed := needed.push decl
      if needed.isEmpty then break
      for decl in needed do lowered := lowered.insert decl.name
      extras := extras ++ needed
      Compiler.LCNF.CompilerM.run do
        let prepared ← Compiler.LCNF.cleanup needed
        let manager ← Compiler.LCNF.getPassManager
        let mut state : (pu : Compiler.LCNF.Purity) × Array (Compiler.LCNF.Decl pu) := ⟨.pure, prepared⟩
        for pass in manager.monoPassesNoLambda ++ manager.impurePasses do
          let decls ← Compiler.LCNF.withPhase pass.phase do
            state.fst.withAssertPurity pass.phase.toPurity fun h => pass.run (h ▸ state.snd)
          state := ⟨_, decls⟩
          Compiler.LCNF.withPhase pass.phaseOut <|
            Compiler.LCNF.checkpoint pass.name state.snd true
    -- Each separately lowered saved-mono group has its own finalization pass.
    -- Toposort the complete resulting local group once before official EmitC;
    -- this also records each final declaration exactly once.
    let finalNames ← Compiler.LCNF.getLocalImpureDecls
    let (recorded, _) := Compiler.LCNF.declOrderExt.getState (← getEnv)
    let mut stableNames := #[]
    let mut seen : NameSet := {}
    for name in recorded.reverse do
      unless seen.contains name do
        seen := seen.insert name
        stableNames := stableNames.push name
    unless stableNames.size == finalNames.size && finalNames.all seen.contains do
      throwError "original final impure order does not cover exactly the local bodies in {moduleName}"
    let ordered ← Compiler.LCNF.CompilerM.run do
      let decls ← stableNames.mapM fun name => do
        let some decl ← Compiler.LCNF.getLocalImpureDecl? name
          | throwError "missing final local impure declaration {name}"
        pure decl
      Compiler.LCNF.withPhase .impure do
        Compiler.LCNF.toposortDecls decls
    unless ordered.size == finalNames.size do
      throwError "whole local impure finalization lost a declaration in {moduleName}"
    modifyEnv fun env =>
      let env := Compiler.LCNF.declOrderExt.modifyState env fun _ => ([], {})
      ordered.foldl (fun env decl => Compiler.LCNF.recordFinalImpureDecl env decl.name) env
    let (order, orderSet) := Compiler.LCNF.declOrderExt.getState (← getEnv)
    unless order.length == finalNames.size && orderSet.size == finalNames.size do
      throwError "whole local impure finalization is not bijective in {moduleName}"
    -- Emit exactly the original import initialization order. The boot separately
    -- initializes the new decision after the complete original module closure.
    let mut abi := #[]
    let generatedEnv ← getEnv
    for name in finalNames do
      let some now ← Compiler.LCNF.getImpureSignature? name | throwError "missing generated signature {name}"
      setEnv originalEnv
      let prior ← Compiler.LCNF.getImpureSignature? name
      setEnv generatedEnv
      if let some old := prior then
        unless old.type == now.type && old.params.map (fun p => (p.type,p.borrow)) == now.params.map (fun p => (p.type,p.borrow)) do
          throwError "original runtime ABI changed for {name}: old arity={old.params.size}, new arity={now.params.size}"
        abi := abi.push name.toString
    let code ← Compiler.LCNF.emitC moduleName
    let path : System.FilePath := row.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path code
    let manifest := Json.mkObj [
      ("original_module", toJson moduleName.toString),
      ("module_package", toJson package),
      ("original_is_module",toJson data.isModule),
      ("runtime_initializer",toJson (mkModuleInitializationFunctionName moduleName package .runtime)),
      ("comptime_initializer",toJson (mkModuleInitializationFunctionName moduleName package .comptime)),
      ("original_initializer",toJson (mkModuleInitializationFunctionName moduleName package)),
      ("original_import_initializers",toJson (data.imports.map fun imp =>
        mkModuleInitializationFunctionName imp.module (originalEnv.getModulePackageByIdx? (originalEnv.getModuleIdx? imp.module).get!))),
      ("original_declarations", toJson (names.map Name.toString)),
      ("original_extra_mono_lowered", toJson (extras.map fun decl => decl.name.toString)),
      ("emitted_impure_declarations", toJson ((← Compiler.LCNF.getLocalImpureDecls).map Name.toString)),
      ("whole_impure_topological_order", toJson (ordered.map fun decl => decl.name.toString)),
      ("stable_original_recorded_order", toJson (stableNames.map Name.toString)),
      ("original_external_self_callees", toJson (0 : Nat)),
      ("saved_mono_abi_family", toJson (originalMono.map fun decl => decl.name.toString)),
      ("original_impure_abi_checked", toJson abi),
      ("official_remaining_mono_and_impure_passes", toJson true)]
    IO.FS.writeFile (row.path ++ ".json") (manifest.pretty ++ "\n")
    IO.println s!"NATIVE CODEGEN PASS {moduleName}"
    (← IO.getStdout).flush
  setEnv originalEnv
