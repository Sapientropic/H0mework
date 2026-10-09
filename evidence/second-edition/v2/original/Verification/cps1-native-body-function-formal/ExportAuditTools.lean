import Lean
open Lean Elab Command
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def ownerModules : List Name := [`CPS1MaterialIncidence.NativeBodyFunction,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime.BodyFunction]

private def rawInfo (env : Environment) (name : Name) : Option ConstantInfo := do
  let index ← env.getModuleIdxFor? name
  let data := env.header.moduleData[index.toNat]!
  let position ← data.constNames.findIdx? (· == name)
  data.constants[position]?

private def usedValues (info : ConstantInfo) : Array Name :=
  match info with
  | .defnInfo value => value.value.getUsedConstants
  | .thmInfo value => value.value.getUsedConstants
  | .opaqueInfo value => value.value.getUsedConstants
  | .recInfo value => value.rules.foldl (fun deps rule => deps ++ rule.rhs.getUsedConstants) #[]
  | _ => #[]

private def usedConstants (info : ConstantInfo) : Array Name := Id.run do
  let mut deps := info.type.getUsedConstants ++ usedValues info
  match info with
  | .inductInfo value => deps := deps ++ value.ctors.toArray ++ value.all.toArray
  | .ctorInfo value => deps := deps.push value.induct
  | .recInfo value => deps := deps ++ value.all.toArray
  | _ => pure ()
  return deps

private def kind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .inductInfo _ => "inductive" | .quotInfo _ => "quotient"

private def sameCompleteInfo (raw aliasInfo : ConstantInfo) : Bool :=
  raw.name == aliasInfo.name && raw.type == aliasInfo.type && raw.value? true == aliasInfo.value? true &&
    raw.levelParams == aliasInfo.levelParams && raw.isUnsafe == aliasInfo.isUnsafe &&
    raw.isPartial == aliasInfo.isPartial && kind raw == kind aliasInfo &&
    (match raw,aliasInfo with
      | .recInfo a,.recInfo b => a == b
      | .ctorInfo a,.ctorInfo b => a == b
      | .inductInfo a,.inductInfo b => a.numParams == b.numParams && a.numIndices == b.numIndices &&
          a.ctors == b.ctors && a.all == b.all && a.numNested == b.numNested &&
          a.isRec == b.isRec && a.isUnsafe == b.isUnsafe
      | _,_ => true)

private def jsonNames (names : Array Name) : Json :=
  .arr (names.map (fun name => .str name.toString))

private def progress (message : String) : CommandElabM Unit := liftIO do
  let stream ← IO.getStdout
  stream.putStrLn message
  stream.flush

private def auditPrefix : CommandElabM String := liftIO do
  let some path ← IO.getEnv "CPS1_AUDIT_PREFIX" | throw (IO.userError "CPS1_AUDIT_PREFIX missing")
  return path

private def moduleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!.toString
  | none => "<current>"

private def exprChildren : Expr → Array Expr
  | .app fn arg => #[fn,arg]
  | .lam _ domain body _ | .forallE _ domain body _ => #[domain,body]
  | .letE _ type value body _ => #[type,value,body]
  | .mdata _ body | .proj _ _ body => #[body]
  | _ => #[]

private def officialCompilerBackends (env : Environment) : CommandElabM (Array Name) := do
  let mut helpers : Array Name := #[]
  let mut rows : Array Json := #[]
  let mut parents : Array (Name × String) := #[]
  -- Compute every fresh compiler helper from an actual raw parent name.
  for module in ownerModules do
    let some index := env.header.moduleNames.findIdx? (· == module) | throwError m!"BACKEND_OWNER_MISSING {module}"
    let data := env.header.moduleData[index]!
    for parent in data.constNames do
      if data.constNames.contains (Compiler.mkUnsafeRecName parent) then
        parents := parents.push (module,parent.toString)
  for (module,parentText) in parents do
    let some moduleIndex := env.header.moduleNames.findIdx? (· == module) | throwError m!"BACKEND_OWNER_MISSING {module}"
    let data := env.header.moduleData[moduleIndex]!
    let some parent := data.constNames.find? (fun name => name.toString == parentText) | throwError m!"SAFE_TOTAL_PARENT_MISSING {module} {parentText}"
    let helper := Compiler.mkUnsafeRecName parent
    unless data.constNames.contains helper do throwError m!"OFFICIAL_BACKEND_MISSING {helper}"
    let some parentInfo := rawInfo env parent | throwError m!"PARENT_RAW_FULLPARTS_MISSING {parent}"
    let some helperInfo := rawInfo env helper | throwError m!"BACKEND_RAW_FULLPARTS_MISSING {helper}"
    unless !parentInfo.isUnsafe && !parentInfo.isPartial && !helperInfo.isUnsafe && helperInfo.isPartial do
      throwError m!"OFFICIAL_BACKEND_ACTUAL_FLAGS_DIFFER {parent} {helper}"
    unless (parentInfo.value? true).isSome && (helperInfo.value? true).isSome do throwError m!"OFFICIAL_PARENT_BACKEND_TVO_UNREADABLE {helper}"
    if (usedConstants parentInfo).contains helper then throwError m!"SAFE_PARENT_MATH_USES_BACKEND {parent} {helper}"
    helpers := helpers.push helper
    rows := rows.push (Json.mkObj [("module",toJson module.toString),("parent",toJson parent.toString),
      ("helper",toJson helper.toString),("Compiler_mkUnsafeRecName_exact",toJson true),
      ("parent_unsafe",toJson parentInfo.isUnsafe),("parent_partial",toJson parentInfo.isPartial),
      ("helper_unsafe",toJson helperInfo.isUnsafe),("helper_partial",toJson helperInfo.isPartial),
      ("complete_TVO_readable",toJson true),("parent_math_value_not_direct_helper",toJson true)])
  let output ← auditPrefix
  liftIO <| IO.FS.writeFile (output ++ ".compiler-backends.json") (Json.arr rows).pretty
  return helpers

private def inventory : CommandElabM (Array (Name × (Name × ConstantInfo))) := do
  let env ← getEnv
  let exactBackends ← officialCompilerBackends env
  unless env.header.trustLevel == 0 do throwError "TRUST_ZERO_REQUIRED"
  progress "OWNER_INVENTORY_BEGIN"
  let imported := env.header.moduleNames
  let indices : Std.HashMap Name Nat := imported.zipIdx.foldl (fun result row => result.insert row.1 row.2) {}
  let mut own : Array (Name × (Name × ConstantInfo)) := #[]
  let mut previous : Std.HashMap Name ConstantInfo := {}
  for module in ownerModules do
    let some index := indices[module]? | throwError m!"OWNER_NOT_IMPORTED {module}"
    let data := env.header.moduleData[index]!
    unless data.constants.size > 0 do throwError m!"EMPTY_OWNER {module}"
    unless data.constNames.size == data.constants.size do throwError m!"RAW_SIZE_MISMATCH {module}"
    for name in data.constNames, info in data.constants do
      unless name == info.name do throwError m!"RAW_NAME_MISMATCH {module} {name}"
      if info.isUnsafe || (info.isPartial && !exactBackends.contains name) then throwError m!"RAW_UNSAFE_PARTIAL_NEEDS_EXACT_COMPILER_CLASSIFICATION {module} {name}"
      if let some old := previous[name]? then
        unless sameCompleteInfo info old do throwError m!"OWNER_RAW_ALIAS_COMPLETE_TVO_MISMATCH {module} {name}"
      previous := previous.insert name info
      own := own.push (module,(name,info))
    progress s!"OWNER {module} declarations={data.constants.size}"
  own := own.qsort (fun first last => first.2.1.toString < last.2.1.toString)
  let path ← auditPrefix
  let expressions ← liftIO <| IO.FS.Handle.mk (path ++ ".expressions.jsonl") .write
  let owners ← liftIO <| IO.FS.Handle.mk (path ++ ".owners.jsonl") .write
  let mut memo : ExprStructMap Nat := {}
  let emit (value : Expr) : StateT (ExprStructMap Nat) CommandElabM Nat := do
    let mut memo ← get
    let mut pending : Array (Expr × Bool) := #[(value,false)]
    while !pending.isEmpty do
      let (node,ready) := pending.back!
      pending := pending.pop
      if !(memo.contains ⟨node⟩) then
        if !ready then
          pending := pending.push (node,true)
          for child in (exprChildren node).reverse do
            if !(memo.contains ⟨child⟩) then pending := pending.push (child,false)
        else
          let id := memo.size
          let refs := (exprChildren node).map (fun child => toJson (memo[ExprStructEq.mk child]!))
          let fields : List (String × Json) := match node with
            | .bvar index => [("tag",toJson "bvar"),("index",toJson index)]
            | .fvar name => [("tag",toJson "fvar"),("name",toJson (reprStr name))]
            | .mvar name => [("tag",toJson "mvar"),("name",toJson (reprStr name))]
            | .sort level => [("tag",toJson "sort"),("level",toJson (reprStr level))]
            | .const name levels => [("tag",toJson "const"),("name",toJson (reprStr name)),("levels",toJson (levels.map reprStr))]
            | .app .. => [("tag",toJson "app")]
            | .lam name _ _ binder => [("tag",toJson "lam"),("name",toJson (reprStr name)),("binder",toJson (reprStr binder))]
            | .forallE name _ _ binder => [("tag",toJson "forall"),("name",toJson (reprStr name)),("binder",toJson (reprStr binder))]
            | .letE name _ _ _ nondependent => [("tag",toJson "let"),("name",toJson (reprStr name)),("nondependent",toJson nondependent)]
            | .lit literal => [("tag",toJson "literal"),("literal",toJson (reprStr literal))]
            | .mdata metadata _ => [("tag",toJson "mdata"),("metadata",toJson (reprStr metadata))]
            | .proj name index _ => [("tag",toJson "proj"),("name",toJson (reprStr name)),("index",toJson index)]
          liftIO <| expressions.putStrLn (Json.mkObj (("id",toJson id) :: ("children",.arr refs) :: fields)).compress
          memo := memo.insert ⟨node⟩ id
    set memo
    return memo[ExprStructEq.mk value]!
  for (emittingModule,(name,info)) in own do
    let (typeRoot,nextMemo) ← (emit info.type).run memo
    memo := nextMemo
    let mut valueRoot : Json := .null
    if let some value := info.value? true then
      let (id,nextMemo) ← (emit value).run memo
      memo := nextMemo
      valueRoot := toJson id
    let mut rules : Array Json := #[]
    if let .recInfo recursor := info then
      for rule in recursor.rules do
        let (id,nextMemo) ← (emit rule.rhs).run memo
        memo := nextMemo
        rules := rules.push (Json.mkObj [("constructor",toJson rule.ctor.toString),("fields",toJson rule.nfields),("root",toJson id)])
    let row := Json.mkObj [
      ("name",toJson name.toString),("module",toJson emittingModule.toString),("canonical_module",toJson (moduleName env name)),("kind",toJson (kind info)),
      ("type_root",toJson typeRoot),("value_root",valueRoot),("recursor_rules",.arr rules),
      ("constructor_metadata",match info with
        | .ctorInfo v => Json.mkObj [("inductive",toJson v.induct.toString),("index",toJson v.cidx),("parameters",toJson v.numParams),("fields",toJson v.numFields)]
        | _ => .null),
      ("recursor_metadata",match info with
        | .recInfo v => Json.mkObj [("parameters",toJson v.numParams),("indices",toJson v.numIndices),("motives",toJson v.numMotives),("minors",toJson v.numMinors),("k",toJson v.k)]
        | _ => .null),
      ("constructors",match info with | .inductInfo v => jsonNames v.ctors.toArray | _ => .arr #[]),
      ("inductive_metadata",match info with
        | .inductInfo v => Json.mkObj [("all",jsonNames v.all.toArray),("parameters",toJson v.numParams),("indices",toJson v.numIndices),("nested",toJson v.numNested),("recursive",toJson v.isRec)]
        | _ => .null),
      ("all_dependencies",jsonNames (usedConstants info)),
      ("levels",jsonNames info.levelParams.toArray),("unsafe",toJson info.isUnsafe),("partial",toJson info.isPartial),
      ("actual_raw_fullparts_TVO",toJson true),
      ("official_safe_total_compiler_backend",toJson (exactBackends.contains name)),
      ("type_constants",jsonNames info.type.getUsedConstants),("value_constants",jsonNames (usedValues info))]
    liftIO <| owners.putStrLn row.compress
  liftIO <| owners.flush
  liftIO <| expressions.flush
  progress s!"LOSSLESS_EXPR_DAG owners={own.size} nodes={memo.size}"
  let mut header : Array Json := #[]
  for module in imported do
    let artifact ← liftIO <| findOLean module
    let index := indices[module]!
    let data := env.header.moduleData[index]!
    let parts := if data.isModule then #[artifact.toString,artifact.toString++".server",artifact.toString++".private"] else #[artifact.toString]
    for dependency in data.imports do
      let some prior := indices[dependency.module]? | throwError m!"UNKNOWN_IMPORT_HEADER {module} {dependency.module}"
      unless prior < index do throwError m!"IMPORT_CYCLE {module} {dependency.module}"
    header := header.push (Json.mkObj [("module",toJson module.toString),("olean",toJson artifact.toString),
      ("parts",toJson parts),("private_fullparts",toJson true),("declarations",toJson data.constants.size),
      ("imports",toJson (data.imports.map fun dep => Json.mkObj [("module",toJson dep.module.toString),("all",toJson dep.importAll),("exported",toJson dep.isExported),("meta",toJson dep.isMeta)]))])
  liftIO <| IO.FS.writeFile (path ++ ".header.json") (Json.arr header).pretty
  return own


elab "auditNativeBodyFunctionCandidate" : command => do
  let rawOwn ← inventory
  let env ← getEnv
  let backends ← officialCompilerBackends env
  let own := rawOwn.filter (fun row => !backends.contains row.2.1)
  let ownNames : NameSet := own.foldl (fun result row => result.insert row.2.1) {}
  let some paidPath ← liftIO (IO.getEnv "CPS1_REUSED_ROOT_NAMES") | throwError "PAID_NAMES_REQUIRED"
  let paidText ← liftIO <| IO.FS.readFile paidPath
  let paid : Std.HashSet String := (paidText.splitOn "\n").foldl (fun result name => result.insert name) {}
  let rechecked := (own.filter (fun row => paid.contains row.2.1.toString)).map (fun row => row.2.1)
  let paid := rechecked.foldl (fun result name => result.erase name.toString) paid
  progress s!"RECHECKED_PAID_NAMES {rechecked}"
  let output ← auditPrefix
  let valueClosure (initial : Name) : CommandElabM NameSet := do
    let mut seen : NameSet := {}
    let mut pending := #[initial]
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if !seen.contains name then
        seen := seen.insert name
        if ownNames.contains name then
          let some info := rawInfo env name | throwError m!"RAW_OWNED_VALUE_NODE_MISSING {name}"
          for dependency in usedValues info do
            if !seen.contains dependency then pending := pending.push dependency
    return seen
  let checks : Array (Name × Array Name) := #[
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.ChannelRead, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.channel_read, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.FunctionDisposition, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.function_disposition, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.DispositionLaw, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.disposition_law, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.source_generated_native_body_function, #[`CPS1MaterialIncidence.NativeBodyFunctionProbe.function_disposition,`CPS1MaterialIncidence.NativeBodyProbe.bodyEvent,`CPS1MaterialIncidence.NativeBodyProbe.bodyWrite]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.actual_result, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.actual_execution, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.actual_next, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.next_state, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.next_stock, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.next_history, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.actual_disposition, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.account, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.whole, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.fields, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.electrons, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.invariant, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.genomic_read, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.duties, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.strict_state, #[]),
    (`CPS1MaterialIncidence.NativeBodyFunctionProbe.unchanged_state_cannot_be_positive, #[`CPS1MaterialIncidence.NativeCPContinuationProbe.strict_direction_irrefl]),
    (`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.FunctionAtDisposition, #[]),
    (`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.NativeBodyFunctionRootAt, #[]),
    (`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.source_generated_native_body_root_function, #[`CPS1MaterialIncidence.NativeBodyFunctionProbe.source_generated_native_body_function,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.source_generated_native_body_root_next,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.native_material_factorizes,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.literal_native_body_next]),
    (`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.source_generated_native_body_after_parent_function, #[`CPS1MaterialIncidence.NativeBodyFunctionProbe.source_generated_native_body_function,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.afterParent,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.source_generated_native_body_after_parent,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.native_material_factorizes,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.literal_native_body_next])
  ]
  let mut valueRows : Array Json := #[]
  let mut missing : Array String := #[]
  for (mouth,required) in checks do
    let closure ← valueClosure mouth
    for dependency in required do
      unless closure.contains dependency do
        missing := missing.push s!"{mouth} -> {dependency}"
    valueRows := valueRows.push (Json.mkObj [("mouth",toJson mouth.toString),("required",jsonNames required),("owned_value_closure",jsonNames closure.toArray),("type_edges_used",toJson false)])
  liftIO <| IO.FS.writeFile (output++".value-paths.json") (Json.arr valueRows).pretty
  unless missing.isEmpty do throwError m!"RAW_VALUE_PATHS_MISSING {missing}"
  let mut publicRows : Array Json := #[]
  for mouth in #[`CPS1MaterialIncidence.NativeBodyFunctionProbe.ChannelRead,`CPS1MaterialIncidence.NativeBodyFunctionProbe.channel_read,`CPS1MaterialIncidence.NativeBodyFunctionProbe.FunctionDisposition,`CPS1MaterialIncidence.NativeBodyFunctionProbe.function_disposition,`CPS1MaterialIncidence.NativeBodyFunctionProbe.DispositionLaw,`CPS1MaterialIncidence.NativeBodyFunctionProbe.disposition_law,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction,`CPS1MaterialIncidence.NativeBodyFunctionProbe.source_generated_native_body_function,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.actual_result,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.actual_execution,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.actual_next,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.next_state,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.next_stock,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.next_history,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.actual_disposition,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.account,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.whole,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.fields,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.electrons,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.invariant,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.genomic_read,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.duties,`CPS1MaterialIncidence.NativeBodyFunctionProbe.NativeBodyFunction.strict_state,`CPS1MaterialIncidence.NativeBodyFunctionProbe.unchanged_state_cannot_be_positive,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.FunctionAtDisposition,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.NativeBodyFunctionRootAt,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.source_generated_native_body_root_function,`SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.source_generated_native_body_after_parent_function] do
    let some info := rawInfo env mouth | throwError m!"RAW_PUBLIC_MOUTH_MISSING {mouth}"
    let mut type := info.type
    let mut binders : Array Json := #[]
    while let .forallE name domain rest binder := type do
      binders := binders.push (Json.mkObj [("name",toJson name.toString),("kind",toJson (reprStr binder)),("type_constants",jsonNames domain.getUsedConstants)])
      type := rest
    publicRows := publicRows.push (Json.mkObj [("mouth",toJson mouth.toString),("binders",.arr binders),("result_constants",jsonNames type.getUsedConstants),("raw_fullparts",toJson true)])
  liftIO <| IO.FS.writeFile (output++".public-mouths.json") (Json.arr publicRows).pretty
  let mut stack := own.map (fun row => row.2.1)
  let mut seen : NameSet := {}
  let mut frontier : NameSet := {}
  let mut axioms : NameSet := {}
  let mut opaqueCount := 0
  let mut edges := 0
  let mut processed := 0
  let graph ← liftIO <| IO.FS.Handle.mk (output++".graph.jsonl") .write
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if !seen.contains name then
      seen := seen.insert name
      if paid.contains name.toString then
        unless (env.getModuleIdxFor? name).isSome do throwError m!"SIGNED_PAID_NAME_NOT_IMPORTED {name}"
        frontier := frontier.insert name
        liftIO <| graph.putStrLn (Json.mkObj [("name",toJson name.toString),("module",toJson (moduleName env name)),("reused",toJson true),("paid_body_walk",toJson false)]).compress
      else
        let some info := rawInfo env name | throwError m!"FRESH_RAW_DECLARATION_MISSING {name}"
        if info.isUnsafe || info.isPartial then throwError m!"FRESH_MATH_UNSAFE_PARTIAL {name}"
        let dependencies := usedConstants info
        liftIO <| graph.putStrLn (Json.mkObj [("name",toJson name.toString),("module",toJson (moduleName env name)),("kind",toJson (kind info)),("dependencies",jsonNames dependencies),("typeDependencies",jsonNames info.type.getUsedConstants),("valueDependencies",jsonNames (usedValues info)),("unsafe",toJson info.isUnsafe),("partial",toJson info.isPartial),("raw_fullparts",toJson true)]).compress
        edges := edges+dependencies.size
        processed := processed+1
        match info with
        | .axiomInfo _ =>
          unless #[`propext,`Classical.choice,`Quot.sound].contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
          axioms := axioms.insert name
        | .opaqueInfo _ =>
          opaqueCount := opaqueCount+1
          unless (info.value? true).isSome do throwError m!"RAW_UNREADABLE_OPAQUE {name}"
        | .defnInfo _ | .thmInfo _ =>
          unless (info.value? true).isSome do throwError m!"RAW_MISSING_VALUE {name}"
        | .recInfo recursor =>
          for rule in recursor.rules do
            let some (.ctorInfo ctor) := rawInfo env rule.ctor | throwError m!"RAW_RULE_CONSTRUCTOR_MISSING {rule.ctor}"
            unless ctor.numFields == rule.nfields do throwError m!"RAW_RULE_CONSTRUCTOR_ARITY {rule.ctor}"
        | _ => pure ()
        for dependency in dependencies do
          if !seen.contains dependency then stack := stack.push dependency
  liftIO <| graph.flush
  for helper in backends do
    if seen.contains helper then throwError m!"OFFICIAL_BACKEND_REACHABLE {helper}"
  if seen.toArray.any (fun name => name.toString == "_private.CPS1ReactiveNuclear.Birth.0.CPS1ReactiveNuclear.bindList._unsafe_rec") then throwError "SIGNED_OLD_BACKEND_REACHABLE"
  let summary := Json.mkObj [("modules",toJson ownerModules.length),("raw",toJson rawOwn.size),("kernel_math_roots",toJson own.size),("visited_new_and_frontier",toJson seen.size),("fresh_declarations",toJson processed),("reused_frontier",jsonNames frontier.toArray),("rechecked_paid_names",jsonNames rechecked),("fresh_edges",toJson edges),("fresh_opaque",toJson opaqueCount),("fresh_axioms",jsonNames axioms.toArray),("value_paths",toJson checks.size),("backends",jsonNames backends),("unsafe",toJson (0 : Nat)),("partial",toJson (0 : Nat)),("unknown",toJson (0 : Nat)),("old_body_walk",toJson (0 : Nat)),("env_checked_proof_bodies",toJson false)]
  liftIO <| IO.FS.writeFile (output++".summary.json") summary.pretty
  progress s!"CERT raw={rawOwn.size} fresh={processed} frontier={frontier.size} edges={edges} readableOpaque={opaqueCount} unsafe=0 partial=0 unknown=0 rawFullparts=true oldBodyWalk=0"
