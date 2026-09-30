import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Copy.Graph.Consumer
import Lean

open Lean Elab Command

private def countedPrefix := "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceCountedObservation."
private def modulePrefix := "SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory."

private def walk (env : Environment) (roots : Array Name) (includeTypes : Bool) : IO (Std.HashSet Name) := do
  let mut pending := roots
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throw <| IO.userError s!"missing declaration: {name}"
    if includeTypes then pending := pending ++ info.type.getUsedConstants
    if let some value := info.value? true then pending := pending ++ value.getUsedConstants
  return seen

run_cmd do
  let env ← getEnv
  let mut owned := #[]
  let mut frontiers := #[]
  let mut modules : Std.HashSet Nat := {}
  let mut calculation := 0
  for index in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[index]!.toString
    if moduleName.startsWith (modulePrefix ++ "Conditional.CountedObservation.") ||
        moduleName.startsWith (modulePrefix ++ "Conditional.CountedRecovery.") ||
        moduleName.startsWith (modulePrefix ++ "Conditional.CountedPosterior.") ||
        moduleName.startsWith (modulePrefix ++ "Conditional.CountedAdvance.") ||
        moduleName.startsWith (modulePrefix ++ "Conditional.CountedMerge.") ||
        moduleName == modulePrefix ++ "Conditional.NativeKeys.Material" then
      modules := modules.insert index
    if moduleName == modulePrefix ++ "Copy.Graph.NativeModelStep.Calculation" then
      calculation := index
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if modules.contains index.toNat then
        owned := owned.push name
      if index.toNat == calculation &&
          name.toString.endsWith ".sourceFrontier" then frontiers := frontiers.push name
  unless !owned.isEmpty && frontiers.size == 1 do throwError "missing owned declarations or source frontier"
  liftIO <| IO.println s!"owned declarations: {owned.size}"
  let closure ← liftIO <| walk env owned true
  liftIO <| IO.println s!"type and value closure: {closure.size}"
  let mut axioms := #[]
  for name in closure.toArray do
    let some info := env.find? name | throwError "missing {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe/partial dependency: {name}"
    if name.toString.startsWith "scratch." || name.toString.contains "ofReduceBool" ||
        name.toString.contains "sorryAx" then throwError "untrusted dependency: {name}"
    if let .axiomInfo _ := info then
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains name do
        throwError "unauthorized axiom: {name}"
      axioms := axioms.push name.toString
  let constructorNames := #["coordinate", "grow", "addAt", "encode", "advance", "decode",
    "collect", "fromInventory", "lookup", "step", "run", "total", "weight",
    "readValue", "mixedValue", "observationTable"]
  let forbidden := #[".SourceConditionalNativeObservers.generate",
    ".SourceRationalWindowReadout.recover", ".SourcePosteriorStability.restoredSupport",
    ".SourceWindowPosterior.model", ".SourceConditionalNativePosterior.decoder",
    ".SourceCountedObservation.Simulates", ".SourceCountedObservation.received_simulates",
    ".SourceCountedObservation.readValue_source", ".SourceCountedObservation.conditional_error",
    ".SourceCountedObservation.field_balance", ".SourceCountedRecovery.error_update",
    ".SourceCountedRecovery.field_update"]
  let mut heads := #[]
  for short in constructorNames do
    let head := (countedPrefix ++ short).toName
    unless env.contains head do throwError "missing constructor/readout: {head}"
    heads := heads.push head
  let values ← liftIO <| walk env heads false
  for name in values.toArray do
    if forbidden.any (fun suffix => name.toString.endsWith suffix) then
      throwError "source/query/target in constructor or readout value path: {name}"
  liftIO <| IO.println s!"constructor/readout value closure: {values.size}"
  let posteriorPrefix := "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceCountedPosterior."
  let posteriorHeads := #["restore", "model"].map (fun short => (posteriorPrefix ++ short).toName)
  for head in posteriorHeads do
    unless env.contains head do throwError "missing posterior constructor: {head}"
  let posteriorValues ← liftIO <| walk env posteriorHeads false
  let posteriorForbidden := #[".SourceConditionalNativeObservers.generate", ".SourceConditionalNativePosterior.model",
    ".SourceConditionalNativePosterior.decoder", ".SourceRetainedReceiver.start",
    ".SourceCountedPosterior.restored_source", ".SourceCountedPosterior.model_source",
    ".SourceCountedPosterior.continued_source", ".SourceCountedPosterior.continued_model"]
  for name in posteriorValues.toArray do
    if posteriorForbidden.any (fun suffix => name.toString.endsWith suffix) then
      throwError "source answer in posterior constructor: {name}"
  unless posteriorValues.contains
      ``SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceFibreExactState.restore do
    throwError "posterior constructor bypasses the existing restore"
  let advancePrefix := "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceCountedAdvance."
  let advanceHeads := #["samples", "next", "nextModel"].map (fun short => (advancePrefix ++ short).toName)
  for head in advanceHeads do
    unless env.contains head do throwError "missing autonomous next constructor: {head}"
  let advanceValues ← liftIO <| walk env advanceHeads false
  for name in advanceValues.toArray do
    if posteriorForbidden.any (fun suffix => name.toString.endsWith suffix) ||
        (name.toString.startsWith advancePrefix &&
          #[".next_source", ".step_commutes", ".next_model_source", ".step_model_commutes",
            ".continued_next", ".continued_model", ".next_field_balance", ".continued_next_field"].any
              (fun suffix => name.toString.endsWith suffix)) then
      throwError "source answer in autonomous next constructor: {name}"
  for required in #[
      ``SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceFibreExactState.restore,
      ``SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceFibreExactState.next,
      ``SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceFibreExactState.nextModel,
      ``SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceConditionalNativeObservers.advance] do
    unless advanceValues.contains required do throwError "autonomous next bypasses existing action: {required}"
  let mergePrefix := "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceCountedMerge."
  let mergeHeads := #["capacity", "mergeEntry", "mergeTable", "observationTable"].map
    (fun short => (mergePrefix ++ short).toName)
  for head in mergeHeads do
    unless env.contains head do throwError "missing counted coarsening constructor: {head}"
  let mergeValues ← liftIO <| walk env mergeHeads false
  for name in mergeValues.toArray do
    if forbidden.any (fun suffix => name.toString.endsWith suffix) ||
        posteriorForbidden.any (fun suffix => name.toString.endsWith suffix) ||
        #[".SourceRetainedCoarsening.merge", ".SourceFibreExactState.restore",
          ".SourceCountedPosterior.restore", ".SourceCountedMerge.merge_simulates",
          ".SourceCountedMerge.continued_source", ".SourceCountedMerge.continued_next_model",
          ".SourceCountedMerge.continued_next_field"].any (fun suffix => name.toString.endsWith suffix) then
      throwError "source/frame/recovery answer in counted coarsening constructor: {name}"
  let frontier ← liftIO <| walk env frontiers true
  for name in frontier.toArray do
    if name.toString.startsWith countedPrefix &&
        #[".stage_law", ".received_simulates", ".conditional_error", ".field_balance",
          ".readValue_source"].any (fun suffix => name.toString.endsWith suffix) then
      throwError "output proof in source frontier: {name}"
    if #[".SourceCountedRecovery.error_update", ".SourceCountedRecovery.field_update"].any
        (fun suffix => name.toString.endsWith suffix) then
      throwError "recovery output proof in source frontier: {name}"
    if name.toString.startsWith posteriorPrefix &&
        #[".restored_source", ".model_source", ".continued_source", ".continued_model", ".field_balance",
          ".field_update", ".continued_field_update", ".continued_field_balance"].any
          (fun suffix => name.toString.endsWith suffix) then
      throwError "posterior output proof in source frontier: {name}"
    if name.toString.startsWith advancePrefix &&
        #[".next_source", ".step_commutes", ".next_model_source", ".step_model_commutes",
          ".continued_next", ".continued_model", ".next_field_balance", ".continued_next_field"].any
            (fun suffix => name.toString.endsWith suffix) then
      throwError "autonomous next output proof in source frontier: {name}"
    if name.toString.startsWith mergePrefix &&
        #[".merge_simulates", ".next_simulates", ".initial_half_margin", ".trajectory_half_margin",
          ".continued_source", ".continued_next_model", ".next_field_balance", ".next_observation",
          ".continued_next_field", ".continued_next_table_loss",
          ".continued_next_table_strict"].any (fun suffix => name.toString.endsWith suffix) then
      throwError "counted coarsening output proof in source frontier: {name}"
  let sorted := (owned.map toString).qsort (· < ·)
  let mut types := #[]
  for name in sorted do
    let some info := env.find? name.toName | throwError "missing {name}"
    types := types.push s!"{name}\n{hash info.type}"
  let directory := (← liftIO <| IO.getEnv "COUNTED_AUDIT_DIR").getD "/tmp/counted-observation-audit"
  liftIO <| IO.FS.createDirAll directory
  liftIO <| IO.FS.writeFile (directory ++ "/types.txt") (String.intercalate "\n\n" types.toList)
  liftIO <| IO.FS.writeFile (directory ++ "/values.txt")
    (String.intercalate "\n" ((values.toArray.map toString).qsort (· < ·)).toList)
  liftIO <| IO.FS.writeFile (directory ++ "/closure.txt")
    (String.intercalate "\n" ((closure.toArray.map toString).qsort (· < ·)).toList)
  liftIO <| IO.FS.writeFile (directory ++ "/posterior-values.txt")
    (String.intercalate "\n" ((posteriorValues.toArray.map toString).qsort (· < ·)).toList)
  liftIO <| IO.FS.writeFile (directory ++ "/advance-values.txt")
    (String.intercalate "\n" ((advanceValues.toArray.map toString).qsort (· < ·)).toList)
  liftIO <| IO.FS.writeFile (directory ++ "/merge-values.txt")
    (String.intercalate "\n" ((mergeValues.toArray.map toString).qsort (· < ·)).toList)
  logInfo m!"COUNTED_GATE_PASS owned={owned.size} closure={closure.size} values={constructorNames.size} axioms={axioms.qsort (· < ·)} frontier=source-only"
