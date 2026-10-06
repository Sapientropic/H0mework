import H0mework.Versions.AE.Physics.Bell.SourceHistory
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistoryCertification

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
open Stage9C.Revision StageNineHolonomicField ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open SourceUniqueness

noncomputable section

theorem exactOriginalSource :
    Runtime.source = positiveSmoothUnifiedSource ∧
    SourceHistory.visitAt 0 = Runtime.visit ∧ SourceHistory.eventAt 0 = Runtime.event :=
  ⟨Runtime.source_eq, SourceHistory.original_visit, SourceHistory.original_event⟩

theorem completeOriginalHistory (stage : Nat) :
    (SourceHistory.commonAt stage).map Prod.fst =
      (ActualFormation.historyLaw.historyAt Runtime.event.occurrence).observation stage :=
  SourceHistory.whole_history_read stage

theorem originalHistoryFrontier (stage : Nat) :
    ((ActualFormation.historyLaw.historyAt Runtime.event.occurrence).observation stage).frontier =
      [.generator (SourceHistory.generatorAt stage)] :=
  SourceHistory.history_frontier stage

theorem allPhysicalFields (stage : Nat) :
    SourceHistory.fieldAt stage = Recognition.wholeField (SourceHistory.currentAt stage) :=
  SourceHistory.full_field_read stage

theorem originalConstructor (stage : Nat) :
    (SourceHistory.readAt stage).1 = SourceHistory.constructorCode (SourceHistory.currentAt stage) :=
  SourceHistory.constructor_read stage

theorem modelUsesActualAction (stage : Nat) :
    modelAction ActualFormation.nativeAction SourceHistory.fullObservation (SourceHistory.modelAt stage) =
      SourceHistory.modelAt (stage + 1) :=
  SourceHistory.model_action_next stage

theorem integralWordFutureFibre (left right : ActualFormation.IntegralCarrier) :
    projection ActualFormation.nativeAction SourceHistory.fullObservation left =
      projection ActualFormation.nativeAction SourceHistory.fullObservation right ↔
      ∀ stage : Nat,
        SourceHistory.fullObservation ((ActualFormation.nativeAction ^ stage) left) =
          SourceHistory.fullObservation ((ActualFormation.nativeAction ^ stage) right) :=
  SourceHistory.complete_history_fibre left right

theorem integralWordJointFibre (left right : ActualFormation.IntegralCarrier) :
    canonicalResidual SourceHistory.currentNextObservation left =
      canonicalResidual SourceHistory.currentNextObservation right ↔
      SourceHistory.fullObservation left = SourceHistory.fullObservation right ∧
        SourceHistory.fullObservation (ActualFormation.nativeAction left) =
          SourceHistory.fullObservation (ActualFormation.nativeAction right) :=
  SourceHistory.joint_observation_fibre left right

theorem nativeModelRestoresCurrent {left right : SpinPair.Current}
    (same : projection ActualFormation.nativeAction SourceHistory.fullObservation
      (ActualFormation.event (0, left)) =
      projection ActualFormation.nativeAction SourceHistory.fullObservation
        (ActualFormation.event (0, right))) : left = right :=
  (SourceHistory.complete_model_determines_step same).1

theorem nativeJointRestoresAllOutputs {left right : SpinPair.Current}
    (same : canonicalResidual SourceHistory.currentNextObservation (ActualFormation.event (0, left)) =
      canonicalResidual SourceHistory.currentNextObservation (ActualFormation.event (0, right))) :
    left = right ∧ SpinPair.next left = SpinPair.next right ∧
      HEq (SpinPair.generatedEvolution (SpinPair.emitted left))
        (SpinPair.generatedEvolution (SpinPair.emitted right)) ∧
      ∀ coordinate : SpinPair.Projection,
        HEq (SpinPair.authoritativeRoot.projectionOutcomeAt coordinate left)
          (SpinPair.authoritativeRoot.projectionOutcomeAt coordinate right) :=
  SourceHistory.joint_model_determines_step same

theorem actualJointActionRetainsIncidence (stage : Nat) :
    ActualFormation.jointEvent (SourceHistory.generatorAt (stage + 1)) =
      ActualFormation.jointInput.omega (ActualFormation.jointEvent (SourceHistory.generatorAt stage)) -
        ActualFormation.jointInput.incidenceResidual (ActualFormation.event (SourceHistory.generatorAt stage)) :=
  SourceHistory.joint_action_next stage

theorem entireOriginalLedger (stage : Nat) :
    HEq (SourceHistory.eventAt stage).wholeLedgerWriteBack
      (SpinPair.generatedEvolution (SpinPair.emitted (SourceHistory.currentAt stage))) :=
  SourceHistory.original_whole_ledger stage

theorem allInstalledOutputs (stage : Nat) (coordinate : SpinPair.Projection) :
    HEq ((SourceHistory.eventAt stage).projectionOutcome coordinate)
      (SpinPair.authoritativeRoot.projectionOutcomeAt coordinate (SourceHistory.currentAt stage)) :=
  SourceHistory.original_installed_projection stage coordinate

theorem originalMacroNext : Runtime.tick.next.node.erase =
    ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit⟩ :=
  SourceHistory.original_macro_next

theorem originalCurrentNextBorn (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) :
    SourceHistory.bornAt 0 plus point a b x y = runtimeProbability plus point a b x y ∧
      SourceHistory.bornAt 1 plus point a b x y = nextProbability plus point a b x y :=
  ⟨SourceHistory.current_born_commutes plus point a b x y,
    SourceHistory.next_born_commutes plus point a b x y⟩

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistoryCertification

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let candidate := `H0mework.Versions.AE.Physics.Bell.SourceHistory
  let some candidateIndex := env.getModuleIdx? candidate |
    throwError "source-history candidate module absent"
  let mut owned : Array Name := #[]
  let mut compilerOnly : Array Name := #[]
  for (name, index) in env.const2ModIdx.toList do
    if index == candidateIndex then
      if (env.find? name).isSome then owned := owned.push name
      else compilerOnly := compilerOnly.push name
  let consumerPrefix := `SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistoryCertification
  let consumers := env.constants.toList.toArray.filterMap fun (name, _) =>
    if consumerPrefix.isPrefixOf name then some name else none
  if owned.isEmpty || consumers.isEmpty then throwError "empty source-history audit"
  let mut kernelOwned : Array Name := #[]
  let mut runtimeHelpers : Array Name := #[]
  for name in owned do
    let some info := env.find? name | throwError "owned source-history declaration missing"
    match info with
    | .defnInfo value =>
      if value.safety != .safe then
        unless name.toString.endsWith "._unsafe_rec" do
          throwError "unexpected unsafe source-history declaration: {name}"
        runtimeHelpers := runtimeHelpers.push name
      else kernelOwned := kernelOwned.push name
    | _ => kernelOwned := kernelOwned.push name
  let mut declarations : Array Json := #[]
  for name in kernelOwned ++ consumers do
    let some info := env.find? name | throwError "owned source-history declaration missing"
    for helper in runtimeHelpers do
      if info.getUsedConstantsAsSet.contains helper then
        throwError "logical source-history declaration references runtime helper: {name}: {helper}"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo value => if value.safety == .safe then "definition" else "unsafe-definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    if kind == "unsafe-definition" then throwError "unsafe source-history declaration: {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound do
        throwError "unauthorized source-history axiom: {name}: {axiomName}"
    declarations := declarations.push (Json.mkObj [("name", .str name.toString), ("kind", .str kind),
      ("axioms", .arr (axioms.map fun value => .str value.toString))])
  let mouths := #[
    `SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistory.complete_model_determines_step,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistory.joint_model_determines_step,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistory.complete_history_fibre,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistory.joint_observation_fibre]
  let mut publicMouths : Array Json := #[]
  for name in mouths do
    let some info := env.find? name | throwError "source-history mouth missing"
    let pretty ← liftTermElabM <| Meta.ppExpr info.type
    publicMouths := publicMouths.push (Json.mkObj [("name", .str name.toString), ("type", .str pretty.pretty)])
  logInfo m!"BELL_SOURCE_HISTORY_AUDIT|{(Json.mkObj [
    ("candidate_module", .str candidate.toString),
    ("owned_declarations", .arr (kernelOwned.map fun name => .str name.toString)),
    ("compiler_only_module_symbols", .arr (compilerOnly.map fun name => .str name.toString)),
    ("compiler_runtime_helpers", .arr (runtimeHelpers.map fun name => .str name.toString)),
    ("compiler_runtime_helpers_absent_from_logical_type_value_dependencies", .bool true),
    ("independent_consumers", .arr (consumers.map fun name => .str name.toString)),
    ("declaration_axioms", .arr declarations), ("public_mouths", .arr publicMouths)]).compress}"
