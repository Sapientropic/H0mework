import H0mework.Papers.WholeLedgerAccountingR453de275
import Lean

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Lean Elab Command
private def releaseName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.type.getUsedConstantsAsSet ++ info.getUsedConstantsAsSet
  if let some value := info.value? true then refs := refs ++ value.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := refs.insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => (completeRefs info).toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let roots : List (String × String) := [("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.Law", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.faithfulLaw", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.generated_event_ledger_next", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.generated_recovery_or_residual", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionConsumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.generated_single_equation", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.historyLaw", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.materialInstallation", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.materialLivingRoot", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.materialRoot", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.materialSource", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.raw_action_eq_event", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.receiptFromCompiler", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.receiptFromCompiler_eq_event", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.recognition", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.residualRoot", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.CofinalAction.same_lower_root", "H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction")]
  for (decl, owner) in roots do
    let name := releaseName decl
    unless (env.checked.get.find? name).isSome do throwError "MISSING_DECLARATION {name}"
    let some index := env.getModuleIdxFor? name | throwError "MISSING_DECLARATION_MODULE {name}"
    unless env.header.moduleNames[index]! == releaseName owner do
      throwError "WRONG_DECLARATION_MODULE {name} expected={owner} actual={env.header.moduleNames[index]!}"
  let closure := recoveryClosure env (roots.map fun item => releaseName item.1)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED_CONSTANT {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAPPROVED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_CONSTANT_VALUE {name}"
    | _ => pure ()
  let report := Json.mkObj [
    ("token", toJson "8e60fcefe302f9c445dc504956e145654ffb98a85986fdfc8e4c393e403a0a80"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
