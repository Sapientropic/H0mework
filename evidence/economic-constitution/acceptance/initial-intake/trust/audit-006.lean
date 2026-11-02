import H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer
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
  let roots : List (String × String) := [("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case001", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case002", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case003", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case004", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case005", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case006", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case007", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case008", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case009", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case010", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case011", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case012", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case013", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case014", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case015", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case016", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case017", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case018", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case019", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case020", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case021", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case022", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case023", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case024", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case025", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case026", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case027", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case028", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case029", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case030", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case031", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case032", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case033", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case034", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case035", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case036", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case037", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case038", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case039", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case040", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case041", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case042", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case043", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case044", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case045", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case046", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case047", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case048", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case049", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case050", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case051", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case052", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case053", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case054", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case055", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case056", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case057", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer"),
    ("H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case058", "H0mework.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer")]
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
    ("token", toJson "29265a778a8fea3faf1073ec1fda90f21296913f31d94031e04232e0694d6e4b"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
