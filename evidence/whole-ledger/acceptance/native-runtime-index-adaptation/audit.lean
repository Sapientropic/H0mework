import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeRuntimeFace.Source
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

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal

private def sameInfo (a b : ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo x, .axiomInfo y => x == y
  | .defnInfo x, .defnInfo y => x == y
  | .thmInfo x, .thmInfo y => x == y
  | .opaqueInfo x, .opaqueInfo y => x == y
  | .quotInfo x, .quotInfo y => x == y
  | .inductInfo x, .inductInfo y => x == y
  | .ctorInfo x, .ctorInfo y => x == y
  | .recInfo x, .recInfo y => x == y
  | _, _ => false

run_cmd do
  let env ← getEnv
  let module := releaseName "H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeRuntimeFace.Source"
  let component := "OriginalKNativeRuntimeFace"
  unless (Lean.LibrarySuggestions.nameDenyListExt.getState env).contains component do
    throwError "MISSING_IMPORTED_INDEX_EXCLUSION"
  let mut roots : List Name := []
  let mut theoremRoots := 0
  let mut outsideComponent : List String := []
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index]! == module do continue
    roots := name :: roots
    unless name.anyS (· == component) do
      outsideComponent := name.toString :: outsideComponent
    if info matches .thmInfo _ then
      theoremRoots := theoremRoots + 1
      unless Lean.LibrarySuggestions.isDeniedPremise env name do
        throwError "THEOREM_INDEX_EXCLUSION_NOT_ACTIVE {name}"
  if roots.isEmpty then throwError "EMPTY_SOURCE_OWNERSHIP"
  unless outsideComponent.isEmpty do
    throwError "SOURCE_DECLARATIONS_OUTSIDE_EXACT_COMPONENT {outsideComponent}"
  let closure := recoveryClosure env roots
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
  let updated := Lean.LibrarySuggestions.nameDenyListExt.addEntry env component
  let constants := env.constants.toList
  let updatedConstants := updated.constants.toList
  unless constants.length == updatedConstants.length do
    throwError "INDEX_EXTENSION_CHANGED_CONSTANT_COUNT"
  for (name, info) in constants do
    let some newInfo := updated.checked.get.find? name |
      throwError "INDEX_EXTENSION_REMOVED_CONSTANT {name}"
    unless sameInfo info newInfo do
      throwError "INDEX_EXTENSION_CHANGED_CONSTANT_METADATA {name}"
  let positive := releaseName "Example.OriginalKNativeRuntimeFace.actual_source_input"
  let nearSuffix := releaseName "Example.OriginalKNativeRuntimeFaceOther.actual_source_input"
  let nearPrefix := releaseName "Example.OtherOriginalKNativeRuntimeFace.actual_source_input"
  unless positive.anyS (· == component) do throwError "EXACT_COMPONENT_POSITIVE_FAILURE"
  if nearSuffix.anyS (· == component) || nearPrefix.anyS (· == component) then
    throwError "EXACT_COMPONENT_NEAR_NAME_FAILURE"
  let rows := roots.map fun name =>
    let info := (env.checked.get.find? name).get!
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    Json.mkObj [("qualified_name", toJson name.toString), ("kind", toJson kind)]
  let report := Json.mkObj [
    ("module", toJson module.toString), ("roots", toJson roots.length),
    ("theorem_roots", toJson theoremRoots), ("constants", toJson closure.size),
    ("edges", toJson edges), ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true), ("extension_active", toJson true),
    ("extension_constant_count", toJson constants.length),
    ("extension_constant_metadata_unchanged", toJson true),
    ("exact_component_positive", toJson true),
    ("similar_suffix_rejected", toJson true), ("similar_prefix_rejected", toJson true),
    ("owned_declarations", toJson rows)]
  logInfo m!"NATIVE_INDEX_LOGICAL_AUDIT {report.compress}"
