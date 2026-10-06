import H0mework.Papers.ConstrainedLocalQuantumV
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
  let roots : List (String × String) := [("LowEnergy.AntiunitaryDefectPair.DomainSymmetry", "H0mework.Physics.LowEnergy.Quantum.AntiunitaryDefectPair"),
    ("LowEnergy.AntiunitaryDefectPair.DomainSymmetry.symm", "H0mework.Physics.LowEnergy.Quantum.AntiunitaryDefectPair"),
    ("LowEnergy.AntiunitaryDefectPair.antiunitary_inner", "H0mework.Physics.LowEnergy.Quantum.AntiunitaryDefectPair"),
    ("LowEnergy.AntiunitaryDefectPair.defectEquiv", "H0mework.Physics.LowEnergy.Quantum.AntiunitaryDefectPair"),
    ("LowEnergy.AntiunitaryDefectPair.defectEquiv_apply", "H0mework.Physics.LowEnergy.Quantum.AntiunitaryDefectPair"),
    ("LowEnergy.AntiunitaryDefectPair.defectSpace", "H0mework.Physics.LowEnergy.Quantum.AntiunitaryDefectPair"),
    ("LowEnergy.AntiunitaryDefectPair.maps_defect", "H0mework.Physics.LowEnergy.Quantum.AntiunitaryDefectPair"),
    ("LowEnergy.AntiunitaryDefectPair.mem_defect_iff_adjoint", "H0mework.Physics.LowEnergy.Quantum.AntiunitaryDefectPair"),
    ("LowEnergy.SecondClassReduction.constraintMatrix", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SecondClassReduction.constraint_determinant", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SecondClassReduction.constraint_measure_cancellation", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SecondClassReduction.constraint_mul_inverse", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SecondClassReduction.diracInverse", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SecondClassReduction.inverse_mul_constraint", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SecondClassReduction.remaining_dirac_bracket", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SecondClassReduction.remaining_dirac_correction_zero", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SecondClassReduction.second_class_measure_cancellation", "H0mework.Physics.LowEnergy.Quantum.SecondClassReduction"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.Coframe", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.Configuration", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.FockHilbert", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.Gauge", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.Mode", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.Occupation", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.SectorHilbert", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.chart", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.chartMeasure", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.coframeMeasure", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.coframeVolume", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.coframeVolume_continuous", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.coframeVolume_pos", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.configurationMeasure", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.configuration_finrank", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.fockTestDomain", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.fockTestDomain_dense", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.full_mode_card", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.gaugeMeasure", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.gauge_finrank", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.numberMeasure", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.numberWeight", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.numberWeight_continuous", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.numberWeight_pos", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.sourceCoframe", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.sourceCoframe_eq", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.sourceGauge", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.sourcePoint", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.source_weight_one", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.testDomain", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumConfigurationHilbert.testDomain_dense", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumConfigurationHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.BaseHilbert", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.FlatFockHilbert", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.divideHalf", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.divideHalf_memLp", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.eLpNorm_multiplyHalf", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.fockHalfDensityEquiv", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.fockHalfDensityEquiv_apply", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensity", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensityEquiv", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensityMap", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensityMap_apply", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensityMap_surjective", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensity_continuous", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensity_enorm_sq", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensity_pos", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.halfDensity_sq", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.multiplyHalf", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.multiplyHalf_memLp", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.multiply_divideHalf", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.source_halfDensity_one", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.weight_measurable", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SourceQuantumHalfDensityHilbert.weighted_null_sets", "H0mework.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert"),
    ("LowEnergy.SymmetricGraphClosure.FormalAdjointPair", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.closedExtension", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.closedGraph", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.closed_extension_graph", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.closed_extension_isClosed", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.closed_graph_pairing", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.closed_graph_single_valued", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.closed_graph_zero_fiber", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.extends_original", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.minimal_closed_extension", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.symmetric_zero_sequence_limit", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("LowEnergy.SymmetricGraphClosure.zero_sequence_limit", "H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure"),
    ("SourceFockFilteredWords.homogeneous_eigenstate", "H0mework.Physics.LowEnergy.Quantum.FockFilteredWords"),
    ("SourceFockFilteredWords.weight", "H0mework.Physics.LowEnergy.Quantum.FockFilteredWords"),
    ("SourceFockFilteredWords.weighted_tensor_word_vanishes", "H0mework.Physics.LowEnergy.Quantum.FockFilteredWords"),
    ("SourceFockFilteredWords.weighted_word_vanishes", "H0mework.Physics.LowEnergy.Quantum.FockFilteredWords"),
    ("SourceFockFilteredWords.word_eigenstate", "H0mework.Physics.LowEnergy.Quantum.FockFilteredWords")]
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
    ("token", toJson "844b3e0f11bc6f30cee167556a9638cb8ba82bee88758fc3e730f18f99bfae41"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
