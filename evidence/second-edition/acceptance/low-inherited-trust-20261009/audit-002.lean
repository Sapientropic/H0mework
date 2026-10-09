import H0mework.Papers.LowEnergyLoopResponse
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
  let roots : List (String × String) := [("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Arrow", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Arrow.add", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Arrow.compose_zero", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Arrow.diagonal_left", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Arrow.diagonal_right", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Arrow.smul", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Arrow.sub", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Arrow.zero", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Consumer.actual_regular_loop_exists", "H0mework.Checks.Physics.LowEnergy.ClosedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Consumer.actual_whole_word_readback", "H0mework.Checks.Physics.LowEnergy.ClosedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion.arrow_left", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion.arrow_right", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion.mul", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion.one", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion.product", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion.refl", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion.smul", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Expansion.sub", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.GaugeLine", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.GaugeLine.Regular", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.GaugeLine.diagonal", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.GaugeLine.full", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.GaugeLine.generated", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.GaugeLine.propagator", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.arrow_trace", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.expansion_trace", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.freeDiracResolvent", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.gauge_loop_independent_yukawa", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.gauge_word_generated", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.loopTrace", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.loopTrace_mul_comm", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.ordered_loop", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.ordered_loop_with_arrow", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.original_gauge_vertex", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.original_principal_inverse", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.original_scalar_vertex", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.scalar_insertion_closed_loop", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.six", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Grading"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.source_diracResolvent", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.source_hamiltonian", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.source_resolvent", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.source_variation", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.two_scalar_open_chain", "H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer.actual_scalar_weighted_zero", "H0mework.Checks.Physics.LowEnergy.PreparedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer.actual_unit_word", "H0mework.Checks.Physics.LowEnergy.PreparedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer.actual_weight_is_not_bare_trace", "H0mework.Checks.Physics.LowEnergy.PreparedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer.native_weighted_all_words", "H0mework.Checks.Physics.LowEnergy.PreparedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer.original_return_stays_visible", "H0mework.Checks.Physics.LowEnergy.PreparedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer.source_reader_raw_identity", "H0mework.Checks.Physics.LowEnergy.PreparedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer.source_scalar_transfer_vanishes", "H0mework.Checks.Physics.LowEnergy.PreparedLoops.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.SourceStep", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.SourceStep.line", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.SourceStep.regular", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.arrow_prepared_zero", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.boundary_grade", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.complete_word_expansion", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.diagonalSteps", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.expansion_prepared", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.fullSteps", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.fullWord", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.fullWord_oneParticle", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.fullWord_read", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.native_transfer_yukawa_independent", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.prepared_matrix_pair", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.prepared_six_read", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.scalarForce", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Scalar"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.scalarForce_arrow", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Scalar"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.scalarReader", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Scalar"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.scalarReader_arrow", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Scalar"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.sourceForce", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.sourceForce_grade", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.sourceReader", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.sourceReader_grade", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.sourceReader_original", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.source_scalar_Stage10", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.source_scalar_gauge_transfer_zero", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Scalar"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.source_scalar_weighted_word", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.source_weighted_Stage10", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.source_weighted_yukawa_independent", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.steps_generated", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.transferRead", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.transferRead_expansion", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.transferRead_generated", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Transfer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.transferRead_scalar_force_zero", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Scalar"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.transferRead_scalar_reader_zero", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Scalar"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.weightedWord", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.weightedWord_expansion", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.weightedWord_native", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Words"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.weighted_arrow_zero", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.weighted_expansion", "H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Source")]
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
    ("token", toJson "028bb85d23cfb3eb02c8f73612a1e8d2049edc0a7843e6a99b2d008f1a151af3"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
