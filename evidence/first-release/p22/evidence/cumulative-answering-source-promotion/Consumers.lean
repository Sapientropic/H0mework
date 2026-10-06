import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.InquirySource.Consumer
import SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair.InquiryPrograms
import Lean
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.InquirySourceControls
open MotherInquirySource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision
noncomputable section

def Recovered {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt N V) : Prop :=
  ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
    ∃ origin : Origin (rank := rank) state,
      unpackMaterials material = origin.materials ∧
      (unpackMaterials material).current = origin.materials.current ∧
      (unpackMaterials material).u7 =
        (origin.header.demandMaterial, origin.header.eventMaterial, origin.header.compilerMaterial) ∧
      (unpackMaterials material).queries = origin.materials.queries ∧
      (unpackMaterials material).clauses = origin.materials.clauses ∧
      origin.readWorld = ⟨N, V, RootInquiryEngineStateAt.create state⟩ ∧
      (∀ query : origin.readWorld.Query,
        HEq (origin.readWorld.state.base.compileInquiry query)
          (state.compileInquiry (Equiv.cast (congrArg RootInquiryStatePresentation.Query origin.readWorld_eq) query)))

theorem actual_eight_piece_source {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt N V)
    (answering : ∀ query, MotherInquiryAnswerClause.Answering state.calculus query (state.compileInquiry query)) :
    Recovered state := by
  obtain ⟨rank, material, origin, bound, _same, _retained⟩ := every_answering_source N V state answering
  refine ⟨rank, material, origin, bound, ?_, ?_, ?_, ?_, origin.readWorld_eq, origin.compile_recovers⟩
  · exact congrArg Materials.current bound
  · exact (congrArg Materials.u7 bound).trans origin.header_materials
  · exact congrArg Materials.queries bound
  · exact congrArg Materials.clauses bound

theorem original_noninitial_visit10 : Recovered (SpinPair.readInquiryState 10) := by
  apply actual_eight_piece_source
  intro query
  cases query
  trivial

theorem eight_material_slots_faithful {rank : Ordinal.{0}} (first last : Materials rank)
    (different : first ≠ last) : packMaterials first ≠ packMaterials last := by
  intro same
  apply different
  have recovered := congrArg unpackMaterials same
  simpa only [unpack_pack] using recovered

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.InquirySourceControls

open Lean Elab Command
open SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => info.getUsedConstantsAsSet.toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)


run_cmd do
  let env ← getEnv
  for module in env.header.moduleNames do
    if "scratch.".isPrefixOf module.toString then throwError "PRODUCTION_SCRATCH_IMPORT {module}"
  let controls := [``InquirySourceControls.actual_eight_piece_source, ``InquirySourceControls.original_noninitial_visit10, ``InquirySourceControls.eight_material_slots_faithful]
  let closure := recoveryClosure env controls
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "CONTROL_MISSING {name}"
    if info.isUnsafe || info.isPartial then throwError "CONTROL_UNSAFE_PARTIAL {name}"
    edges := edges + info.getUsedConstantsAsSet.size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "CONTROL_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "CONTROL_MISSING_VALUE {name}"
    | _ => pure ()
  for name in controls do
    let used ← collectAxioms name
    logInfo m!"CONTROL {name} axioms={used}"
  logInfo m!"CONTROLS_PASS count={controls.length} closure={closure.size} edges={edges} axioms={axioms.toArray} unsafe=0 partial=0"
