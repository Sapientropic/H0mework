import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.AdmittedWorld.Consumer
import SaturationMonoid.LivingLawRootTemporalAnswerNextRegression
import SaturationMonoid.LivingLawRootAnswerNextRegression
import SaturationMonoid.PhysicsCore.Stage10.Runtime.Activation
import Lean
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AdmittedWorldControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot ZeroLawRootAdmission
open MotherAdmittedWorld RootTemporalAnswerNextRegression
open SourceNativeLedgerCompilerRegression SourceNativeRootAuthorityRegression
noncomputable section

universe u

theorem generic_universe_visit_material {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) (visit : SourceNativeTemporalVisitAt root)
    (rank : Ordinal.{0}) :
    ∃ material : MotherArenaHigher.Material rank, formVisit root material = some visit :=
  every_visit_material root visit

def Produced {N : WorldRelationNetwork.{0}} (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) (state : LawfulWorldStateAt root) : Prop :=
  ∃ origin : Origin (⟨V, root, state⟩ : StateAt N),
    origin.world = ⟨N, V, root, state⟩ ∧
    origin.read = ⟨V, root, state⟩ ∧
    formState origin.presentation.restrictHeader (MotherArenaHigher.split origin.rank origin.material).2 = some origin.read ∧
    HEq origin.read.2.2.registeredOccurrence state.registeredOccurrence ∧
    HEq origin.read.2.2.authoritativeEvolution state.authoritativeEvolution ∧
    HEq origin.read.2.2.positiveDisposition state.positiveDisposition ∧
    HEq origin.read.2.2.registeredOccurrence.2.priorPatches state.registeredOccurrence.2.priorPatches ∧
    HEq origin.read.2.2.registeredOccurrence.2.currentPatch state.registeredOccurrence.2.currentPatch ∧
    HEq origin.read.2.2.registeredOccurrence.2.wholeLedgerWriteBack state.registeredOccurrence.2.wholeLedgerWriteBack ∧
    HEq (advance origin.read.2.1.toLedgerRoot origin.read.2.2) (advance root.toLedgerRoot state) ∧
    TotalReality.TotalRealityAt (RootTotalReality.semantics origin.read.2.1) ∧
    Function.LeftInverse (MotherArenaHigher.restrictOriginal origin.rank origin.originalAddress)
      (MotherArenaHigher.includeOriginal origin.rank origin.originalAddress)

theorem complete_general_authoritative_world {N : WorldRelationNetwork.{0}} (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) (state : LawfulWorldStateAt root) : Produced V root state := by
  obtain ⟨origin, world, _occurrence, _evolution, _disposition, _ledger, _next, total⟩ := every_admitted_world N V root state
  obtain ⟨occurrence, evolution, disposition, prior, patch, ledger, _next, advanced⟩ := origin.consumers_recovers
  exact ⟨origin, world, origin.read_eq, (Option.some_get _).symm, occurrence, evolution,
    disposition, prior, patch, ledger, advanced, total, origin.originalRetained⟩

theorem recurrent_histories_remain_distinct :
    ∃ first : Origin (⟨V, livingRoot.toAuthoritativeRoot, .finite recurrentFirstVisit⟩ : StateAt N),
    ∃ last : Origin (⟨V, livingRoot.toAuthoritativeRoot, .finite recurrentSecondVisit⟩ : StateAt N),
      first.read ≠ last.read ∧
      Produced V livingRoot.toAuthoritativeRoot (.finite recurrentFirstVisit) ∧
      Produced V livingRoot.toAuthoritativeRoot (.finite recurrentSecondVisit) := by
  obtain ⟨first⟩ := every_state N (⟨V, livingRoot.toAuthoritativeRoot, .finite recurrentFirstVisit⟩ : StateAt N)
  obtain ⟨last⟩ := every_state N (⟨V, livingRoot.toAuthoritativeRoot, .finite recurrentSecondVisit⟩ : StateAt N)
  refine ⟨first, last, ?_, complete_general_authoritative_world _ _ _, complete_general_authoritative_world _ _ _⟩
  intro same
  have worlds := first.read_eq.symm.trans (same.trans last.read_eq)
  have roots := eq_of_heq (Sigma.mk.inj_iff.mp worlds).2
  have visits := eq_of_heq (Sigma.mk.inj_iff.mp roots).2
  exact recurrent_visits_are_distinct (SourceNativeTemporalVisitAt.finite_injective visits)

theorem cofinal_and_post_cofinal_whole_worlds :
    formCofinal livingRoot.toAuthoritativeRoot.toLedgerRoot = some cofinalVisit ∧
    Produced V livingRoot.toAuthoritativeRoot temporalVisit ∧
    Produced V livingRoot.toAuthoritativeRoot (temporalVisit.next rfl) ∧
    advance livingRoot.toAuthoritativeRoot.toLedgerRoot temporalVisit = some (temporalVisit.next rfl) :=
  ⟨formCofinal_recovers _ _, complete_general_authoritative_world _ _ _,
    complete_general_authoritative_world _ _ _, advance_recovers _ _ rfl⟩

theorem original_spin_pair_complete_world :
    Produced Stage9C.Revision.SpinPair.V Stage9C.Revision.SpinPair.livingRoot.toAuthoritativeRoot
      (Stage9C.Revision.SpinPair.visit 10) ∧
    Stage10.Runtime.visit = Stage9C.Revision.SpinPair.visit 10 ∧ Stage10.Runtime.SameOccurrenceActivation :=
  ⟨complete_general_authoritative_world _ _ _, rfl, Stage10.Runtime.sameOccurrenceActivation⟩

theorem terminal_cannot_create_successor_or_cofinal :
    advance RootAnswerNextRegression.livingTerminalRoot.toAuthoritativeRoot.toLedgerRoot
      (.finite RootAnswerNextRegression.terminalVisit) = none ∧
    formCofinal RootAnswerNextRegression.livingTerminalRoot.toAuthoritativeRoot.toLedgerRoot = none ∧
    Produced _ RootAnswerNextRegression.livingTerminalRoot.toAuthoritativeRoot
      (.finite RootAnswerNextRegression.terminalVisit) :=
  ⟨rfl, rfl, complete_general_authoritative_world _ _ _⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AdmittedWorldControls
open Lean Elab Command
open SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.getUsedConstantsAsSet
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
  for module in env.header.moduleNames do
    if "scratch.".isPrefixOf module.toString then throwError "PRODUCTION_SCRATCH_IMPORT {module}"
  let controls := [``AdmittedWorldControls.generic_universe_visit_material, ``AdmittedWorldControls.complete_general_authoritative_world, ``AdmittedWorldControls.recurrent_histories_remain_distinct, ``AdmittedWorldControls.cofinal_and_post_cofinal_whole_worlds, ``AdmittedWorldControls.original_spin_pair_complete_world, ``AdmittedWorldControls.terminal_cannot_create_successor_or_cofinal]
  let closure := recoveryClosure env controls
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "CONTROL_MISSING {name}"
    if info.isUnsafe || info.isPartial then throwError "CONTROL_UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
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
