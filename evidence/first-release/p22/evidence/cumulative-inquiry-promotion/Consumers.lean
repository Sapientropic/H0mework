import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.NativeVisit.Material
import SaturationMonoid.LivingLawRootTemporalAnswerNextRegression
import SaturationMonoid.LivingLawRootAnswerNextRegression
import SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair.InquiryPrograms
import Lean
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingProcess.Consumer
import SaturationMonoid.LivingLawRootAnswerNextHistoryRegression
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingInquiryAlignment.U7Coverage
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingInquiryAlignment.Query
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingInquiryAlignment.HeaderConsumer
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.NativeCurrent.World
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.InquiryQuery.Coverage

/-! Production consumers of complete living/current registries, full U7 and three-branch query formation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.NativeVisitControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RootTemporalAnswerNextRegression
noncomputable section

theorem recurrent_same_current_retains_distinct_histories :
    ∃ first last : MotherArenaHigher.Material (0 : Ordinal.{0}),
      MotherNativeVisit.formVisit livingRoot first = some (.finite recurrentFirstVisit) ∧
      MotherNativeVisit.formVisit livingRoot last = some (.finite recurrentSecondVisit) ∧ first ≠ last := by
  obtain ⟨first, formedFirst⟩ := MotherNativeVisit.every_visit_material (rank := 0) livingRoot (.finite recurrentFirstVisit)
  obtain ⟨last, formedLast⟩ := MotherNativeVisit.every_visit_material (rank := 0) livingRoot (.finite recurrentSecondVisit)
  refine ⟨first, last, formedFirst, formedLast, ?_⟩
  intro same
  have visits := Option.some.inj (formedFirst.symm.trans ((congrArg (MotherNativeVisit.formVisit livingRoot) same).trans formedLast))
  exact recurrent_visits_are_distinct (SourceNativeTemporalVisitAt.finite_injective visits)

theorem cofinal_and_its_successor_are_complete :
    ∃ boundary successor : MotherArenaHigher.Material (0 : Ordinal.{0}),
      MotherNativeVisit.formVisit livingRoot boundary = some temporalVisit ∧
      MotherNativeVisit.formVisit livingRoot successor = some (temporalVisit.next rfl) := by
  obtain ⟨boundary, formedBoundary⟩ := MotherNativeVisit.every_visit_material (rank := 0) livingRoot temporalVisit
  obtain ⟨successor, formedSuccessor⟩ := MotherNativeVisit.every_visit_material (rank := 0) livingRoot (temporalVisit.next rfl)
  exact ⟨boundary, successor, formedBoundary, formedSuccessor⟩

theorem original_spin_pair_visit10 :
    ∃ material : MotherArenaHigher.Material (0 : Ordinal.{0}),
      MotherNativeVisit.formVisit Stage9C.Revision.SpinPair.livingRoot material =
        some (Stage9C.Revision.SpinPair.visit 10) :=
  MotherNativeVisit.every_visit_material _ _

theorem terminal_cannot_forge_local_successor :
    MotherNativeVisit.advance RootAnswerNextRegression.livingTerminalRoot
      (.finite RootAnswerNextRegression.terminalVisit) = none := rfl
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.NativeVisitControls
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.LivingProcessControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
abbrev N := SourceNativeLedgerCompilerRegression.N
abbrev Finite := RootAnswerNextHistoryRegression.process
abbrev Cofinal := RootAnswerNextHistoryRegression.cofinalProcess

def nodes : Option Nat ⊕ Nat → SourceNativeLivingRootCurrentAt N
  | .inl value => Finite.stateAt value
  | .inr value => Cofinal.stateAt value

def boundary (value : SourceNativeLivingRootCurrentAt N) : Bool := value.visit.history.hasCofinalBoundary

theorem nodes_injective : Function.Injective nodes := by
  intro first last same
  cases first with
  | inl first =>
    cases last with
    | inl last => exact congrArg Sum.inl (Finite.stateAt_injective same)
    | inr last =>
      have tags := congrArg boundary same
      cases first <;> cases tags
  | inr first =>
    cases last with
    | inl last =>
      have tags := congrArg boundary same
      cases last <;> cases tags
    | inr last => exact congrArg Sum.inr (Cofinal.stateAt_injective same)

def mixed : SourceNativeLivingRootProcess N where
  State := Option Nat ⊕ Nat
  stateAt := nodes
  stateAt_injective := nodes_injective
  initial := .inl none
  successorAt := fun value => match value with
    | .inl value => ⟨.inl (Finite.successor value), (Finite.successorAt value).property⟩
    | .inr value => ⟨.inr (Cofinal.successor value), (Cofinal.successorAt value).property⟩

def lane : mixed.State → Bool
  | .inl _ => false
  | .inr _ => true

def orbit : Nat → mixed.State
  | 0 => mixed.initial
  | depth + 1 => mixed.successor (orbit depth)

theorem successor_preserves_lane (state : mixed.State) : lane (mixed.successor state) = lane state := by
  cases state <;> rfl

theorem initial_orbit_lane (depth : Nat) : lane (orbit depth) = false := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact (successor_preserves_lane (orbit depth)).trans ih

theorem dormant_cofinal_not_in_initial_orbit (depth : Nat) : orbit depth ≠ .inr 0 := by
  intro same
  have tags := congrArg lane same
  rw [initial_orbit_lane] at tags
  cases tags

theorem whole_process_with_dormant_branch_is_formed :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (MotherLivingProcess.formData material).isSome,
        let output := (MotherLivingProcess.formData material).get available
        ∃ p : MotherLivingProcess.Presentation mixed output,
          p.restrict = mixed ∧ p.readInitial = .inl none ∧
          p.readStateAt (.inr 0) = mixed.stateAt (.inr 0) ∧
          p.readSuccessor (.inr 0) = .inr 1 ∧ p.state (.inr 0) ≠ p.state (.inl none) := by
  obtain ⟨rank, material, available, p, recovered, _retained⟩ := MotherLivingProcess.every_original_process N mixed
  refine ⟨rank, material, available, p, recovered, p.readInitial_eq,
    congrFun p.readStateAt_eq (.inr 0), congrFun p.readSuccessor_eq (.inr 0), ?_⟩
  intro same
  cases p.state.injective same
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.LivingProcessControls
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.U7QueryControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision
noncomputable section

def N : WorldRelationNetwork.{0} where
  Support := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  Responsibility := Bool
  Claim := Bool
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  OpenAt := fun _ _ => Unit
  openClaimAt := fun {_} {responsibility} _ => responsibility
  openProgressBudgetAt := fun {_} {responsibility} _ => if responsibility then 41 else 37
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => Unit
  obstructionClaim := fun _ => false
  SemanticChangeAt := fun _ _ _ => Unit
  DispositionAt := fun _ _ => Unit

def demand : U7ProducerCalculus N where
  DemandAt := fun _ => Nat
  generateDemand := fun _ => (37 : Nat)

def source : U7ActualSuccessorSource N demand where
  EventAt := fun _ value => PLift (value = (37 : Nat)) × Bool
  emit := fun _ => ⟨⟨rfl⟩, false⟩
  demandGeneratedAt := fun {support} {obstruction} {value} event => by
    have same : value = (37 : Nat) := event.1.down
    cases same
    exact .canonical obstruction
  demandEntryAt := fun event => ⟨event.2, ()⟩

def calculus : U7ObstructionEvolutionCalculus N demand where
  source := source
  compile := fun event => if event.2 then
    ⟨.settled (), ⟨⟨()⟩, rfl⟩⟩ else ⟨.requiresTheoryAudit (), PUnit.unit⟩

def firstEvent : source.EventAt (support := ()) () (37 : Nat) := ⟨⟨rfl⟩, false⟩
def otherEvent : source.EventAt (support := ()) () (37 : Nat) := ⟨⟨rfl⟩, true⟩

theorem complete_header_source_material :
    ∃ rank : Ordinal.{0}, ∃ addresses : MotherInquiryU7Header.Addresses (rank := rank) ⟨demand, calculus⟩,
      MotherInquiryU7Header.FormationAt demand calculus addresses :=
  MotherInquiryU7Header.every_original_header demand calculus

theorem unselected_event_compiler_values_retained :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ index : MotherInquiryU7.EventTotal calculus.source ↪ MotherArenaHigher.Base rank,
      ∃ member : ∀ point, MotherInquiryU7.DispositionAt calculus.source point ↪ MotherArenaHigher.Base rank,
        ∃ available : (MotherInquiryU7.formCalculus calculus.source index member material).isSome,
          let actual := (MotherInquiryU7.formCalculus calculus.source index member material).get available
          actual = calculus := by
  obtain ⟨rank, material, index, member, formed⟩ := MotherInquiryU7.every_calculus calculus
  have available : (MotherInquiryU7.formCalculus calculus.source index member material).isSome := by rw [formed]; rfl
  exact ⟨rank, material, index, member, available, Option.some.inj ((Option.some_get available).trans formed)⟩

theorem original_unselected_event_is_different :
    (calculus.compile firstEvent).disposition ≠ (calculus.compile otherEvent).disposition := by
  intro same
  cases same

theorem all_demand_and_event_members_preserved :
    ∃ rank : Ordinal.{0}, ∃ addresses : MotherInquiryU7Header.Addresses (rank := rank) ⟨demand, calculus⟩,
      ∃ demandMaterial : MotherArenaHigher.Material rank, ∃ generatedDemand : U7ProducerCalculus N,
      ∃ pd : MotherInquiryU7Demand.Presentation demand generatedDemand,
        MotherInquiryU7Demand.form addresses.obstruction demandMaterial = some generatedDemand ∧
        pd.demand () () (37 : Nat) ≠ pd.demand () () (38 : Nat) ∧
        ∃ eventMaterial : MotherArenaHigher.Material rank, ∃ generatedSource : U7ActualSuccessorSource N demand,
        ∃ pe : MotherInquiryU7Events.Presentation demand source generatedSource,
          MotherInquiryU7Events.form demand addresses.obstruction addresses.demand
            (fun support => (Function.Embedding.sigmaMk support).trans addresses.entry) eventMaterial = some generatedSource ∧
          pe.event () () (37 : Nat) firstEvent ≠ pe.event () () (37 : Nat) otherEvent ∧
          generatedSource.demandEntryAt (pe.event () () (37 : Nat) firstEvent) = source.demandEntryAt firstEvent ∧
          generatedSource.demandEntryAt (pe.event () () (37 : Nat) otherEvent) = source.demandEntryAt otherEvent := by
  obtain ⟨rank, addresses, _formed⟩ := MotherInquiryU7Header.every_original_header demand calculus
  obtain ⟨dm, gd, df, ⟨pd⟩⟩ := MotherInquiryU7Demand.every_at_rank addresses.obstruction demand addresses.demand
  obtain ⟨em, gs, ef, ⟨pe⟩⟩ := MotherInquiryU7Events.every_at_rank demand addresses.obstruction addresses.demand
    (fun support => (Function.Embedding.sigmaMk support).trans addresses.entry) source addresses.event
  refine ⟨rank, addresses, dm, gd, pd, df, ?_, em, gs, pe, ef, ?_, pe.entry_eq () () _ firstEvent,
    pe.entry_eq () () _ otherEvent⟩
  · intro same; have bad := (pd.demand () ()).injective same; cases bad
  · intro same
    have bad := (pe.event () () (37 : Nat)).injective same
    have tags := congrArg Prod.snd bad
    cases tags

theorem original_query_labels_and_state_preserved :
    MotherLivingInquiryAlignment.assembleQueryRestriction
      (Equiv.ulift.symm : (SpinPair.readInquiryState 10).Query ≃ ULift.{0} (SpinPair.readInquiryState 10).Query)
      (MotherLivingInquiryAlignment.queryClauseEquiv Equiv.ulift.symm
        (MotherNativeClause.ofState (SpinPair.readInquiryState 10))) = SpinPair.readInquiryState 10 :=
  MotherLivingInquiryAlignment.original_query_state_recovers _ _ _ rfl

theorem actual_header_installed {K : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt K V) :
    ∃ actual : MotherInquiryU7Header.Header K, ∃ same : actual = ⟨state.U7, state.calculus⟩,
      MotherLivingInquiryAlignment.assembleWithHeader state.visit state.Query actual same
        (MotherNativeClause.ofState state) = state := by
  obtain ⟨rank, addresses, dm, gd, pd, df, em, gs, pe, ef, cm, actual, cf, same⟩ :=
    MotherInquiryU7Header.every_original_header state.U7 state.calculus
  exact ⟨_, same, MotherLivingInquiryAlignment.original_header_state_recovers state _ same _ rfl⟩
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.U7QueryControls
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.NetworkRestrictionControls
open MotherHandoffRestriction MotherHandoffSource MotherNativeCurrent
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Stage9C.Revision
noncomputable section

abbrev Recovered (N : WorldRelationNetwork.{0}) (old : SourceNativeLivingRootCurrentAt N) : Prop :=
  ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
    let sourceMaterial := (MotherArenaHigher.split rank material).1
    let jointMaterial := (MotherArenaHigher.split rank sourceMaterial).1
    let payloadMaterial := (MotherArenaHigher.split rank sourceMaterial).2
    ∃ available : (formJoint jointMaterial).isSome,
      let value := (formJoint jointMaterial).get available
      ∃ events : EventFamily old.root.source.base,
        ∃ declaration : Declaration old.root.source.base events,
          ∃ p : JointPresentation old.root.toAuthoritativeRoot events declaration value,
            ∃ payloadAvailable : (formPayload old.root declaration jointMaterial value
              (Option.some_get available).symm p payloadMaterial).isSome,
              let payload := (formPayload old.root declaration jointMaterial value
                (Option.some_get available).symm p payloadMaterial).get payloadAvailable
              ∃ same : payload = MotherHandoffPayload.valuesOf declaration,
                let result := formCurrent (restrictHeader old.root declaration value p payload same)
                  (MotherArenaHigher.split rank material).2
                ∃ ready : result.isSome, world p.authority.network (result.get ready) = ⟨N, old⟩

theorem generic_actual_world (N : WorldRelationNetwork.{0}) (old : SourceNativeLivingRootCurrentAt N) : Recovered N old := by
  obtain ⟨rank, material, available, events, declaration, p, payloadAvailable, same, formed, _retained⟩ :=
    every_original_current N old
  obtain ⟨ready, recovered⟩ := world_of_formed p.authority.network old _ _ formed
  exact ⟨rank, material, available, events, declaration, p, payloadAvailable, same, ready, recovered⟩

def spinPairCurrent : SourceNativeLivingRootCurrentAt MaterialN := ⟨SpinPair.V, SpinPair.livingRoot, SpinPair.visit 10⟩

theorem original_spin_pair_world10 : Recovered MaterialN spinPairCurrent :=
  generic_actual_world MaterialN spinPairCurrent
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.NetworkRestrictionControls
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.InquiryQueryControls
open MotherInquiryQuery MotherLivingInquiryAlignment MotherInquiryAnswerClause
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision
noncomputable section

def Recovered {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt N V) : Prop :=
  ∃ rank : Ordinal.{0}, ∃ base : MotherArenaHigher.Material rank,
    ∃ queries : state.Query ≃ MotherAuthorityFamilies.Member base,
    ∃ operand : Operand state.root state.visit ↪ MotherArenaHigher.Base rank,
    ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (formAtQueries state.calculus base queries operand material).isSome,
        assembleQueryRestriction queries ((formAtQueries state.calculus base queries operand material).get available) = state ∧
        ∀ point : MotherNativeClause.Total state.root state.visit state.U7 state.calculus state.Query,
          (queryClauseTotalEquiv queries point).1 = queries point.1

theorem generic_whole_query_carrier {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt N V)
    (answering : ∀ query, Answering state.calculus query (state.compileInquiry query)) : Recovered state := by
  let rank := MotherArenaHigher.carrierRank (state.Query ⊕ Operand state.root state.visit)
  let address := MotherArenaHigher.carrierAddress (state.Query ⊕ Operand state.root state.visit)
  let queryCode : state.Query ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => address (.inl value), fun _ _ same => Sum.inl.inj (address.injective same)⟩
  let operandCode : Operand state.root state.visit ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => address (.inr value), fun _ _ same => Sum.inr.inj (address.injective same)⟩
  obtain ⟨base, queries, material, available, restored⟩ := queries_at_rank state answering queryCode operandCode
  exact ⟨rank, base, queries, operandCode, material, available, restored, queryClauseTotal_projects queries⟩

theorem original_spin_pair_query10 : Recovered (SpinPair.readInquiryState 10) := by
  apply generic_whole_query_carrier
  intro query
  cases query
  trivial
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.InquiryQueryControls
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
  let controls := [``NativeVisitControls.recurrent_same_current_retains_distinct_histories, ``NativeVisitControls.cofinal_and_its_successor_are_complete, ``NativeVisitControls.original_spin_pair_visit10, ``NativeVisitControls.terminal_cannot_forge_local_successor, ``LivingProcessControls.dormant_cofinal_not_in_initial_orbit, ``LivingProcessControls.whole_process_with_dormant_branch_is_formed, ``U7QueryControls.complete_header_source_material, ``U7QueryControls.unselected_event_compiler_values_retained, ``U7QueryControls.original_unselected_event_is_different, ``U7QueryControls.all_demand_and_event_members_preserved, ``U7QueryControls.original_query_labels_and_state_preserved, ``U7QueryControls.actual_header_installed, ``NetworkRestrictionControls.generic_actual_world, ``NetworkRestrictionControls.original_spin_pair_world10, ``InquiryQueryControls.generic_whole_query_carrier, ``InquiryQueryControls.original_spin_pair_query10]
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
