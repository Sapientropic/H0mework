import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.Domain

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.Source
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (budget : Nat)

abbrev views := completeViews model budget
abbrev domain := (views model budget).map View.point
variable (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon (domain model budget)))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (world : Distributed.Recall.Information.World model budget)
  (rival : Opponent model.source.code) (ordinal : Nat)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code)

abbrev point := Budget.Programme.Debt.Information.ofWorld model budget world

abbrev prepared := Runtime.prepare model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law
abbrev facade := Runtime.facade model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget)
abbrev activated (count : Nat) := Runtime.activated model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) count

private theorem strict_improvement_survives_nonstrict_improvement
    {Policy Coordinate : Type} (axes : List Coordinate) (cost : Policy → Coordinate → ℚ)
    (reference old next : Policy) (strict : Distributed.Improves axes cost reference old)
    (improved : Distributed.NoWorse axes cost next old) : Distributed.Improves axes cost reference next :=
  ⟨Distributed.noWorse_trans improved strict.1,fun reverse => strict.2 (Distributed.noWorse_trans reverse improved)⟩

theorem every_available_original_paid_improvement_survives_all_funded_updates
    (actual : Runtime.Activation model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law)
    (available : ∃ tail : Complete.FiniteProgram model.source.code,
      Selection.acceptable model (domain model budget) original reference
        (extension (horizon (domain model budget)) (reserved model original worker quote quotas) tail.2) ∧
      Distributed.Improves (Selection.axes (fuel := horizon (domain model budget)) model (domain model budget))
        (Selection.benefit model (domain model budget) original) reference
        (extension (horizon (domain model budget)) (reserved model original worker quote quotas) tail.2)) :
    Distributed.Improves (Selection.axes (fuel := horizon (domain model budget)) model (domain model budget))
      (Selection.benefit model (domain model budget) original) reference (Execution.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))) := by
  exact strict_improvement_survives_nonstrict_improvement
    (Selection.axes (fuel := horizon (domain model budget)) model (domain model budget))
    (Selection.benefit model (domain model budget) original) reference actual.record.plan.choice.policy.protocol (Execution.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world)))
    (Prefix.every_available_full_responsibility_completion_improvement_is_realized model (domain model budget) original
      (reserved model original worker quote quotas) reference actual.record.plan.choice available)
    (Selection.acceptance_bounds_every_benefit model (domain model budget) original actual.record.plan.choice.policy.protocol (Execution.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world)))
      ((Execution.final model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).above))

theorem the_source_generated_driver_end_is_in_its_own_final_root
    (actual : Runtime.Activation model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law)
    (made : prepared model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law = some actual) :
    Runtime.serviceCut model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) =
      Runtime.cutPoint model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) (Execution.stages model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).length := by
  change Runtime.prepare model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law = some actual at made
  simp only [Runtime.serviceCut,Runtime.cutPoint,made]
  exact (Execution.the_actual_driver_end_is_a_literal_prefix_of_the_same_final_source model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).symm

theorem the_source_scheduled_driver_consumes_every_common_live_slot
    (actual : Runtime.Activation model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law) :
    Driving.remaining (Execution.final model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))) = 0 := by
  apply Driving.no_unreserved_service_can_force_an_empty_physical_spin
  exact (Nat.sub_le _ _).trans (Nat.min_le_left _ _)


theorem the_canonical_driver_reaches_its_entire_actual_window
    (actual : Runtime.Activation model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law) :
    (Execution.final model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).past.length = Deployment.actualHorizon model (point model budget world) := by
  have capacity : Deployment.actualHorizon model (point model budget world) ≤ horizon (domain model budget) :=
    Continuation.Whole.Complete.each_remaining_horizon_is_generated (domain model budget) (point model budget world).point
      (List.mem_map.mpr ⟨point model budget world,every_source_generated_world_is_in_the_information_domain model budget world,rfl⟩)
  have exhausted := the_source_scheduled_driver_consumes_every_common_live_slot model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law actual
  have bounded := (Execution.final model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).actualWithin
  unfold Driving.remaining at exhausted
  rw [Nat.min_eq_left capacity] at exhausted
  omega

def Protection : Option (Runtime.Activation model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law) → Prop
  | none => True
  | some actual =>
      Knowledge.Contains (Execution.final model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).beliefs
        ((Execution.final model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).current (point model budget world) rival) ∧
      Selection.acceptable model (domain model budget) original reference (Execution.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))) ∧
      (∀ other ∈ Prefix.candidates model (domain model budget) original (reserved model original worker quote quotas) reference,
        ¬ Distributed.Improves (Selection.axes (fuel := horizon (domain model budget)) model (domain model budget))
          (Selection.benefit model (domain model budget) original) (Execution.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))) other.protocol) ∧
      Prefix.verify model (domain model budget) original ((Execution.final model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).past) reference
        (Execution.tail model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))) = true ∧
      Synthesis.accepts model.source.code (economicAxes (point model budget world).point.source (point model budget world).point.cut)
        (actualEvaluation model (point model budget world).point original
          (clip (Deployment.actualHorizon model (point model budget world))
            (Execution.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world)))) rival)
        (actualEvaluation model (point model budget world).point original reference rival) ∧
      Runtime.serviceCut model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) = Runtime.cutPoint model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) (Execution.stages model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).length ∧
      (Execution.final model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))).past.length = Deployment.actualHorizon model (point model budget world)

theorem every_original_source_generates_its_actual_driver_full_comparison_and_one_actual_root :
    Protection model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law (prepared model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law) ∧
      ∀ count : Nat,
        let current := activated model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law count
        (ProgrammeHistory.visitAt (Runtime.source model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget)).input (arrival (Runtime.cutPoint model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) count))).current =
          (ProgrammeHistory.visitAt (Runtime.cutPoint model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) count).source.input (arrival (Runtime.cutPoint model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) count))).current ∧
        (∀ visit ≤ arrival (Runtime.cutPoint model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) count),
          Native.Coupling.Match model.source.code (Runtime.cutPoint model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) count).source.input (Runtime.source model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget)).input
            (Financial.accountAt (Runtime.cutPoint model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget) count).source.input visit)
            (Financial.accountAt (Runtime.source model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget)).input visit)) ∧
        HEq ((facade model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law).readoutAt current .learning) (current.tick.generated.projectionOutcome (.component ())) ∧
        HEq current.tick.generated.wholeLedgerWriteBack
          (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
        ((count < (Runtime.remainingWord model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget)).length) → current.tick.nextCurrent = (activated model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law (count+1)).current) := by
  have covered : Knowledge.Contains (views model budget) (point model budget world) :=
    Knowledge.member _ _ (every_source_generated_world_is_in_the_information_domain model budget world)
  refine ⟨?_,Runtime.one_root_consumes_every_paid_learning_cut_entire_ledger_and_literal_next model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget)⟩
  cases generated : prepared model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law with
  | none => trivial
  | some actual =>
      exact ⟨Execution.the_whole_driven_chain_retains_actual_origin_preserving_knowledge model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world)) covered,
        Execution.the_original_reference_and_all_opponents_are_protected model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world)),
        Execution.no_original_paid_candidate_dominates_the_actual_driven_chain model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world)),
        Execution.the_actual_paid_past_and_every_finite_continuation_are_independently_reviewed model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world)),
        Execution.the_new_programme_protects_the_original_actual_reference model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) (Deployment.actualHorizon model (point model budget world))
          (Knowledge.cursor_covered _ _ covered),
        the_source_generated_driver_end_is_in_its_own_final_root model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law actual generated,
        the_canonical_driver_reaches_its_entire_actual_window model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law actual⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.Source
