import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.Domain

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Source
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

theorem every_available_original_paid_improvement_survives_the_received_update
    (actual : Runtime.Activation model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law)
    (available : ∃ tail : Complete.FiniteProgram model.source.code,
      Selection.acceptable model (domain model budget) original reference
        (extension (horizon (domain model budget)) (reserved model original worker quote quotas) tail.2) ∧
      Distributed.Improves (Selection.axes (fuel := horizon (domain model budget)) model (domain model budget))
        (Selection.benefit model (domain model budget) original) reference
        (extension (horizon (domain model budget)) (reserved model original worker quote quotas) tail.2)) :
    Distributed.Improves (Selection.axes (fuel := horizon (domain model budget)) model (domain model budget))
      (Selection.benefit model (domain model budget) original) reference (Proposal.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget)) := by
  exact strict_improvement_survives_nonstrict_improvement
    (Selection.axes (fuel := horizon (domain model budget)) model (domain model budget))
    (Selection.benefit model (domain model budget) original) reference actual.record.plan.choice.policy.protocol (Proposal.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget))
    (Prefix.every_available_full_responsibility_completion_improvement_is_realized model (domain model budget) original
      (reserved model original worker quote quotas) reference actual.record.plan.choice available)
    (Selection.acceptance_bounds_every_benefit model (domain model budget) original actual.record.plan.choice.policy.protocol (Proposal.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget))
      (Proposal.the_selected_programme_is_no_worse_than_the_pre_receipt_programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget)))

def Protection : Option (Runtime.Activation model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law) → Prop
  | none => True
  | some actual =>
      Knowledge.Contains (Observation.posterior model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget))
        (Observation.atCommunication model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record) ∧
      Selection.acceptable model (domain model budget) original reference (Proposal.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget)) ∧
      (∀ other ∈ Prefix.candidates model (domain model budget) original (reserved model original worker quote quotas) reference,
        ¬ Distributed.Improves (Selection.axes (fuel := horizon (domain model budget)) model (domain model budget))
          (Selection.benefit model (domain model budget) original) (Proposal.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget)) other.protocol) ∧
      Prefix.verify model (domain model budget) original (Proposal.past model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record) reference
        (Proposal.tail model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget)) = true ∧
      Synthesis.accepts model.source.code (economicAxes (point model budget world).point.source (point model budget world).point.cut)
        (actualEvaluation model (point model budget world).point original
          (clip (Deployment.actualHorizon model (point model budget world))
            (Proposal.programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget))) rival)
        (actualEvaluation model (point model budget world).point original reference rival)

theorem every_original_source_generates_its_own_posterior_full_comparison_and_actual_root :
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
  refine ⟨?_,Runtime.one_root_consumes_the_actual_learning_cut_entire_ledger_and_literal_next model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law (views model budget)⟩
  cases generated : prepared model budget original reference worker receiver quote quotas slots world rival ordinal vocabulary encoding law with
  | none => trivial
  | some actual =>
      exact ⟨Observation.the_received_reading_generates_an_origin_preserving_posterior model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget) covered,
        Proposal.the_initial_reference_and_every_original_opponent_are_retained model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget),
        Proposal.no_original_paid_candidate_dominates_the_received_programme model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget),
        Proposal.the_locked_past_and_all_finite_futures_are_independently_reviewed model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget),
        Learning.Installation.the_new_programme_protects_the_original_actual_reference model (domain model budget) original reference worker receiver quote quotas slots (point model budget world) rival ordinal vocabulary encoding law actual.record (views model budget)
          (Knowledge.cursor_covered _ _ covered)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Source
