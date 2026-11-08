import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponseRuntime
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountabilityControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponseControls

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information
open Agency.Protocol Continuation

def signature (actor : Bool) : Mandate.Source.Action := ⟨actor, [], .challenge, [.challenge], .present⟩
abbrev base (active : Bool) := {AdmissionControls.base with
  actions := AdmissionControls.base.actions ++ [signature false, signature true]
  eventAlphabet := AdmissionControls.base.eventAlphabet ++ [Event.send 0 0, Event.send 1 0]
  bootstrap := if active then AdmissionControls.base.bootstrap else []}
abbrev source (active : Bool) : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := base active
  reference := fun _ _ => []
  reference_generated := by
    apply (base active).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (base active).publicPrefix
  original := (base active).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev foundation (active : Bool) : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨Distributed.Recall.Information.Regression.base, Distributed.Recall.Information.Regression.scope, source active, rfl, rfl⟩
abbrev model (active : Bool) := AdmissionRuntime.profile (foundation active)
abbrev code (active : Bool) := (model active).source.code
abbrev origin (active : Bool) : Origin (model active) where
  history := ⟨(model active).source.history, (model active).source.original⟩
  response := ⟨Reaction.restrict (code active) (model active).source.opponent, Reaction.restriction_is_generated _ _⟩
  side := .original
abbrev start (active : Bool) (budget : Nat) := EventHistory.ofOrigin (model active) budget (origin active)

def work (active oppose : Bool) : (code active).Policy := fun key _ =>
  if key.1 = 0 then [if oppose then AdmissionControls.no else AdmissionControls.yes]
  else [if oppose then AdmissionControls.ownNo else AdmissionControls.ownYes]
theorem work_generated (active oppose : Bool) : work active oppose ∈ (code active).policies := by
  apply (code active).every_local_policy_is_enumerated
  intro key _
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split <;> cases oppose <;> simp

def activation (active : Bool) (site : Fin (code active).sites) : LocalMove (code active) site :=
  ⟨some ⟨.activate site, by fin_cases site <;> simp [code, base, AdmissionControls.base, DeviationControls.code]⟩,
    by fin_cases site <;> simp [ownMoves, code, base, AdmissionControls.base, DeviationControls.code]⟩
def sending (active : Bool) (recipient site : Fin (code active).sites) : LocalMove (code active) site :=
  ⟨some ⟨.send site recipient, by fin_cases site <;> fin_cases recipient <;> simp [code, base, AdmissionControls.base, DeviationControls.code]⟩,
    by fin_cases site <;> fin_cases recipient <;> simp [ownMoves, code, base, AdmissionControls.base, DeviationControls.code]⟩
def rule (active : Bool) (recipient : Fin (code active).sites) (oppose activating : Bool) : Rule (code active) :=
  ⟨⟨work active oppose, work_generated active oppose⟩, fun key _ => if activating then activation active key.1 else sending active recipient key.1⟩
def quiet (active : Bool) : Rule (code active) where
  work := ⟨fun _ _ => [], by apply (code active).every_local_policy_is_enumerated; intro key _; exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun _ _ => ⟨none, List.mem_cons_self⟩
def environment (active withheld : Bool) : Opponent (code active) := fun history _ _ =>
  match history.length - ((model active).source.history.length + 1) with
  | 5 => some ⟨.deliver 0, by simp [code, base, AdmissionControls.base, DeviationControls.code]⟩
  | 7 => some ⟨.deliver 1, by simp [code, base, AdmissionControls.base, DeviationControls.code]⟩
  | 13 => if withheld then none else some ⟨.deliver 2, by simp [code, base, AdmissionControls.base, DeviationControls.code]⟩
  | _ => none
abbrev rival (active : Bool) : Opponent (code active) := fun _ _ _ => none
def normal (active withheld : Bool) (recipient : Fin (code active).sites) : List (EventHistory.Stage (code := code active)) :=
  ((List.replicate 4 (rule active recipient false true)) ++ (List.replicate 4 (rule active recipient false false)) ++
    (List.replicate 4 (rule active recipient true true)) ++ (List.replicate 2 (rule active recipient true false))).map
      fun protocol => (protocol, environment active withheld)
abbrev past (active : Bool) := normal active false 0 ++ [(quiet active, rival active), (quiet active, rival active)]
abbrev vocabulary := AdmissionControls.vocabulary
abbrev slot := AdmissionControls.slot
abbrev law (active : Bool) : StageReception.Law (code active) := ⟨fun _ _ => slot, 1⟩
def encoding (active : Bool) : StageTransport.Encoding (code := code active) := fun signal =>
  if AdmissionCode.content (base active) signal = 0 then some AdmissionControls.first
  else if AdmissionCode.content (base active) signal = 1 then some AdmissionControls.second else some AdmissionControls.third
abbrev produce (active : Bool) (budget : Nat) (stages : List (EventHistory.Stage (code := code active))) := IncidentResponse.produce (model active) (start active budget) stages vocabulary (encoding active) (law active)
inductive View where
  | idle | awaitingReview | blocked (reason : IncidentResponse.Obstruction) | ready
  deriving DecidableEq
def view (active : Bool) (budget : Nat) (stages : List (EventHistory.Stage (code := code active))) : View :=
  match produce active budget stages with
  | .idle => .idle
  | .awaitingReview => .awaitingReview
  | .blocked reason => .blocked reason
  | .ready _ => .ready

theorem actual_received_conflict_and_original_roster_generate_a_ready_response :
    view true 20 (past true) = .ready ∧
      (StageAccountability.ledger (start true 20) vocabulary (encoding true) (law true) (past true)).map
        (fun incident => (incident.receiver, incident.slot.1, incident.pastStages.length)) = [(0, 0, 13)] ∧
      (EventHistory.execute (start true 20) (past true)).cut = 16 := by
  decide +kernel

theorem missing_interface_wrong_turn_sealed_memory_and_exhaustion_have_distinct_branches :
    (match IncidentResponse.produce AdmissionControls.model AdmissionControls.start (AdmissionControls.stages .normal)
      vocabulary AdmissionControls.encoding AdmissionControls.law with
      | .blocked reason => some reason | _ => none) = some .unsupportedAction ∧
      view true 20 (normal true false 0) = .blocked .notOwner ∧
      view true 20 (normal true false 1) = .blocked .sealed ∧
      view true 14 (normal true false 0) = .blocked .exhausted ∧
      view false 20 (past false) = .blocked .inactive := by
  decide +kernel

theorem missing_second_receipt_or_deleted_source_cannot_generate_a_response :
    view true 20 (normal true true 0) = .idle ∧ view true 20 [] = .idle := by
  decide +kernel

def unrelatedPresent : Rule (code true) where
  work := ⟨fun key _ => if key.1 = 0 then [signature false] else [], by
    apply (code true).every_local_policy_is_enumerated
    intro key _
    apply (mem_words_iff _ _ _).mpr
    split <;> simp⟩
  events := fun key _ => activation true key.1

abbrev journal (stages : List (EventHistory.Stage (code := code true))) :=
  IncidentResponse.journal (model true) (start true 20) stages vocabulary (encoding true) (law true)
abbrev responses := IncidentResponse.stages (model true) (start true 20) (past true) vocabulary (encoding true) (law true) (rival true)

theorem actual_response_is_bound_once_and_repeat_invocation_stays_under_review :
    (journal responses).map (fun answer => (answer.response.incident.receiver, answer.response.incident.slot.1,
      answer.response.incident.pastStages.length, answer.pastStages.length)) = [(0, 0, 13, 16)] ∧
      view true 20 responses = .awaitingReview ∧
      IncidentResponse.stages (model true) (start true 20) responses vocabulary (encoding true) (law true) (rival true) = responses := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · have checked : view true 20 responses = .awaitingReview := by decide +kernel
    cases chosen : produce true 20 responses with
    | awaitingReview => simp only [IncidentResponse.stages, chosen]
    | idle => simp only [view, chosen] at checked; contradiction
    | blocked reason => simp only [view, chosen] at checked; contradiction
    | ready response => simp only [view, chosen] at checked; contradiction

theorem an_unrelated_valid_owned_present_is_not_an_incident_response :
    (StageTrace.material (EventHistory.execute (start true 20) (past true)) unrelatedPresent (rival true)).submitted = [signature false] ∧
      StageTrace.activation (StageTrace.material (EventHistory.execute (start true 20) (past true)) unrelatedPresent (rival true)) = some 0 ∧
      (code true).law.Valid (EventStep.seed (EventHistory.execute (start true 20) (past true))).current (signature false) ∧
      (journal (past true ++ [(unrelatedPresent, rival true)])).isEmpty = true := by
  decide +kernel

theorem a_generated_review_does_not_mint_a_paid_ballot :
    StageBudget.ledger vocabulary (start true 20) responses = [AdmissionControls.first, AdmissionControls.second, AdmissionControls.third] ∧
      (StageTrace.records (start true 20) responses).getLast?.map (fun record => record.submitted) = some [signature false] := by
  decide +kernel

abbrev protocols : Nat → Rule (code true) := fun _ => quiet true
abbrev emitted := IncidentResponseRuntime.emitted (foundation true) (start true 20) (past true) vocabulary (encoding true) (law true) (rival true)
abbrev runtime := IncidentResponseRuntime.runtime (foundation true) (start true 20) (past true) protocols vocabulary (encoding true) (law true) slot 2 (rival true)
abbrev authority := IncidentResponseRuntime.authority (foundation true) (start true 20) (past true) protocols vocabulary (encoding true) (law true) slot 2 (rival true)
abbrev rooted := IncidentResponseRuntime.rooted (foundation true) (start true 20) (past true) protocols vocabulary (encoding true) (law true) slot 2 (rival true)

theorem the_new_native_review_stays_pending_with_its_original_incident :
    authority.current.challenges.map (fun row => Mandate.Challenge.History.isPending
      (IncidentResponseRuntime.family (foundation true) (start true 20) (past true) protocols vocabulary (encoding true) (law true) (rival true))
      (IncidentResponseRuntime.sourceIndex (foundation true) (start true 20) (past true) protocols vocabulary (encoding true) (law true) (rival true)) row.2) = [true] ∧
      rooted.incidents.length = 1 := by
  decide +kernel

theorem the_independent_consumer_uses_the_generated_native_claim_original_incident_ledger_and_next :
    ∃ ordinal ∈ authority.current.challenges.map (fun row => row.1.position.ordinal),
      ordinal = EventStep.boundary (EventHistory.execute (start true 20) (past true)) ∧
      rooted.incidents.length = 1 ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (StageAccountabilityRuntime.facade (foundation true) (start true 20) emitted protocols vocabulary (encoding true) (law true) slot 2).process.stateAt
        ((StageAccountabilityRuntime.facade (foundation true) (start true 20) emitted protocols vocabulary (encoding true) (law true) slot 2).process.successor runtime.state) := by
  have ready : view true 20 (past true) = .ready := actual_received_conflict_and_original_roster_generate_a_ready_response.1
  cases chosen : produce true 20 (past true) with
  | idle => simp only [view, chosen] at ready; contradiction
  | awaitingReview => simp only [view, chosen] at ready; contradiction
  | blocked reason => simp only [view, chosen] at ready; contradiction
  | ready response =>
    obtain ⟨claim, ordinal, _, admitted, _, _, _, ledger, next⟩ :=
      IncidentResponseRuntime.the_incident_generates_an_actual_native_challenge_in_its_own_root
        (foundation true) (start true 20) (past true) protocols vocabulary (encoding true) (law true) slot 2 (rival true) response chosen
    exact ⟨claim.position.ordinal, List.mem_map.mpr ⟨_, admitted, rfl⟩, ordinal, by decide +kernel, ledger, next⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponseControls
