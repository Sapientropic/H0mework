import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Progress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RootExposure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RootProgress

open Distributed Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : Source Party Good Port Technology Instrument)
  (interface : Interface source.code) (receiver : Fin source.code.sites)
  (incoming : Nat → Option (Envelope source.code)) (scope : Scope)
  (proposed : Fin source.code.signals)

def readyFromOutcome : source.code.Outcome source.reference → Option (Finset (Fin source.code.sites))
  | .blocked _ => none
  | .selected choice => some (Progress.readyKeys source.code interface choice.policy.policy
      (source.code.historyCurrent source.history) source.events receiver incoming source.events.length scope proposed)

/-- Readiness is generated from the original selected policy and actual source.
The existing synthesis occurrence owns the branch. -/
def rootedReady : Option (Finset (Fin source.code.sites)) :=
  match (Runtime.facade source).readoutAt
      (Runtime.activated source (source.history.length + 1)) .synthesis with
  | .inl outcome => readyFromOutcome source interface receiver incoming scope proposed outcome.2
  | .inr impossible => nomatch impossible

def readout (threshold : Nat) : Quorum.Readout source.code :=
  match RootConsumer.rooted source interface receiver incoming with
  | .blocked => .blocked
  | .available state => Quorum.readout source.code state scope threshold

theorem rooted_ready_of_selected (choice : source.code.Selection source.reference)
    (selected : source.answer = .selected choice) :
    rootedReady source interface receiver incoming scope proposed =
      some (Progress.readyKeys source.code interface choice.policy.policy
        (source.code.historyCurrent source.history) source.events receiver incoming source.events.length scope proposed) := by
  change readyFromOutcome source interface receiver incoming scope proposed source.answer = _
  rw [selected]
  rfl

theorem generated_root_readiness_produces_a_decision
    (threshold : Nat) (keys : Finset (Fin source.code.sites))
    (actual : rootedReady source interface receiver incoming scope proposed = some keys)
    (positive : 0 < threshold) (communication : threshold ≤ keys.card) :
    ∃ generated : Fin source.code.signals,
      readout source interface receiver incoming scope threshold = .decided generated := by
  have generatedReady : rootedReady source interface receiver incoming scope proposed =
      readyFromOutcome source interface receiver incoming scope proposed source.answer := rfl
  rw [generatedReady] at actual
  unfold readyFromOutcome at actual
  cases selected : source.answer with
  | blocked _ => simp only [selected] at actual; contradiction
  | selected choice =>
    simp only [selected] at actual
    have same := Option.some.inj actual
    subst keys
    obtain ⟨generated, decided⟩ := Progress.finite_delivery_condition_generates_a_decision source.code interface
      choice.policy.policy (source.code.historyCurrent source.history) source.events receiver incoming
      source.events.length threshold scope proposed positive communication
    refine ⟨generated, ?_⟩
    unfold readout
    rw [RootConsumer.rooted_eq_generated]
    unfold RootConsumer.generate RootConsumer.fromOutcome
    rw [selected]
    exact decided

theorem decided_root_preserves_original_service_and_next
    (threshold : Nat) (value : Fin source.code.signals)
    (decided : readout source interface receiver incoming scope threshold = .decided value) :
    ∃ choice : source.code.Selection source.reference,
      source.answer = .selected choice ∧
      (source.history, source.events) ∈ source.code.scenarios ∧
      (source.actualExecution source.history.length).submitted =
        (source.code.executed choice.policy.policy (source.history, source.events)).word ∧
      ServiceAdequate source.code.law (source.actualExecution source.history.length).before source.code.task
        (source.actualExecution source.history.length).submitted ∧
      source.currentAt (source.history.length + 2) = source.code.law.next
        (source.code.historyCurrent source.history)
        (source.code.executed choice.policy.policy (source.history, source.events)).word ∧
      source.code.verify source.reference choice.policy.policy = true := by
  unfold readout at decided
  cases reception : RootConsumer.rooted source interface receiver incoming with
  | blocked => rw [reception] at decided; contradiction
  | available state =>
    have available := reception
    rw [RootConsumer.rooted_eq_generated] at available
    obtain ⟨choice, selected, _, submitted, service, next, verified⟩ :=
      RootConsumer.available_has_paid_source source interface receiver incoming state available
    exact ⟨choice, selected, source.admitted, submitted, service, next, verified⟩

theorem blocked_root_produces_no_protocol_decision
    (threshold : Nat)
    (blocked : RootConsumer.rooted source interface receiver incoming = .blocked) :
    readout source interface receiver incoming scope threshold = .blocked := by
  simp only [readout, blocked]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RootProgress
