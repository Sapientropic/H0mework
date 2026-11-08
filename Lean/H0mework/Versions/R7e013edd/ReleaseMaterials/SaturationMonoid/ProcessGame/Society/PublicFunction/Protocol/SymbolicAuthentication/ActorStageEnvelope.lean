import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorQuorum
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueue

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageEnvelope
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

-- Pool installed local words before reading ballots or receiver certificates.
-- All aliases of an actor and all actual live cuts share the same decision budget.
def choices (stages : List (EventHistory.Stage (code := code))) (scope : Scope) (actor : Party) : Finset Bool :=
  Finset.univ.filter fun value => ∃ row ∈ StageBudget.liveRecords start stages,
    ∃ key : Fin code.sites, code.siteParty key = actor ∧ (scope,value) ∈ StageBudget.labels vocabulary row key

def affected (stages : List (EventHistory.Stage (code := code))) (scope : Scope) : Finset Party :=
  (ActorEnvelope.roster start.source).filter fun actor =>
    false ∈ choices start vocabulary stages scope actor ∧ true ∈ choices start vocabulary stages scope actor
abbrev budget (stages : List (EventHistory.Stage (code := code))) (scope : Scope) :=
  (affected start vocabulary stages scope).card

theorem mem_choices_iff (stages : List (EventHistory.Stage (code := code))) (scope : Scope) (actor : Party) (value : Bool) :
    value ∈ choices start vocabulary stages scope actor ↔ ∃ row ∈ StageBudget.liveRecords start stages,
      ∃ key : Fin code.sites, code.siteParty key = actor ∧ (scope,value) ∈ StageBudget.labels vocabulary row key := by
  simp only [choices,Finset.mem_filter,Finset.mem_univ,true_and]

theorem every_actual_ballot_has_its_own_live_installed_source_word
    (stages : List (EventHistory.Stage (code := code))) (body : StageBudget.Ballot (code := code))
    (inside : body ∈ StageBudget.ledger vocabulary start stages) :
    body.actor ∈ ActorEnvelope.roster start.source ∧
      body.choice ∈ choices start vocabulary stages body.scope body.actor := by
  obtain ⟨row,member,position,made⟩ := StageBudget.ledger_origin vocabulary start stages body inside
  obtain ⟨live,owned,label⟩ := StageBudget.issued_is_in_the_actual_installed_local_word vocabulary start stages row member position body made
  have actor := ActorEnvelope.actual_ballot_retains_the_original_actor vocabulary start stages body inside
  exact ⟨Finset.mem_image.mpr ⟨body.key,Finset.mem_univ _,actor.symm⟩,
    (mem_choices_iff start vocabulary stages body.scope body.actor body.choice).mpr ⟨row,live,body.key,actor.symm,label⟩⟩

theorem conflicting_actual_aliases_or_cuts_spend_one_affected_identity
    (stages : List (EventHistory.Stage (code := code))) (scope : Scope)
    (one two : StageBudget.Ballot (code := code))
    (first : one ∈ StageBudget.ledger vocabulary start stages) (second : two ∈ StageBudget.ledger vocabulary start stages)
    (sameActor : one.actor = two.actor) (scopeOne : one.scope = scope) (scopeTwo : two.scope = scope)
    (different : one.choice ≠ two.choice) : one.actor ∈ affected start vocabulary stages scope := by
  obtain ⟨member,a⟩ := every_actual_ballot_has_its_own_live_installed_source_word start vocabulary stages one first
  have b := (every_actual_ballot_has_its_own_live_installed_source_word start vocabulary stages two second).2
  rw [scopeOne] at a
  rw [scopeTwo,← sameActor] at b
  apply Finset.mem_filter.mpr
  refine ⟨member,?_⟩
  cases firstChoice : one.choice <;> cases secondChoice : two.choice <;> simp_all

theorem actual_words_stay_within_the_original_actor_interface
    (stages : List (EventHistory.Stage (code := code))) (scope : Scope) (actor : Party) :
    choices start vocabulary stages scope actor ⊆ ActorEnvelope.choices start.source vocabulary scope actor := by
  intro value member
  obtain ⟨row,live,key,owner,label⟩ := (mem_choices_iff start vocabulary stages scope actor value).mp member
  have sameLabel : DeviationBudget.labelFor row.cursor.source vocabulary key =
      DeviationBudget.labelFor start.source vocabulary key := by funext request; rfl
  rw [StageBudget.labels,sameLabel] at label
  have registered := InterfaceDeviationEnvelope.every_generated_policy_choice_is_in_the_source_interface start.source vocabulary
    row.protocol.work.val row.protocol.work.property scope key value
    ((ProtocolCapabilityBudget.mem_choices_iff start.source row.protocol.work.val vocabulary scope key value).mpr
      ⟨row.before.frame.inbox key,label⟩)
  exact (ActorEnvelope.mem_choices_iff start.source vocabulary scope actor value).mpr ⟨key,owner,registered⟩

theorem the_actual_identity_budget_never_exceeds_the_static_source_budget
    (stages : List (EventHistory.Stage (code := code))) (scope : Scope) :
    affected start vocabulary stages scope ⊆ ActorEnvelope.affected start.source vocabulary scope := by
  intro actor member
  obtain ⟨roster,a,b⟩ := Finset.mem_filter.mp member
  have covered := actual_words_stay_within_the_original_actor_interface start vocabulary stages scope actor
  exact Finset.mem_filter.mpr ⟨roster,covered a,covered b⟩

theorem actual_extension_preserves_every_installed_actor_choice
    (past more : List (EventHistory.Stage (code := code))) (scope : Scope) (actor : Party) :
    choices start vocabulary past scope actor ⊆ choices start vocabulary (past ++ more) scope actor := by
  intro value member
  obtain ⟨row,live,key,owner,label⟩ := (mem_choices_iff start vocabulary past scope actor value).mp member
  obtain ⟨actual,paid⟩ := List.mem_filter.mp live
  apply (mem_choices_iff start vocabulary (past ++ more) scope actor value).mpr
  refine ⟨row,List.mem_filter.mpr ⟨?_,paid⟩,key,owner,label⟩
  rw [StageQueue.records_append]
  exact List.mem_append_left _ actual

theorem affected_identity_history_cannot_be_erased_by_later_stages
    (past more : List (EventHistory.Stage (code := code))) (scope : Scope) :
    affected start vocabulary past scope ⊆ affected start vocabulary (past ++ more) scope := by
  intro actor member
  obtain ⟨roster,a,b⟩ := Finset.mem_filter.mp member
  have preserved := actual_extension_preserves_every_installed_actor_choice start vocabulary past more scope actor
  exact Finset.mem_filter.mpr ⟨roster,preserved a,preserved b⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageEnvelope
