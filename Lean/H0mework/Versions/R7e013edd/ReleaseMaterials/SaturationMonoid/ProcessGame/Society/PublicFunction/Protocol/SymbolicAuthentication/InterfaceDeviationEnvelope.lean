import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageSourceAdmission

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterfaceDeviationEnvelope
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

-- The registered request alphabet bounds every generated policy; no policy-table search is needed.
def choices (scope : Scope) (key : Fin source.code.sites) : Finset Bool :=
  Finset.univ.filter fun value => decide ((scope,value) ∈
    source.code.actions.filterMap (DeviationBudget.labelFor source vocabulary key))

theorem mem_choices_iff (scope : Scope) (key : Fin source.code.sites) (value : Bool) :
    value ∈ choices source vocabulary scope key ↔
      (scope,value) ∈ source.code.actions.filterMap (DeviationBudget.labelFor source vocabulary key) := by
  simp only [choices,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]

theorem every_interface_choice_has_a_registered_request
    (scope : Scope) (key : Fin source.code.sites) (value : Bool)
    (inside : value ∈ choices source vocabulary scope key) :
    ∃ request ∈ source.code.actions,
      DeviationBudget.labelFor source vocabulary key request = some (scope,value) :=
  List.mem_filterMap.mp ((mem_choices_iff source vocabulary scope key value).mp inside)

theorem every_generated_policy_choice_is_in_the_source_interface
    (work : source.code.Policy) (generated : work ∈ source.code.policies)
    (scope : Scope) (key : Fin source.code.sites) (value : Bool)
    (possible : value ∈ ProtocolCapabilityBudget.choices source work vocabulary scope key) :
    value ∈ choices source vocabulary scope key := by
  obtain ⟨reading,labelled⟩ := (ProtocolCapabilityBudget.mem_choices_iff source work vocabulary scope key value).mp possible
  obtain ⟨request,present,label⟩ := List.mem_filterMap.mp labelled
  have supported : source.code.action work key reading ∈ words source.code.actions source.code.actionLimit := by
    unfold Code.action
    split
    · exact (List.mem_pi _ _).mp generated (key,reading) (source.code.key_mem _)
    · exact (mem_words_iff _ _ _).mpr (by simp)
  exact (mem_choices_iff source vocabulary scope key value).mpr
    (List.mem_filterMap.mpr ⟨request,((mem_words_iff _ _ _).mp supported).2 request present,label⟩)

def affected (scope : Scope) : Finset (Fin source.code.sites) :=
  Finset.univ.filter fun key => false ∈ choices source vocabulary scope key ∧
    true ∈ choices source vocabulary scope key

def budget (scope : Scope) : Nat := (affected source vocabulary scope).card

theorem mem_affected_iff (scope : Scope) (key : Fin source.code.sites) :
    key ∈ affected source vocabulary scope ↔
      false ∈ choices source vocabulary scope key ∧ true ∈ choices source vocabulary scope key := by
  simp only [affected,Finset.mem_filter,Finset.mem_univ,true_and]

variable {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)

theorem every_actual_ballot_is_in_the_source_generated_interface
    (stages : List (EventHistory.Stage (code := code)))
    (body : StageBudget.Ballot (code := code))
    (inside : body ∈ StageBudget.ledger vocabulary start stages) :
    body.choice ∈ choices start.source vocabulary body.scope body.key := by
  obtain ⟨row,member,position,made⟩ := StageBudget.ledger_origin vocabulary start stages body inside
  have labelled := (StageBudget.issued_is_in_the_actual_installed_local_word vocabulary start stages row member position body made).2.2
  have sameLabel : DeviationBudget.labelFor row.cursor.source vocabulary body.key =
      DeviationBudget.labelFor start.source vocabulary body.key := by
    funext request
    rfl
  rw [StageBudget.labels,sameLabel] at labelled
  exact every_generated_policy_choice_is_in_the_source_interface start.source vocabulary
    row.protocol.work.val row.protocol.work.property body.scope body.key body.choice
    ((ProtocolCapabilityBudget.mem_choices_iff start.source row.protocol.work.val vocabulary body.scope body.key body.choice).mpr
      ⟨row.before.frame.inbox body.key,labelled⟩)

theorem conflicting_actual_ballots_expose_a_source_affected_key
    (left right : List (EventHistory.Stage (code := code))) (scope : Scope)
    (one two : StageBudget.Ballot (code := code))
    (first : one ∈ StageBudget.ledger vocabulary start left)
    (second : two ∈ StageBudget.ledger vocabulary start right)
    (sameKey : one.key = two.key) (scopeOne : one.scope = scope) (scopeTwo : two.scope = scope)
    (different : one.choice ≠ two.choice) :
    one.key ∈ affected start.source vocabulary scope := by
  have a := every_actual_ballot_is_in_the_source_generated_interface vocabulary start left one first
  have b := every_actual_ballot_is_in_the_source_generated_interface vocabulary start right two second
  rw [scopeOne] at a
  rw [scopeTwo,← sameKey] at b
  apply (mem_affected_iff start.source vocabulary scope one.key).mpr
  cases firstChoice : one.choice <;> cases secondChoice : two.choice <;> simp_all

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterfaceDeviationEnvelope
