import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ScopeCapabilityBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProtocolCapabilityBudget
open Distributed Reaction Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (work : source.code.Policy)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def labels (key : Fin source.code.sites) (reading : Fin source.code.signals) : List (Scope × Bool) :=
  (source.code.action work key reading).filterMap (DeviationBudget.labelFor source vocabulary key)

-- The complete registered memory interface is finite. No future callback or run is inspected.
def choices (scope : Scope) (key : Fin source.code.sites) : Finset Bool :=
  ((List.finRange source.code.signals).flatMap fun reading =>
    (labels source work vocabulary key reading).filterMap
      (fun label => if label.1 = scope then some label.2 else none)).toFinset

theorem mem_choices_iff (scope : Scope) (key : Fin source.code.sites) (value : Bool) :
    value ∈ choices source work vocabulary scope key ↔
      ∃ reading, (scope,value) ∈ labels source work vocabulary key reading := by
  simp only [choices,List.mem_toFinset,List.mem_flatMap]
  constructor
  · rintro ⟨reading,_,inside⟩
    obtain ⟨label,present,found⟩ := List.mem_filterMap.mp inside
    split_ifs at found with same
    have valueEq := Option.some.inj found
    exact ⟨reading,by simpa only [← same,← valueEq,Prod.mk.eta] using present⟩
  · rintro ⟨reading,present⟩
    exact ⟨reading,List.mem_finRange _,List.mem_filterMap.mpr ⟨(scope,value),present,by simp⟩⟩

def affected (scope : Scope) : Finset (Fin source.code.sites) :=
  Finset.univ.filter fun key => false ∈ choices source work vocabulary scope key ∧
    true ∈ choices source work vocabulary scope key

def budget (scope : Scope) : Nat := (affected source work vocabulary scope).card

theorem mem_affected_iff (scope : Scope) (key : Fin source.code.sites) :
    key ∈ affected source work vocabulary scope ↔
      false ∈ choices source work vocabulary scope key ∧ true ∈ choices source work vocabulary scope key := by
  simp only [affected,Finset.mem_filter,Finset.mem_univ,true_and]

variable (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)

theorem every_actual_scoped_choice_is_in_the_registered_interface
    (input : Input source.code) (cut : Nat) (rival : Opponent source.code)
    (scope : Scope) (horizon : Nat) (key : Fin source.code.sites) :
    ScopeCapabilityBudget.choices source input cut protocol rival vocabulary scope horizon key ⊆
      choices source protocol.work.val vocabulary scope key := by
  intro value member
  obtain ⟨n,_,_,actual⟩ := (ScopeCapabilityBudget.mem_choices_iff source input cut protocol rival vocabulary scope horizon key value).mp member
  exact (mem_choices_iff source protocol.work.val vocabulary scope key value).mpr
    ⟨(AttestationTransport.state source input cut protocol rival n).frame.inbox key,actual⟩

theorem all_actual_future_windows_are_covered_by_the_same_source_budget
    (input : Input source.code) (cut : Nat) (rival : Opponent source.code) (scope : Scope) (horizon : Nat) :
    ScopeCapabilityBudget.affected source input cut protocol rival vocabulary scope horizon ⊆
      affected source protocol.work.val vocabulary scope := by
  intro key member
  obtain ⟨first,second⟩ := (ScopeCapabilityBudget.mem_affected_iff source input cut protocol rival vocabulary scope horizon key).mp member
  have covered := every_actual_scoped_choice_is_in_the_registered_interface source vocabulary protocol input cut rival scope horizon key
  exact (mem_affected_iff source protocol.work.val vocabulary scope key).mpr ⟨covered first,covered second⟩

theorem actual_budget_never_exceeds_the_registered_budget
    (input : Input source.code) (cut : Nat) (rival : Opponent source.code) (scope : Scope) (horizon : Nat) :
    ScopeCapabilityBudget.budget source input cut protocol rival vocabulary scope horizon ≤ budget source protocol.work.val vocabulary scope :=
  Finset.card_le_card (all_actual_future_windows_are_covered_by_the_same_source_budget source vocabulary protocol input cut rival scope horizon)

theorem authenticated_choice_has_its_original_registered_work
    (input : Input source.code) (cut : Nat) (rival : Opponent source.code) (ballot : OwnedAttestation.Ballot source)
    (valid : OwnedAttestation.verify source input cut protocol rival vocabulary ballot = true) :
    ballot.choice ∈ choices source protocol.work.val vocabulary ballot.scope ballot.key := by
  have actual := (DeviationBudget.issued_body_is_in_the_actual_local_word source input cut protocol rival vocabulary
    ballot.cut ballot.position ballot (of_decide_eq_true valid)).2
  exact (mem_choices_iff source protocol.work.val vocabulary ballot.scope ballot.key ballot.choice).mpr
    ⟨(AttestationTransport.state source input cut protocol rival ballot.cut).frame.inbox ballot.key,actual⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProtocolCapabilityBudget
