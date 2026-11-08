import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BallotQuorum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ScopeCapabilityBudget
open Distributed Reaction Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

-- Capability is read before receiver certificates, at actual owned activation cuts.
-- Admission and payment still decide which selected labels become attestations.
def choices (scope : Scope) (horizon : Nat) (key : Fin source.code.sites) : Finset Bool :=
  ((List.range horizon).flatMap fun n =>
    if OwnedAttestation.owner source input cut protocol rival n = some key then
      (DeviationBudget.labelsAt source input cut protocol rival vocabulary n key).filterMap
        (fun label => if label.1 = scope then some label.2 else none)
    else []).toFinset

theorem mem_choices_iff (scope : Scope) (horizon : Nat) (key : Fin source.code.sites) (value : Bool) :
    value ∈ choices source input cut protocol rival vocabulary scope horizon key ↔
    ∃ n < horizon, OwnedAttestation.owner source input cut protocol rival n = some key ∧
      (scope,value) ∈ DeviationBudget.labelsAt source input cut protocol rival vocabulary n key := by
  simp only [choices,List.mem_toFinset,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨n,inside,member⟩
    split_ifs at member with owned
    · obtain ⟨label,present,found⟩ := List.mem_filterMap.mp member
      split_ifs at found with same
      have valueEq := Option.some.inj found
      exact ⟨n,inside,owned,by simpa only [← same,← valueEq,Prod.mk.eta] using present⟩
    · simp at member
  · rintro ⟨n,inside,owned,present⟩
    refine ⟨n,inside,?_⟩
    rw [if_pos owned]
    exact List.mem_filterMap.mpr ⟨(scope,value),present,by simp⟩

def affected (scope : Scope) (horizon : Nat) : Finset (Fin source.code.sites) :=
  Finset.univ.filter fun key => false ∈ choices source input cut protocol rival vocabulary scope horizon key ∧
    true ∈ choices source input cut protocol rival vocabulary scope horizon key

def budget (scope : Scope) (horizon : Nat) : Nat :=
  (affected source input cut protocol rival vocabulary scope horizon).card

theorem mem_affected_iff (scope : Scope) (horizon : Nat) (key : Fin source.code.sites) :
    key ∈ affected source input cut protocol rival vocabulary scope horizon ↔
    false ∈ choices source input cut protocol rival vocabulary scope horizon key ∧
      true ∈ choices source input cut protocol rival vocabulary scope horizon key := by
  simp only [affected,Finset.mem_filter,Finset.mem_univ,true_and]

theorem every_scoped_capability_is_in_the_original_source_budget (scope : Scope) (horizon : Nat) :
    affected source input cut protocol rival vocabulary scope horizon ⊆
      DeviationBudget.affectedThrough source input cut protocol rival vocabulary horizon := by
  intro key member
  obtain ⟨first,second⟩ := (mem_affected_iff source input cut protocol rival vocabulary scope horizon key).mp member
  obtain ⟨n,inside,owned,negative⟩ := (mem_choices_iff source input cut protocol rival vocabulary scope horizon key false).mp first
  obtain ⟨m,later,_,positive⟩ := (mem_choices_iff source input cut protocol rival vocabulary scope horizon key true).mp second
  by_contra unaffected
  have same := (DeviationBudget.unaffected_view_is_constant source input cut protocol rival vocabulary horizon key unaffected n (by omega)).trans
    (DeviationBudget.unaffected_view_is_constant source input cut protocol rival vocabulary horizon key unaffected m (by omega)).symm
  have together : (scope,true) ∈ DeviationBudget.labelsAt source input cut protocol rival vocabulary n key := by
    change DeviationBudget.labelsAt source input cut protocol rival vocabulary n key = _ at same
    rw [same]
    exact positive
  have hazard := (DeviationBudget.contradictory_iff _).mpr
    ⟨(scope,false),negative,(scope,true),together,rfl,by change false ≠ true; decide⟩
  exact unaffected ((DeviationBudget.affected_iff_source_change_or_actual_work_hazard source input cut protocol rival vocabulary horizon key).mpr
    ⟨n,inside,Or.inr ⟨owned,hazard⟩⟩)

theorem budget_never_exceeds_the_original_source_budget (scope : Scope) (horizon : Nat) :
    budget source input cut protocol rival vocabulary scope horizon ≤
      DeviationBudget.budget source input cut protocol rival vocabulary horizon :=
  Finset.card_le_card (every_scoped_capability_is_in_the_original_source_budget source input cut protocol rival vocabulary scope horizon)

theorem authenticated_equivocation_exposes_actual_scoped_capability (horizon : Nat)
    (one two : OwnedAttestation.Ballot source)
    (first : OwnedAttestation.verify source input cut protocol rival vocabulary one = true)
    (second : OwnedAttestation.verify source input cut protocol rival vocabulary two = true)
    (firstInside : one.cut < horizon) (secondInside : two.cut < horizon)
    (sameKey : one.key = two.key) (sameScope : one.scope = two.scope) (different : one.choice ≠ two.choice) :
    one.key ∈ affected source input cut protocol rival vocabulary one.scope horizon := by
  obtain ⟨owned,firstLabel⟩ := DeviationBudget.issued_body_is_in_the_actual_local_word source input cut protocol rival vocabulary
    one.cut one.position one (of_decide_eq_true first)
  obtain ⟨other,secondLabel⟩ := DeviationBudget.issued_body_is_in_the_actual_local_word source input cut protocol rival vocabulary
    two.cut two.position two (of_decide_eq_true second)
  have a := (mem_choices_iff source input cut protocol rival vocabulary one.scope horizon one.key one.choice).mpr
    ⟨one.cut,firstInside,owned,firstLabel⟩
  have b := (mem_choices_iff source input cut protocol rival vocabulary one.scope horizon one.key two.choice).mpr
    ⟨two.cut,secondInside,by simpa only [sameKey] using other,by simpa only [sameKey,sameScope] using secondLabel⟩
  apply (mem_affected_iff source input cut protocol rival vocabulary one.scope horizon one.key).mpr
  cases firstChoice : one.choice <;> cases secondChoice : two.choice <;> simp_all

variable (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

theorem conflicting_support_exposes_the_actual_scoped_source_budget
    (left right : Fin source.code.sites) (leftCount rightCount horizon : Nat)
    (leftBound : leftCount ≤ horizon) (rightBound : rightCount ≤ horizon)
    (scope : Scope) (a b : Bool) (different : a ≠ b) :
    BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∩
      BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b ⊆
        affected source input cut protocol rival vocabulary scope horizon := by
  intro key member
  obtain ⟨one,present,scopeOne,valueOne,keyOne⟩ := (BallotQuorum.mem_support_iff source _ scope a key).mp (Finset.mem_inter.mp member).1
  obtain ⟨two,received,scopeTwo,valueTwo,keyTwo⟩ := (BallotQuorum.mem_support_iff source _ scope b key).mp (Finset.mem_inter.mp member).2
  obtain ⟨authOne,boundOne⟩ := BallotQuorum.receipt_ballot_has_actual_origin source input cut protocol rival vocabulary encoding law left leftCount one present
  obtain ⟨authTwo,boundTwo⟩ := BallotQuorum.receipt_ballot_has_actual_origin source input cut protocol rival vocabulary encoding law right rightCount two received
  have exposed := authenticated_equivocation_exposes_actual_scoped_capability source input cut protocol rival vocabulary horizon
    one.wire.ballot two.wire.ballot authOne authTwo (by omega) (by omega) (keyOne.trans keyTwo.symm)
    (scopeOne.trans scopeTwo.symm) (by intro equal; exact different (valueOne.symm.trans (equal.trans valueTwo)))
  simpa only [scopeOne,keyOne] using exposed

theorem agreement_from_actual_scoped_capability
    (left right : Fin source.code.sites) (leftCount rightCount horizon : Nat)
    (leftBound : leftCount ≤ horizon) (rightBound : rightCount ≤ horizon)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : BallotQuorum.readout source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope threshold = .decided a)
    (two : BallotQuorum.readout source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope threshold = .decided b)
    (safe : source.code.sites + budget source input cut protocol rival vocabulary scope horizon < threshold + threshold) : a = b := by
  by_contra different
  have first := (BallotQuorum.decided_has_positive_quorum source _ scope threshold a one).2
  have second := (BallotQuorum.decided_has_positive_quorum source _ scope threshold b two).2
  have exposed := Finset.card_le_card (conflicting_support_exposes_the_actual_scoped_source_budget source input cut protocol rival vocabulary encoding law
    left right leftCount rightCount horizon leftBound rightBound scope a b different)
  have unionBound : (BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∪
      BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b).card ≤ source.code.sites := by
    simpa only [Fintype.card_fin] using (BallotQuorum.support source
      (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∪
        BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b).card_le_univ
  have count := Finset.card_union_add_card_inter
    (BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a)
    (BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b)
  unfold budget at safe
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ScopeCapabilityBudget
