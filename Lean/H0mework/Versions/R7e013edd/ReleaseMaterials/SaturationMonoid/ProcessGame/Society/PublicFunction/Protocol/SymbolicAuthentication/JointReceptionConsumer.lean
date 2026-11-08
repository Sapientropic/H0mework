import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionProgress

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage JointReceptionSource JointReceptionProgress

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)}
 (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law root) (origin : Cursor root) (past : List (EventHistory.Stage (code := root)))
 (scope : Scope) (value : Bool)

def addressedActors (recipient : Fin root.sites) : Finset Party :=
 ((targets vocabulary origin past scope value).filter fun task => task.1=recipient).image Prod.snd

theorem complete_joint_delivery_supplies_each_original_addressed_actor
 (state : JointReceptionSource.State root)
 (complete : pending vocabulary law origin past scope value state=∅) (recipient : Fin root.sites) :
 addressedActors vocabulary origin past scope value recipient ⊆
 ActorQuorum.support (observed vocabulary law origin past state recipient) scope value := by
 intro actor inside
 obtain ⟨⟨address,owner⟩,member,rfl⟩ := Finset.mem_image.mp inside
 obtain ⟨target,same⟩ := Finset.mem_filter.mp member
 dsimp only at same ⊢
 subst address
 by_contra missing
 have unpaid : (recipient,owner)∈pending vocabulary law origin past scope value state :=
  Finset.mem_filter.mpr ⟨target,missing⟩
 rw [complete] at unpaid
 exact Finset.notMem_empty _ unpaid

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem enough_distinct_actors_generate_a_decision
 (received : HeaderReception.Receiver (code := root)) (threshold : Nat)
 (positive : 0<threshold) (enough : threshold≤(ActorQuorum.support received scope value).card) :
 ∃ answer, ActorQuorum.readout received scope threshold=.decided answer := by
 unfold ActorQuorum.readout
 rw [if_neg (Nat.ne_of_gt positive)]
 cases found : [false,true].find? (fun choice => decide (threshold≤(ActorQuorum.support received scope choice).card)) with
 | some answer => exact ⟨answer,rfl⟩
 | none =>
   have absent := (List.find?_eq_none.mp found) value (by cases value <;> simp)
   simp only [enough,decide_true] at absent
   contradiction

def produce (state : JointReceptionSource.State root) (recipient : Fin root.sites)
 (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
 if ¬(ActorEnvelope.roster origin.source).card+ActorStageEnvelope.budget origin vocabulary past scope<threshold+threshold then
  .blocked .unsafeSourceBudget
 else match ActorQuorum.readout (observed vocabulary law origin past state recipient) scope threshold with
 | .blocked => .blocked .missingQuorum
 | .decided answer => .decided answer

theorem actual_joint_completion_generates_source_budget_decisions
 (state : JointReceptionSource.State root)
 (complete : pending vocabulary law origin past scope value state=∅)
 (threshold : Nat) (positive : 0<threshold)
 (safe : (ActorEnvelope.roster origin.source).card+ActorStageEnvelope.budget origin vocabulary past scope<threshold+threshold)
 (recipient : Fin root.sites)
 (enough : threshold≤(addressedActors vocabulary origin past scope value recipient).card) :
 ∃ answer, produce vocabulary law origin past state recipient scope threshold=.decided answer := by
 have supported := Finset.card_le_card
  (complete_joint_delivery_supplies_each_original_addressed_actor vocabulary law origin past scope value state complete recipient)
 obtain ⟨answer,readout⟩ := enough_distinct_actors_generate_a_decision scope value
  (observed vocabulary law origin past state recipient) threshold positive (Nat.le_trans enough supported)
 refine ⟨answer,?_⟩
 unfold produce
 rw [if_neg (not_not.mpr safe),readout]

variable (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

theorem recurrent_actual_opportunities_generate_joint_quorum_at_one_finite_endpoint
 (start : JointReceptionSource.State root)
 (external : Nat → JointReceptionSource.State root → RenewableArchiveSource.Command)
 (opportunities : ∀ index,
  (pending vocabulary law origin past scope value
   (JointReceptionSource.run vocabulary law origin past scope value contract start external index)).Nonempty →
  ∃ delay task, task∈menu (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay)) ∧
   offer vocabulary law origin past scope value
    (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay)) task=true)
 (threshold : Nat) (positive : 0<threshold)
 (safe : (ActorEnvelope.roster origin.source).card+ActorStageEnvelope.budget origin vocabulary past scope<threshold+threshold) :
 ∃ index, ∀ recipient : Fin root.sites,
 threshold≤(addressedActors vocabulary origin past scope value recipient).card →
 ∃ answer, produce vocabulary law origin past
  (JointReceptionSource.run vocabulary law origin past scope value contract start external index)
   recipient scope threshold=.decided answer := by
 obtain ⟨index,complete⟩ := recurrent_actual_menu_opportunities_generate_finite_joint_completion
  vocabulary law origin past scope value contract start external opportunities
 exact ⟨index,fun recipient enough => actual_joint_completion_generates_source_budget_decisions
  vocabulary law origin past scope value _ complete threshold positive safe recipient enough⟩

theorem every_actual_cumulative_receipt_has_the_original_paid_source
 (state : JointReceptionSource.State root) (recipient : Fin root.sites)
 (receipt : HeaderReception.Receipt (code := root))
 (inside : receipt∈(observed vocabulary law origin past state recipient).receipts) :
 receipt.wire.ballot∈StageBudget.ledger vocabulary origin past :=
 RenewableHistoryReception.all_received_ballots_keep_the_original_paid_issuing_ledger _ _ _ _ _ _ _ _ (by simp) receipt inside

private theorem actor_source (state : JointReceptionSource.State root) (recipient : Fin root.sites)
 (scope : Scope) (choice : Bool) (actor : Party)
 (inside : actor∈ActorQuorum.support (observed vocabulary law origin past state recipient) scope choice) :
 ∃ ballot∈StageBudget.ledger vocabulary origin past,
 ballot.actor=actor ∧ ballot.scope=scope ∧ ballot.choice=choice := by
 obtain ⟨key,member,owner⟩ := (ActorQuorum.mem_support_iff _ _ _ _).mp inside
 obtain ⟨receipt,present,sameScope,value,sameKey⟩ := (StageQuorum.mem_support_iff _ _ _ _).mp member
 have paid := every_actual_cumulative_receipt_has_the_original_paid_source vocabulary law origin past state recipient receipt present
 have signed := ActorEnvelope.actual_ballot_retains_the_original_actor vocabulary origin past _ paid
 exact ⟨receipt.wire.ballot,paid,by rw [signed,sameKey,owner],sameScope,value⟩

theorem generated_decision_requires_positive_actual_quorum_and_source_budget
 (state : JointReceptionSource.State root) (recipient : Fin root.sites) (scope : Scope) (threshold : Nat) (answer : Bool)
 (done : produce vocabulary law origin past state recipient scope threshold=.decided answer) :
 (ActorEnvelope.roster origin.source).card+ActorStageEnvelope.budget origin vocabulary past scope<threshold+threshold ∧
 0<threshold ∧ threshold≤(ActorQuorum.support (observed vocabulary law origin past state recipient) scope answer).card := by
 unfold produce at done
 split at done <;> try contradiction
 rename_i safe
 split at done <;> try contradiction
 rename_i selected chosen
 cases done
 exact ⟨of_not_not safe,ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ chosen⟩

theorem all_generated_endpoint_decisions_agree
 (one two : JointReceptionSource.State root) (left right : Fin root.sites)
 (scope : Scope) (threshold : Nat) (a b : Bool)
 (first : produce vocabulary law origin past one left scope threshold=.decided a)
 (second : produce vocabulary law origin past two right scope threshold=.decided b) : a=b := by
 obtain ⟨safe,_,supportOne⟩ := generated_decision_requires_positive_actual_quorum_and_source_budget vocabulary law origin past one left scope threshold a first
 obtain ⟨_,_,supportTwo⟩ := generated_decision_requires_positive_actual_quorum_and_source_budget vocabulary law origin past two right scope threshold b second
 by_contra different
 let A := ActorQuorum.support (observed vocabulary law origin past one left) scope a
 let B := ActorQuorum.support (observed vocabulary law origin past two right) scope b
 have overlap : A∩B ⊆ ActorStageEnvelope.affected origin vocabulary past scope := by
  intro actor member
  obtain ⟨r,rPaid,rActor,rScope,rChoice⟩ := actor_source vocabulary law origin past one left scope a actor (Finset.mem_inter.mp member).1
  obtain ⟨s,sPaid,sActor,sScope,sChoice⟩ := actor_source vocabulary law origin past two right scope b actor (Finset.mem_inter.mp member).2
  have affected := ActorStageEnvelope.conflicting_actual_aliases_or_cuts_spend_one_affected_identity origin vocabulary past scope r s rPaid sPaid
   (rActor.trans sActor.symm) rScope sScope (by intro same;exact different (rChoice.symm.trans (same.trans sChoice)))
  simpa only [rActor] using affected
 have subset (received : HeaderReception.Receiver (code := root)) (choice : Bool) :
  ActorQuorum.support received scope choice ⊆ ActorEnvelope.roster origin.source := by
   intro actor member
   obtain ⟨key,_,owner⟩ := (ActorQuorum.mem_support_iff _ _ _ _).mp member
   exact Finset.mem_image.mpr ⟨key,Finset.mem_univ _,owner⟩
 have unionBound := Finset.card_le_card (Finset.union_subset
  (subset (observed vocabulary law origin past one left) a) (subset (observed vocabulary law origin past two right) b))
 have intersectionBound := Finset.card_le_card overlap
 have count := Finset.card_union_add_card_inter A B
 change threshold≤A.card at supportOne
 change threshold≤B.card at supportTwo
 change (A∪B).card≤_ at unionBound
 unfold ActorStageEnvelope.budget at safe
 omega

theorem each_generated_endpoint_keeps_its_whole_ledger_and_own_next
 (state : JointReceptionSource.State root) :
 ArchivedDeliveryConsumer.NativeContinuation state.actual.model state.actual.point := by
 unfold ArchivedDeliveryConsumer.NativeContinuation
 exact (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
  state.actual.model state.actual.point).2.2.2

theorem recurrent_opportunities_generate_a_common_decision_and_actual_continuation
 (start : JointReceptionSource.State root)
 (external : Nat → JointReceptionSource.State root → RenewableArchiveSource.Command)
 (opportunities : ∀ index,
  (pending vocabulary law origin past scope value
   (JointReceptionSource.run vocabulary law origin past scope value contract start external index)).Nonempty →
  ∃ delay task, task∈menu (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay)) ∧
   offer vocabulary law origin past scope value
    (JointReceptionSource.run vocabulary law origin past scope value contract start external (index+delay)) task=true)
 (threshold : Nat) (positive : 0<threshold)
 (safe : (ActorEnvelope.roster origin.source).card+ActorStageEnvelope.budget origin vocabulary past scope<threshold+threshold)
 (reference : Fin root.sites)
 (enough : threshold≤(addressedActors vocabulary origin past scope value reference).card) :
 ∃ index answer,
 (∀ recipient, threshold≤(addressedActors vocabulary origin past scope value recipient).card →
  produce vocabulary law origin past
   (JointReceptionSource.run vocabulary law origin past scope value contract start external index)
   recipient scope threshold=.decided answer) ∧
 ArchivedDeliveryConsumer.NativeContinuation
  (JointReceptionSource.run vocabulary law origin past scope value contract start external index).actual.model
  (JointReceptionSource.run vocabulary law origin past scope value contract start external index).actual.point := by
 obtain ⟨index,decisions⟩ := recurrent_actual_opportunities_generate_joint_quorum_at_one_finite_endpoint
  vocabulary law origin past scope value contract start external opportunities threshold positive safe
 obtain ⟨answer,first⟩ := decisions reference enough
 refine ⟨index,answer,?_,each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩
 intro recipient supported
 obtain ⟨other,second⟩ := decisions recipient supported
 have same := all_generated_endpoint_decisions_agree vocabulary law origin past _ _ reference recipient scope threshold answer other first second
 simpa only [same] using second

include contract in
theorem zero_timing_cannot_select_an_executable_service
 (state : JointReceptionSource.State root) (zero : law.maxDelay=0)
 (task : Fin root.sites × LocalCommandSource.Input)
 (chosen : selected vocabulary law origin past scope value state=some task) : False := by
 obtain ⟨wire,_,_,_,checked,_⟩ := selected_service_delivers_a_previously_missing_original_identity
  vocabulary law origin past scope value contract state task chosen
 obtain ⟨_,_,earlier,_,_,_,_,deadline,_,_⟩ := RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ checked
 rw [zero,Nat.add_zero] at deadline
 omega

include contract in
theorem an_already_supported_actor_cannot_pay_for_another_service
 (state : JointReceptionSource.State root) (task : Fin root.sites × LocalCommandSource.Input)
 (chosen : selected vocabulary law origin past scope value state=some task) :
 ∃ actor, actor∉ActorQuorum.support (observed vocabulary law origin past state task.1) scope value ∧
  (task.1,actor)∈targets vocabulary origin past scope value := by
 obtain ⟨wire,missing,_,_,_,_⟩ := selected_service_delivers_a_previously_missing_original_identity
  vocabulary law origin past scope value contract state task chosen
 obtain ⟨target,fresh⟩ := Finset.mem_filter.mp missing
 exact ⟨_,fresh,target⟩

theorem an_unsafe_original_budget_cannot_become_a_decision
 (state : JointReceptionSource.State root) (recipient : Fin root.sites) (scope : Scope) (threshold : Nat)
 (overBudget : ¬(ActorEnvelope.roster origin.source).card+ActorStageEnvelope.budget origin vocabulary past scope<threshold+threshold) :
 produce vocabulary law origin past state recipient scope threshold=.blocked .unsafeSourceBudget := by
 simp only [produce,if_pos overBudget]

theorem missing_received_quorum_cannot_be_replaced_by_original_target_count
 (state : JointReceptionSource.State root) (recipient : Fin root.sites) (scope : Scope) (threshold : Nat) (answer : Bool)
 (short : (ActorQuorum.support (observed vocabulary law origin past state recipient) scope answer).card<threshold) :
 produce vocabulary law origin past state recipient scope threshold≠.decided answer := by
 intro done
 have supported := (generated_decision_requires_positive_actual_quorum_and_source_budget vocabulary law origin past state recipient scope threshold answer done).2.2
 omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionConsumer
