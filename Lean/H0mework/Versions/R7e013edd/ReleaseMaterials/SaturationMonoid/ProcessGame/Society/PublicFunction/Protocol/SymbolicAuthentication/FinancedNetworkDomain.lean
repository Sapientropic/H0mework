import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkDomain
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open FinancedNetworkSource

abbrev Related (left right : Node) := EnvelopeObservation.Compatible start left.stages right.stages

theorem related_states (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    left.state = right.state := by
  have states : EventStep.seed left.cursor = EventStep.seed right.cursor := by
    rw [one.1,two.1]
    exact same.1.state
  exact one.2.1.trans (states.trans two.2.1.symm)

theorem related_choices (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    choices left = choices right := by
  rw [choices_are_the_original_source_envelope left one,choices_are_the_original_source_envelope right two]
  exact EnvelopeObservation.choices_equal start _ _ same allowance

def chosen (left right : Node) (rival : Opponent code) : Move code :=
  CausalLocalDomain.chosen (EventHistory.execute start left.stages) (EventHistory.execute start right.stages) rival

theorem chosen_is_actual (left right : Node) (two : Valid right) (same : Related left right) (rival : Opponent code) :
    chosen left right rival = intake right rival := by
  unfold chosen intake
  rw [EnvelopeObservation.chosen_is_the_actual_intake start _ _ same,← two.1]

theorem compact_step (left right : Node) (same : Related left right) (rival : Opponent code) :
    Related (step left (EventStep.fixed (chosen left right rival))) (step right rival) :=
  EnvelopeObservation.compact_extension start _ _ same protocol rival

-- The callback may change its behaviour after observing its entire actual history.
theorem every_compliant_actual_callback_has_a_generated_branch
    (rivals : Nat → Opponent code) (count : Nat) (within : Within rivals count) :
    ∃ node ∈ generate count, Related node (actual rivals count) := by
  induction count with
  | zero => exact ⟨initial,List.mem_singleton_self _,EventStep.matches_self _,EnvelopeObservation.reflexive _⟩
  | succ count ih =>
    obtain ⟨node,member,same⟩ := ih (fun index bounded => within index (by omega))
    have one := generated_valid count node member
    have two := actual_valid rivals count
    let rival := rivals (actual rivals count).cursor.cut
    let move := chosen node (actual rivals count) rival
    have allowed : move ∈ choices node := by
      dsimp only [move]
      rw [related_choices node _ one two same,chosen_is_actual node _ two same]
      exact within count (by omega)
    exact ⟨step node (EventStep.fixed move),
      List.mem_flatMap.mpr ⟨node,member,List.mem_map.mpr ⟨move,allowed,rfl⟩⟩,
      compact_step node _ same rival⟩

theorem related_subjects (left right : Node) (same : Related left right) :
    StagePaymentQuorum.resolve vocabulary start left.stages scope =
      StagePaymentQuorum.resolve vocabulary start right.stages scope :=
  StagePaymentQuorum.resolve_equal vocabulary (EnvelopeObservation.communication same.2) scope

theorem related_results (left right : Node) (same : Related left right) : result left = result right := by
  have counts := QuorumObservation.count_equal start _ _ same.2
  have receivers := CommunicationObservation.run_equal vocabulary encoding start start _ _
    (EnvelopeObservation.communication same.2) reception 0 right.stages.length
  unfold result StagePaymentQuorum.produce
  rw [related_subjects left right same]
  split <;> try rfl
  split <;> try rfl
  unfold StagePaymentQuorum.received
  rw [counts,receivers]

set_option maxHeartbeats 160000000 in
-- The finite leaf check pays primitive resource and content laws; coverage above is over functions.
def checkAll : Nat → Node → Bool :=
  Nat.rec (fun node => decide (result node = .decided true expected) &&
    (node.rows.all fun row => (StageTrace.audit row).all Prod.snd) &&
    decide (node.state.current.claims () 1 2 = 9) && decide (node.state.current.stock 1 .service = 0))
    fun _ recur node => (choices node).all fun move => recur (step node (EventStep.fixed move))

set_option maxHeartbeats 160000000 in
theorem all_source_admitted_network_choices_complete_the_financed_subject :
    checkAll window initial = true := by decide +kernel

theorem generated_prefix_keeps_its_remaining_check
    (count remaining : Nat) (node : Node) (member : node ∈ generate count)
    (passed : checkAll (count+remaining) initial = true) : checkAll remaining node = true := by
  induction count generalizing remaining node with
  | zero => cases List.mem_singleton.mp member;simpa only [Nat.zero_add] using passed
  | succ count ih =>
    obtain ⟨before,inside,next⟩ := List.mem_flatMap.mp member
    obtain ⟨move,allowed,rfl⟩ := List.mem_map.mp next
    have previous := ih (remaining+1) before inside (by simpa only [Nat.add_assoc,Nat.add_comm 1] using passed)
    exact List.all_eq_true.mp previous move allowed

theorem generated_success (node : Node) (member : node ∈ generate window) :
    result node = .decided true expected ∧
      (node.rows.all fun row => (StageTrace.audit row).all Prod.snd) = true ∧
      node.state.current.claims () 1 2 = 9 ∧ node.state.current.stock 1 .service = 0 := by
  have checked := generated_prefix_keeps_its_remaining_check window 0 node member
    (by simpa only [Nat.add_zero] using all_source_admitted_network_choices_complete_the_financed_subject)
  simpa only [checkAll,Nat.rec_zero,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using checked

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkDomain
