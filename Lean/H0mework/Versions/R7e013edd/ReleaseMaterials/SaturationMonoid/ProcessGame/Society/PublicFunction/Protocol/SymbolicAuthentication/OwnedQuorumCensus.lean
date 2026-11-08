import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumDomain
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 48000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumCensus
open OwnedQuorumSource OwnedQuorumDomain

def check (node : Node) : Bool :=
  decide (calculated node = .decided true) && decide ((cached node).receipts.length = 2) &&
    (node.rows.all fun row => (StageTrace.audit row).all Prod.snd) &&
    decide (node.state.current.stock 0 .feedstock = 0) &&
    decide (node.state.current.stock 1 .service = 0) &&
    decide (node.state.current.claims () 1 2 = 7) &&
    decide (((ballots node).filter fun body => decide (body.scope = RenewedQuorumSource.slot true)).length = 2)

-- Traverse source branches directly instead of retaining the entire leaf list.
def checkAll : Nat → Node → Bool :=
  Nat.rec check fun _ recur node => (controls node).all fun requested =>
    (choices node).all fun move => recur (step node requested (EventStep.fixed move))

theorem all_original_signing_supply_and_delivery_controls_finish :
    checkAll window initial = true := by decide +kernel

theorem every_generated_prefix_inherits_its_remaining_source_check
    (count remaining : Nat) (node : Node) (member : node ∈ generate count)
    (passed : checkAll (count + remaining) initial = true) : checkAll remaining node = true := by
  induction count generalizing remaining node with
  | zero => cases List.mem_singleton.mp member;simpa only [Nat.zero_add] using passed
  | succ count ih =>
    obtain ⟨before,inside,next⟩ := List.mem_flatMap.mp member
    obtain ⟨requested,selected,rest⟩ := List.mem_flatMap.mp next
    obtain ⟨move,allowed,rfl⟩ := List.mem_map.mp rest
    have earlier := ih (remaining+1) before inside (by simpa only [Nat.add_assoc,Nat.add_comm 1] using passed)
    change ((controls before).all fun requested => (choices before).all fun move =>
      checkAll remaining (step before requested (EventStep.fixed move))) = true at earlier
    exact List.all_eq_true.mp (List.all_eq_true.mp earlier requested selected) move allowed

theorem generated_success (node : Node) (member : node ∈ generate window) :
    result node = .decided true ∧ (observed node).receipts.length = 2 ∧
      (node.rows.all fun row => (StageTrace.audit row).all Prod.snd) = true ∧
      node.state.current.stock 0 .feedstock = 0 ∧ node.state.current.stock 1 .service = 0 ∧
      node.state.current.claims () 1 2 = 7 ∧
      ((ballots node).filter fun body => decide (body.scope = RenewedQuorumSource.slot true)).length = 2 := by
  have checked := every_generated_prefix_inherits_its_remaining_source_check window 0 node member
    (by simpa only [Nat.add_zero] using all_original_signing_supply_and_delivery_controls_finish)
  have valid := every_generated_node_is_source_generated window node member
  simpa only [checkAll,Nat.rec_zero,check,Bool.and_eq_true,decide_eq_true_eq,and_assoc,
    calculated_is_the_original_producer node valid,cached_is_the_actual_receiver node valid] using checked
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumCensus
