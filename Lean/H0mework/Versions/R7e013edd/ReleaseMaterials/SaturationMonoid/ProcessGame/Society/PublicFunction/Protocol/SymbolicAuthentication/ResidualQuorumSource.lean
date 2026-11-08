import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedQuorumConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualAdaptiveWindow

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualQuorumSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code start protocols encoding)
open RenewedQuorumSource (vocabulary slot)

-- Preserve the actual pre-window callbacks, keys, clocks and original attempt baseline.
def splice (future : Nat → Opponent code) (index : Nat) : Opponent code :=
  if index < 23 then RenewedQuorumConsumer.rivals index else future (index - 23)

theorem every_future_keeps_the_actual_resource_cut (future : Nat → Opponent code) (n : Nat) (bounded : n ≤ 23) :
    AdaptiveDeliveryTrace.cursorAt start protocols (splice future) n =
      AdaptiveDeliveryTrace.cursorAt start protocols RenewedQuorumConsumer.rivals n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [AdaptiveDeliveryTrace.cursorAt,ih (by omega),splice,if_pos (show n < 23 by omega)]

inductive Network where | reverse | missing | replay
  deriving DecidableEq

def environment (network : Network) : Opponent code := fun actual _ _ =>
  let cut := actual.length - (EventStep.seed start).history.length
  if network = .missing then none
  else if cut = 33 then some ⟨.deliver 3,by decide⟩
  else if cut = 37 then some ⟨.deliver 2,by decide⟩
  else if network = .replay ∧ cut = 35 then some ⟨.deliver 0,by decide⟩ else none
abbrev rivals (network : Network) := splice (fun _ => environment network)
abbrev deadline (network : Network) := ResidualAdaptiveDeadline.horizon start protocols (rivals network) 23 1 33
abbrev full (network : Network) := ResidualAdaptiveWindow.full start protocols (rivals network) 23 1 33
abbrev reception (delay : Nat) := RenewedQuorumSource.reception RenewedQuorumConsumer.resources 2 true delay
abbrev row (network : Network) (n : Nat) := AdaptiveDeliveryTrace.row start protocols (rivals network) n
abbrev current (network : Network) (n : Nat) := (AdaptiveDeliveryTrace.state start protocols (rivals network) n).current

def produce (network : Network) (allowance delay threshold : Nat) (second : Bool) :=
  ResidualAdaptiveWindow.produce start protocols (rivals network) vocabulary encoding (reception delay)
    23 allowance 33 2 (slot second) threshold

-- The prefix violation is real even when the continuation subsequently complies.
def priorReplay (index : Nat) : Opponent code :=
  if index = 17 then fun _ _ _ => some ⟨.deliver 0,by decide⟩
  else rivals .reverse index

theorem every_future_inherits_two_remaining_addresses_and_the_actual_resource_stock
    (future : Nat → Opponent code) :
    AdaptiveDeliveryTrace.rank start protocols (splice future) 23 = 2 ∧
      (AdaptiveDeliveryTrace.state start protocols (splice future) 23).current.stock 1 .service = 6 ∧
      (AdaptiveDeliveryTrace.state start protocols (splice future) 23).current.stock 0 .feedstock = 0 ∧
      ResidualAdaptiveDeadline.horizon start protocols (splice future) 23 1 33 = 41 := by
  have same := every_future_keeps_the_actual_resource_cut future 23 (by omega)
  have rank : AdaptiveDeliveryTrace.rank start protocols (splice future) 23 = 2 := by
    change (QueueScheduler.untried code (AdaptiveDeliveryTrace.baseline start)
      (EventStep.seed (AdaptiveDeliveryTrace.cursorAt start protocols (splice future) 23)).past).card = 2
    rw [same]
    decide +kernel
  refine ⟨rank,?_,?_,?_⟩
  · change (EventStep.seed (AdaptiveDeliveryTrace.cursorAt start protocols (splice future) 23)).current.stock 1 .service = 6
    rw [same];decide +kernel
  · change (EventStep.seed (AdaptiveDeliveryTrace.cursorAt start protocols (splice future) 23)).current.stock 0 .feedstock = 0
    rw [same];decide +kernel
  · change max (AdaptiveDeliveryTrace.warmup start) 33 + 2 *
      (AdaptiveDeliveryTrace.rank start protocols (splice future) 23 * (1 + 1)) = 41
    rw [rank];decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualQuorumSource
