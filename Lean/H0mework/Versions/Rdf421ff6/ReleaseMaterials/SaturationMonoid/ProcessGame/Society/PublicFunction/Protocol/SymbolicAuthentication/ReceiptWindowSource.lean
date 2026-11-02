import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenTrace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptBranchCoverage

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ReceiptDrivenSource

abbrev allowance := 1
def cycle := 2 * (code .normal).sites
def separation := cycle * (allowance + 1)
def horizon := 3 * separation
abbrev initial := start .normal horizon

-- Leave a complete receiver rotation after the latest permitted fresh delivery.
-- These are public source/communication coordinates, not a test of remote Goal.
def programme : List (Rule (code .normal)) := (List.range horizon).map fun index =>
  if index = 0 then vote .normal
  else if index = cycle ∨ index = cycle + separation then send .normal
  else quiet .normal

abbrev Timing := Bool × Bool
def deliveryAt (timing : Timing) (second : Bool) :=
  cycle + (if second then separation else 0) + 1 + 2 * (if second then timing.2.toNat else timing.1.toNat)
def replyAt (timing : Timing) (second : Bool) :=
  ((List.range cycle).map (deliveryAt timing second + 1 + ·)).find?
    (fun index => decide (Distributed.Recall.Information.Agency.ownerAt (code .normal) initial.ownerStart
      ((EventStep.seed initial).history.length + index) = some 1)) |>.getD horizon

def ruleAt (timing : Timing) (index : Nat) : Rule (code .normal) :=
  if deliveryAt timing false + 1 ≤ index ∧ index ≤ replyAt timing false then ReceiptDrivenTrace.response 1
  else if deliveryAt timing true + 1 ≤ index ∧ index ≤ replyAt timing true then ReceiptDrivenTrace.response 2
  else programme[index]?.getD (quiet .normal)

def moveAt (timing : Timing) (index : Nat) : Move (code .normal) :=
  if index = deliveryAt timing false then some ⟨.deliver 0, by simp [code]⟩
  else if index = deliveryAt timing true then some ⟨.deliver 1, by simp [code]⟩ else none

def stages (timing : Timing) := (List.range horizon).map fun index =>
  (ruleAt timing index, EventStep.fixed (moveAt timing index))

def pendingAt (timing : Timing) (index : Nat) : FreshReception.Mailbox (code := code .normal) := fun site =>
  if deliveryAt timing false + 1 ≤ index ∧ index < replyAt timing false then
    FreshReception.poll vocabulary (encoding .normal) (law .normal) initial (stages timing |>.take (deliveryAt timing false + 1)) site
  else if deliveryAt timing true + 1 ≤ index ∧ index < replyAt timing true then
    FreshReception.poll vocabulary (encoding .normal) (law .normal) initial (stages timing |>.take (deliveryAt timing true + 1)) site
  else []

def path (timing : Timing) : ReceiptDrivenMaterialization.Slots (model .normal) :=
  (List.range horizon).map fun index => ⟨ruleAt timing index, moveAt timing index, pendingAt timing index⟩
def timings : List Timing := [(false, false), (false, true), (true, false), (true, true)]
def paths := timings.map path

def actual (rival : Opponent (code .normal)) := ReceiptDrivenRun.produce (model .normal) initial vocabulary
  (encoding .normal) (law .normal) allowance programme rival

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowSource
