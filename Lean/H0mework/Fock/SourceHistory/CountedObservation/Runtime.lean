import H0mework.Fock.SourceHistory.CountedObservation.Simulation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver
variable {Key : Type*} [DecidableEq Key]

theorem run_simulates (bound stride : Nat) (table : Table Key) (frame : Frame Key bound stride)
    (source : Simulates bound stride table frame)
    (receipts : Nat → Key) (steps : Nat) :
    Simulates (bound + steps) (stride + steps)
      (run bound receipts table steps)
      (SourceRetainedReceiver.run bound stride receipts frame steps) := by
  induction steps generalizing table frame with
  | zero => exact source
  | succ steps previous =>
    change Simulates (bound + (steps + 1)) (stride + (steps + 1))
      (step (bound + steps) (run bound receipts table steps) (receipts steps))
      (SourceRetainedReceiver.step (bound + steps) (stride + steps) (stride + steps + 1)
        (SourceRetainedReceiver.run bound stride receipts frame steps) (receipts steps))
    have current := previous (table := table) (frame := frame) source
    have growth : (bound + steps + 1) * (stride + steps + 1) ≤
        (bound + steps + 2) * (stride + steps + 2) := by
      exact Nat.mul_le_mul (by omega) (by omega)
    have birth : bound + steps + 2 < (bound + steps + 2) * (stride + steps + 2) := by
      have factor : 2 ≤ stride + steps + 2 := by omega
      have positive : 0 < bound + steps + 2 := by omega
      nlinarith [Nat.mul_le_mul_left (bound + steps + 2) factor]
    exact step_simulates (bound + steps) (stride + steps) (stride + steps + 1)
      (run bound receipts table steps)
      (SourceRetainedReceiver.run bound stride receipts frame steps)
      current (receipts steps) growth birth

theorem run_lookup (bound stride : Nat) (table : Table Key) (frame : Frame Key bound stride)
    (source : Simulates bound stride table frame)
    (receipts : Nat → Key) (steps : Nat) (key : Key)
    (positive : ((SourceRetainedReceiver.run bound stride receipts frame steps).native key).1 ≠ 0) :
    decode (bound + steps) (stride + steps)
      (lookup (run bound receipts table steps) key) =
      SourceRetainedReceiver.rawAt (bound + steps) (stride + steps)
        (SourceRetainedReceiver.run bound stride receipts frame steps) key := by
  exact simulated_decode (bound + steps) (stride + steps) (run bound receipts table steps)
    (SourceRetainedReceiver.run bound stride receipts frame steps)
    (run_simulates bound stride table frame source receipts steps) key positive

end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
