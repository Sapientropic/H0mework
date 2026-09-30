import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver
variable {Key : Type*} [DecidableEq Key]

theorem observed_raw (bound stride : Nat) (table : Table Key)
    (frame : Frame Key bound stride) (source : Simulates bound stride table frame)
    (receipts : Nat → Key) (steps : Nat) (key : Key)
    (positive : ((SourceRetainedReceiver.run bound stride receipts frame steps).native key).1 ≠ 0) :
    decode (bound + steps) (stride + steps)
      (lookup (run bound receipts table steps) key) =
      SourceRetainedReceiver.rawAt (bound + steps) (stride + steps)
        (SourceRetainedReceiver.run bound stride receipts frame steps) key := by
  exact run_lookup bound stride table frame source receipts steps key positive

end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
