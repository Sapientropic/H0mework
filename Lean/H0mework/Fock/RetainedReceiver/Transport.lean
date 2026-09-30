import H0mework.Fock.RetainedReceiver.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*}

def reindex {bound target stride nextStride : Nat} (bounds : bound = target) (strides : stride = nextStride)
    (frame : Frame Key bound stride) : Frame Key target nextStride :=
  bounds ▸ strides ▸ frame

theorem reindex_keys {bound target stride nextStride : Nat} (bounds : bound = target) (strides : stride = nextStride)
    (frame : Frame Key bound stride) : (reindex bounds strides frame).keys = frame.keys := by
  cases bounds
  cases strides
  rfl

theorem reindex_native {bound target stride nextStride : Nat} (bounds : bound = target) (strides : stride = nextStride)
    (frame : Frame Key bound stride) :
    (reindex bounds strides frame).native = cast (congrArg (SourceConditionalNativeObservers.State Key) bounds) frame.native := by
  cases bounds
  cases strides
  rfl

theorem reindex_raw [DecidableEq Key] {bound target stride nextStride : Nat} (bounds : bound = target) (strides : stride = nextStride)
    (frame : Frame Key bound stride) (key : Key) :
    rawAt target nextStride (reindex bounds strides frame) key =
      cast (congrArg₂ Raw bounds strides) (rawAt bound stride frame key) := by
  cases bounds
  cases strides
  rfl

theorem reindex_trans {a b c u v w : Nat} (ab : a = b) (bc : b = c) (uv : u = v) (vw : v = w)
    (frame : Frame Key a u) :
    reindex bc vw (reindex ab uv frame) = reindex (ab.trans bc) (uv.trans vw) frame := by
  cases ab
  cases bc
  cases uv
  cases vw
  rfl

theorem step_reindex [DecidableEq Key] {a b u v w z : Nat} (bounds : a = b) (strides : u = v) (targets : w = z)
    (frame : Frame Key a u) (added : Key) :
    step b v z (reindex bounds strides frame) added =
      reindex (congrArg (fun n => n + 1) bounds) targets (step a u w frame added) := by
  cases bounds
  cases strides
  cases targets
  rfl

end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
