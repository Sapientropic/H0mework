import H0mework.Versions.X.Fock.RetainedReceiver.Iteration

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]

theorem run_keys (bound stride : Nat) (initial : Frame Key bound stride) (read : Nat → Key)
    (source : initial.keys = SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)) (steps : Nat) :
    (run bound stride (fun offset => read (bound + offset + 1)) initial steps).keys =
      SourceUniformFibreVariance.outputs (bound + steps) (fun actor => read actor.val) := by
  induction steps with
  | zero => exact source
  | succ steps previous =>
    change insert (read (bound + steps + 1))
      (run bound stride (fun offset => read (bound + offset + 1)) initial steps).keys =
        SourceUniformFibreVariance.outputs ((bound + steps) + 1) (fun actor => read actor.val)
    rw [previous, SourceConditionalInventory.outputs_append]

theorem started_keys (bound stride : Nat) (nonunit : stride ≠ 0) (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples bound (stride + 1)) (steps : Nat) :
    (run bound stride (fun offset => read (bound + offset + 1))
      (start bound stride nonunit (SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)) samples) steps).keys =
        SourceUniformFibreVariance.outputs (bound + steps) (fun actor => read actor.val) :=
  run_keys bound stride _ read rfl steps

end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
