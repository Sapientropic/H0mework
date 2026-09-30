import H0mework.Versions.X.Fock.RetainedCoarsening.Square

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (At next trajectory)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
noncomputable section

theorem merge_trajectory (runtime : LivingRuntimeState process) (frame : At runtime Fine) (read : Nat → Fine) (forget : Fine → Coarse)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) (steps : Nat) :
    merge (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val
      (trajectory runtime frame (fun offset => read (inventoryBound runtime + offset + 1)) steps) forget =
        trajectory runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget)
          (fun offset => forget (read (inventoryBound runtime + offset + 1))) steps := by
  induction steps with
  | zero => simp only [SourceRetainedReceiver.trajectory_zero, LivingRuntimeState.advance]
  | succ steps previous =>
    rw [SourceRetainedReceiver.trajectory_next, SourceRetainedReceiver.trajectory_next]
    change merge (inventoryBound (runtime.advance steps).tick.next) (maximumIndex (runtime.advance steps).tick.next).val
      (next (runtime.advance steps)
        (trajectory runtime frame (fun offset => read (inventoryBound runtime + offset + 1)) steps)
        (read (inventoryBound runtime + steps + 1))) forget =
      next (runtime.advance steps)
        (trajectory runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget)
          (fun offset => forget (read (inventoryBound runtime + offset + 1))) steps)
        (forget (read (inventoryBound runtime + steps + 1)))
    rw [SourceRetainedReceiver.receipt_at runtime read steps,
      merge_next (runtime.advance steps) _ read forget
        (SourceRetainedReceiver.trajectory_native runtime frame read source steps)
        (SourceRetainedReceiver.trajectory_keys runtime frame read keys steps), previous]

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
