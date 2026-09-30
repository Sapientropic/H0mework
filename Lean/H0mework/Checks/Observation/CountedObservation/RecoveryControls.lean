import H0mework.Fock.SourceHistory.CountedRecovery.Energy

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedRecovery

open SourceGeneratedAcquisitionContinuation
open SourceRetainedReceiver (At next residual)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

example (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    residualMass runtime.tick.next (next runtime frame (read runtime.tick.next.state)) read ≤
      residualMass runtime frame read := by
  rw [residual_mass_next runtime frame read source]
  apply sub_le_self
  positivity

example (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (fresh : (frame.native (read runtime.tick.next.state)).1 = 0) :
    error runtime.tick.next (next runtime frame (read runtime.tick.next.state)) read =
      error runtime frame read + SourceConditionalNativeBirth.innovation runtime read := by
  rw [error_update runtime frame read source, fresh]
  simp only [Nat.cast_zero, zero_div, zero_mul, sub_zero]

example (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (present : 0 < (frame.native (read runtime.tick.next.state)).1)
    (noisy : residual runtime frame (read runtime.tick.next.state) ≠ 0) :
    residualMass runtime.tick.next (next runtime frame (read runtime.tick.next.state)) read <
      residualMass runtime frame read := by
  rw [residual_mass_next runtime frame read source]
  apply sub_lt_self
  apply mul_pos
  · exact div_pos (Nat.cast_pos.mpr present) (by positivity)
  · exact pow_pos (norm_pos_iff.mpr noisy) 2

#print axioms residual_mass_next
#print axioms error_update

end
end SourceCountedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
