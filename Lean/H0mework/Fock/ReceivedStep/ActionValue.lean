import H0mework.Fock.ReceivedStep.ActionTransport
import H0mework.Fock.ReceivedStep.ActionBorn

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceCopyTimeModel (hilbert mass)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

private theorem value_ext (left right : SourceJointClockGraph.Carrier)
    (coordinates : ∀ position, hilbert left position = hilbert right position)
    (massEqual : mass left = mass right) (clockEqual : SourceJointClockGraph.clock left = SourceJointClockGraph.clock right) :
    left = right := by
  apply (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).injective
  apply Prod.ext
  · apply (WithLp.linearEquiv 2 ℂ (SourceOwnedObservationHistory.SourceShift.H × ℂ)).injective
    apply Prod.ext
    · apply Subtype.ext
      funext position
      exact coordinates position
    · exact massEqual
  · exact clockEqual

theorem next_hilbert (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (count : Nat) (selected : Bool)
    (previous : (Fin ((inventoryBound runtime + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) (position : Nat) :
    hilbert (completeValue runtime.tick.next (maximumIndex runtime.tick.next) 0 (nextData runtime index count selected previous)) position =
      if selected then hilbert (completeValue runtime index 0 previous) position + (((count + 1 : Nat) : ℚ)⁻¹ : ℂ) *
        (hilbert (SourceConditionalInventory.born (inventoryBound runtime)) position - hilbert (completeValue runtime index 0 previous) position)
      else hilbert (completeValue runtime index 0 previous) position := by
  have before := coordinate_source runtime index 0 previous position
  have after := coordinate_source runtime.tick.next (maximumIndex runtime.tick.next) 0 (nextData runtime index count selected previous) position
  have actual := congrArg (fun scalar : ℚ => (scalar : ℂ)) (next_coordinate runtime index count selected previous position)
  simp only [Nat.add_zero] at before after
  rw [← before, ← after, born_hilbert]
  simpa only [apply_ite, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_zero,
    Rat.cast_inv, Rat.cast_natCast] using actual

theorem next_value_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (count : Nat) (selected : Bool)
    (previous : (Fin ((inventoryBound runtime + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) :
    completeValue runtime.tick.next (maximumIndex runtime.tick.next) 0 (nextData runtime index count selected previous) =
      if selected then completeValue runtime index 0 previous + (((count + 1 : Nat) : ℚ)⁻¹ : ℂ) •
        (SourceConditionalInventory.born (inventoryBound runtime) - completeValue runtime index 0 previous)
      else completeValue runtime index 0 previous := by
  cases selected with
  | false =>
    change completeValue runtime.tick.next (maximumIndex runtime.tick.next) 0 (nextData runtime index count false previous) =
      completeValue runtime index 0 previous
    apply value_ext
    · exact next_hilbert runtime index count false previous
    · exact congrArg (fun value : ℚ × ℚ => (value.1 : ℂ)) (next_moments runtime index count false previous)
    · exact congrArg (fun value : ℚ × ℚ => (value.2 : ℂ)) (next_moments runtime index count false previous)
  | true =>
    change completeValue runtime.tick.next (maximumIndex runtime.tick.next) 0 (nextData runtime index count true previous) =
      completeValue runtime index 0 previous + (((count + 1 : Nat) : ℚ)⁻¹ : ℂ) •
        (SourceConditionalInventory.born (inventoryBound runtime) - completeValue runtime index 0 previous)
    apply value_ext
    · intro position
      have source := next_hilbert runtime index count true previous position
      change hilbert (completeValue runtime.tick.next (maximumIndex runtime.tick.next) 0 (nextData runtime index count true previous)) position =
        hilbert (completeValue runtime index 0 previous) position + (((count + 1 : Nat) : ℚ)⁻¹ : ℂ) *
          (hilbert (SourceConditionalInventory.born (inventoryBound runtime)) position - hilbert (completeValue runtime index 0 previous) position)
      exact source
    · have source := congrArg (fun value : ℚ × ℚ => (value.1 : ℂ)) (next_moments runtime index count true previous)
      change ((nextData runtime index count true previous).2.1 : ℂ) =
        (previous.2.1 : ℂ) + (((count + 1 : Nat) : ℚ)⁻¹ : ℂ) *
          (mass (SourceConditionalInventory.born (inventoryBound runtime)) - (previous.2.1 : ℂ))
      rw [born_mass]
      simpa only [ite_true, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast] using source
    · have source := congrArg (fun value : ℚ × ℚ => (value.2 : ℂ)) (next_moments runtime index count true previous)
      change ((nextData runtime index count true previous).2.2 : ℂ) =
        (previous.2.2 : ℂ) + (((count + 1 : Nat) : ℚ)⁻¹ : ℂ) *
          (SourceJointClockGraph.clock (SourceConditionalInventory.born (inventoryBound runtime)) - (previous.2.2 : ℂ))
      rw [born_clock]
      simpa only [ite_true, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, Rat.cast_inv,
        Rat.cast_ofNat, Nat.cast_add, Nat.cast_ofNat] using source

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
