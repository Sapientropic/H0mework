import H0mework.Fock.SourceHistory.CountedObservation.Entry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

theorem encode_coordinate (bound stride count : Nat) (raw : SourceRetainedReceiver.Raw bound stride) (position : Nat) :
    coordinate (encode bound stride count raw).hilbert position =
      (count : ℚ) * SourceReceivedConditionalStep.coordinateAt bound stride raw position := by
  dsimp only [coordinate, encode, SourceReceivedConditionalStep.coordinateAt]
  rw [Array.getElem?_ofFn]
  split_ifs <;> simp

private theorem average_update (count : Nat) (previous born : ℚ) :
    ((count : ℚ) * previous + born) / ((count + 1 : Nat) : ℚ) =
      previous + ((count + 1 : Nat) : ℚ)⁻¹ * (born - previous) := by
  have nonzero : ((count + 1 : Nat) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  field_simp
  push_cast
  ring

theorem advance_decode_encoded (bound stride nextStride count : Nat) (raw : SourceRetainedReceiver.Raw bound stride) :
    decode (bound + 1) nextStride (advance bound (encode bound stride count raw)) =
      SourceReceivedConditionalStep.advanceData bound stride nextStride count true raw := by
  apply Prod.ext
  · funext position
    change coordinate (advance bound (encode bound stride count raw)).hilbert position.val /
      ((count + 1 : Nat) : ℚ) = _
    rw [advance_coordinate, encode_coordinate]
    exact average_update count _ _
  · apply Prod.ext
    · exact average_update count _ _
    · exact average_update count _ _

end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
