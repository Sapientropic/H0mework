import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver (Raw)
open SourceReceivedConditionalStep (coordinateAt advanceData)

structure Represents (bound stride : Nat) (entry : Entry) (count : Nat) (raw : Raw bound stride) : Prop where
  count_eq : entry.count = count
  hilbert_eq : ∀ position, coordinate entry.hilbert position = (count : ℚ) * coordinateAt bound stride raw position
  mass_eq : entry.mass = (count : ℚ) * raw.2.1
  clock_eq : entry.clock = (count : ℚ) * raw.2.2

theorem represents_encode (bound stride count : Nat) (raw : Raw bound stride) :
    Represents bound stride (encode bound stride count raw) count raw :=
  ⟨rfl, encode_coordinate bound stride count raw, rfl, rfl⟩

theorem represented_decode (bound stride : Nat) (entry : Entry) (count : Nat) (raw : Raw bound stride)
    (source : Represents bound stride entry count raw) (positive : count ≠ 0) :
    decode bound stride entry = raw := by
  have nonzero : (count : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr positive
  apply Prod.ext
  · funext position
    change coordinate entry.hilbert position.val / entry.count = _
    rw [source.hilbert_eq, source.count_eq, coordinateAt, dif_pos position.isLt]
    exact mul_div_cancel_left₀ _ nonzero
  · apply Prod.ext
    · change entry.mass / entry.count = _
      rw [source.mass_eq, source.count_eq]
      exact mul_div_cancel_left₀ _ nonzero
    · change entry.clock / entry.count = _
      rw [source.clock_eq, source.count_eq]
      exact mul_div_cancel_left₀ _ nonzero

theorem advanceData_coordinate (bound stride nextStride count : Nat) (selected : Bool) (raw : Raw bound stride)
    (growth : (bound + 1) * (stride + 1) ≤ (bound + 2) * (nextStride + 1))
    (birth : bound + 2 < (bound + 2) * (nextStride + 1)) (position : Nat) :
    coordinateAt (bound + 1) nextStride (advanceData bound stride nextStride count selected raw) position =
      if selected then coordinateAt bound stride raw position + ((count + 1 : Nat) : ℚ)⁻¹ *
        ((if position = bound + 2 then 1 else 0) - coordinateAt bound stride raw position)
      else coordinateAt bound stride raw position := by
  by_cases inside : position < (bound + 2) * (nextStride + 1)
  · rw [coordinateAt, dif_pos inside]
    cases selected <;> rfl
  · have outside : ¬position < (bound + 1) * (stride + 1) := by omega
    have other : position ≠ bound + 2 := by omega
    rw [coordinateAt, dif_neg inside, coordinateAt, dif_neg outside]
    cases selected <;> simp [other]

private theorem weighted_update (count : Nat) (before born : ℚ) :
    ((count + 1 : Nat) : ℚ) * (before + ((count + 1 : Nat) : ℚ)⁻¹ * (born - before)) =
      (count : ℚ) * before + born := by
  have nonzero : ((count + 1 : Nat) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]
  push_cast
  ring

theorem represents_advance (bound stride nextStride : Nat) (entry : Entry) (count : Nat) (raw : Raw bound stride)
    (source : Represents bound stride entry count raw)
    (growth : (bound + 1) * (stride + 1) ≤ (bound + 2) * (nextStride + 1))
    (birth : bound + 2 < (bound + 2) * (nextStride + 1)) :
    Represents (bound + 1) nextStride (advance bound entry) (count + 1)
      (advanceData bound stride nextStride count true raw) := by
  refine ⟨congrArg (· + 1) source.count_eq, ?_, ?_, ?_⟩
  · intro position
    rw [advance_coordinate, source.hilbert_eq, advanceData_coordinate _ _ _ _ _ _ growth birth]
    exact (weighted_update count _ _).symm
  · change entry.mass + 1 = _
    rw [source.mass_eq]
    exact (weighted_update count _ _).symm
  · change entry.clock + (bound + 3 : ℚ) = _
    rw [source.clock_eq]
    exact (weighted_update count _ _).symm

theorem represents_retained (bound stride nextStride : Nat) (entry : Entry) (count : Nat) (raw : Raw bound stride)
    (source : Represents bound stride entry count raw)
    (growth : (bound + 1) * (stride + 1) ≤ (bound + 2) * (nextStride + 1))
    (birth : bound + 2 < (bound + 2) * (nextStride + 1)) :
    Represents (bound + 1) nextStride entry count (advanceData bound stride nextStride count false raw) := by
  refine ⟨source.count_eq, ?_, source.mass_eq, source.clock_eq⟩
  intro position
  rw [advanceData_coordinate _ _ _ _ _ _ growth birth]
  exact source.hilbert_eq position

end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
