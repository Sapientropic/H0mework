import H0mework.Fock.ReceivedStep.ActionBounds

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

theorem advance_coordinate (bound stride nextStride count : Nat) (selected : Bool)
    (previous : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ)
    (retained : (bound + 1) * (stride + 1) ≤ (bound + 2) * (nextStride + 1))
    (born : bound + 2 < (bound + 2) * (nextStride + 1)) (position : Nat) :
    coordinateAt (bound + 1) nextStride (advanceData bound stride nextStride count selected previous) position =
      if selected then coordinateAt bound stride previous position + ((count + 1 : Nat) : ℚ)⁻¹ *
        ((if position = bound + 2 then 1 else 0) - coordinateAt bound stride previous position)
      else coordinateAt bound stride previous position := by
  by_cases inside : position < (bound + 2) * (nextStride + 1)
  · rw [coordinateAt, dif_pos inside]
    cases selected <;> rfl
  · have oldOutside : ¬ position < (bound + 1) * (stride + 1) := by omega
    have notBirth : position ≠ bound + 2 := by omega
    rw [coordinateAt, dif_neg inside, coordinateAt, dif_neg oldOutside, if_neg notBirth]
    cases selected <;> simp

end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
