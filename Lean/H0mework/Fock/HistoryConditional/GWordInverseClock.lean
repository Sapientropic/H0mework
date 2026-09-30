import H0mework.Fock.HistoryConditional.GWordInverseSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordInverse

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

theorem clock_balance (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) *
      SourceJointClockGraph.clock (recover depth word value) +
        ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value =
      SourceJointClockGraph.clock value := by
  change ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) *
    (((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ)⁻¹ *
      (SourceJointClockGraph.clock value - ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value)) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value = _
  rw [mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr (SourceCompiledWordOperator.slope_positive _).ne'), sub_add_cancel]

theorem clock_recover (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (recover depth word value) =
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ)⁻¹ *
        (SourceJointClockGraph.clock value -
          ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) * mass value) := rfl

end
end SourceGWordInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
