import H0mework.Fock.HistoryModel.DynamicProbability

/-! The entire conditional source support is exactly the retained old-word fibre in the same full history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalHistory

noncomputable section

theorem source_in_whole_fibre (depth : Nat) (state : Current) :
    Complete.point depth state = previous depth (Complete.nativeNext depth) ↔
      Complete.point (depth + 1) state - Complete.nativeNext depth ∈ LinearMap.ker (previous depth) := by
  have retained := whole_next_fibre depth (Complete.point (depth + 1) state)
  rw [previous_point, ← previous_native_next] at retained
  exact retained

theorem conditional_whole_fibre (depth : Nat)
    (supported : previous depth (Complete.nativeNext depth) ∈
      (observed (Fock.sourceLaw (depth + 1)) (Complete.point depth)).support) (state : Current) :
    state ∈ (conditional (Fock.sourceLaw (depth + 1)) (Complete.point depth)
        (previous depth (Complete.nativeNext depth)) supported).support ↔
      Complete.point (depth + 1) state - Complete.nativeNext depth ∈ LinearMap.ker (previous depth) ∧
        state ∈ (Fock.sourceLaw (depth + 1)).support := by
  rw [conditional_support]
  change (Complete.point depth state = previous depth (Complete.nativeNext depth) ∧
    state ∈ (Fock.sourceLaw (depth + 1)).support) ↔ _
  rw [source_in_whole_fibre]

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
