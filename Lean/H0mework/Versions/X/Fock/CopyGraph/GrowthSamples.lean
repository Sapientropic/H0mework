import H0mework.Versions.X.Fock.CopyGraph.GrowthSource
import H0mework.Probability.HistoryGrowth.Conditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceHistoryGrowth
noncomputable section

theorem normalized_at (depth : Nat) (value : Space (historyPMF depth)) (actor : Fin (depth + 2)) :
    normalizedInclusion (Nat.le_succ depth) value actor =
      (Real.sqrt (fraction depth (depth + 1)))⁻¹ • extend (Nat.le_succ depth) value actor :=
  ae_at_support (historyPMF (depth + 1)) actor (source_positive (depth + 1) actor)
    (MeasureTheory.Lp.coeFn_smul (Real.sqrt (fraction depth (depth + 1)))⁻¹ (extend (Nat.le_succ depth) value))

theorem normalized_prior (depth : Nat) (value : Space (historyPMF depth)) (actor : Fin (depth + 1)) :
    normalizedInclusion (Nat.le_succ depth) value (includeActor (Nat.le_succ depth) actor) =
      (Real.sqrt (fraction depth (depth + 1)))⁻¹ • value actor := by
  rw [normalized_at, extend_at]

theorem normalized_new (depth : Nat) (value : Space (historyPMF depth)) :
    normalizedInclusion (Nat.le_succ depth) value (Fin.last (depth + 1)) = 0 := by
  rw [normalized_at, extend_at_new (Nat.le_succ depth) _ _ (by rfl), smul_zero]

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
