import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Conditional.Coarsening.Residual

/-! Actual history size determines the cost; noninjectivity alone cannot assert positive loss. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePulseCoarsening

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
noncomputable section

theorem positive_coarsening_loss (bound : Nat) (positive : 0 < bound) :
    error (historyPMF bound) (observe bound) (clockTask bound) (currentDecoder bound) <
      error (historyPMF bound) (nextObserve bound) (clockTask bound) (nextDecoder bound) := by
  rw [clock_coarsening_loss]
  exact lt_add_of_pos_right _ (div_pos (Nat.cast_pos.mpr positive) (by norm_num))

theorem singleton_no_loss :
    error (historyPMF 0) (observe 0) (clockTask 0) (currentDecoder 0) = 0 ∧
      error (historyPMF 0) (nextObserve 0) (clockTask 0) (nextDecoder 0) = 0 := by
  rw [current_attains, next_attains]
  norm_num

end
end SourcePulseCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
