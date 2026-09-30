import H0mework.Versions.X.Fock.SourceHistoryClock.PosteriorCore
import H0mework.Probability.Recovery.Error

/-! The existing conditional optimum recovers every task on the same actual actor inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Clock

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem posterior_readback {Target : Type*} (bound depth : Nat) (index : Fin (bound + 1))
    (read : Fin (bound + 1) → Target) :
    (posterior bound depth index).map read = PMF.pure (read index) := by
  rw [posterior_is_original, PMF.pure_map]

theorem optimum_recovers (bound depth : Nat) (signal : Fin (bound + 1) → ℂ) (index : Fin (bound + 1)) :
    optimalDecoder (historyPMF bound) (observe bound depth) signal (observe bound depth index) = signal index := by
  have conditional := optimal_is_conditional (historyPMF bound) (observe bound depth) signal
    (observe bound depth index) (observation_supported bound depth index)
  change optimalDecoder (historyPMF bound) (observe bound depth) signal (observe bound depth index) =
    ∑ candidate : Fin (bound + 1), (posterior bound depth index candidate).toReal • signal candidate at conditional
  apply conditional.trans
  rw [posterior_is_original, Finset.sum_eq_single index]
  · simp
  · intro candidate _ different
    rw [PMF.pure_apply, if_neg different]
    simp
  · intro missing
    exact (missing (Finset.mem_univ index)).elim

theorem optimum_cost_zero (bound depth : Nat) (signal : Fin (bound + 1) → ℂ) :
    error (historyPMF bound) (observe bound depth) signal (optimalDecoder (historyPMF bound) (observe bound depth) signal) = 0 := by
  simp only [error, optimum_recovers, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

theorem source_residual_zero (bound depth : Nat) (signal : Fin (bound + 1) → ℂ) :
    residual (historyPMF bound) (observe bound depth) (taskValue (historyPMF bound) signal) = 0 := by
  have zero := (optimal_attains (historyPMF bound) (observe bound depth) signal).symm.trans
    (optimum_cost_zero bound depth signal)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp zero)

theorem posterior_same_material (bound depth : Nat) (index candidate : Fin (bound + 1))
    (supported : candidate ∈ (posterior bound depth index).support) :
    HEq ((history runtimeSeed bound).stageAt candidate) ((history runtimeSeed bound).stageAt index) := by
  rw [posterior_support] at supported
  have same : candidate = index := supported
  subst candidate
  rfl

end
end SourceWeightedRecovery.Runtime.Actor.History.Clock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
