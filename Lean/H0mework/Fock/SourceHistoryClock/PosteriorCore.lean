import H0mework.Fock.SourceHistoryClock.RecoveryDecoder
import H0mework.Probability.Recovery.Conditional

/-! The existing clock recovery makes its complete source posterior an exact original-actor fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Clock

open SourceGeneratedRuntimeHistoryProbability

noncomputable section

theorem observe_injective (bound depth : Nat) : Function.Injective (observe bound depth) := by
  intro left right same
  have readback := (recovers_actor bound depth left).symm.trans
    ((congrArg (decode depth) same).trans (recovers_actor bound depth right))
  rw [task_source, task_source] at readback
  exact Fin.ext (Nat.cast_injective readback)

theorem observation_supported (bound depth : Nat) (index : Fin (bound + 1)) :
    observe bound depth index ∈ (observed (historyPMF bound) (observe bound depth)).support :=
  observed_supported (historyPMF bound) (observe bound depth) index (by simp [historyPMF])

def posterior (bound depth : Nat) (index : Fin (bound + 1)) : PMF (Fin (bound + 1)) :=
  SourceConditionalHistory.conditional (historyPMF bound) (observe bound depth) (observe bound depth index)
    (observation_supported bound depth index)

theorem posterior_support (bound depth : Nat) (index : Fin (bound + 1)) :
    (posterior bound depth index).support = {index} := by
  rw [posterior, SourceConditionalHistory.conditional_support]
  ext candidate
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro member
    exact observe_injective bound depth member.1
  · rintro rfl
    exact ⟨rfl, by simp [historyPMF]⟩

theorem observed_weight (bound depth : Nat) (index : Fin (bound + 1)) :
    observed (historyPMF bound) (observe bound depth) (observe bound depth index) = historyPMF bound index := by
  rw [observed, PMF.map_apply]
  rw [tsum_eq_single index]
  · exact if_pos rfl
  · intro candidate different
    exact if_neg (fun same => different (observe_injective bound depth same).symm)

theorem posterior_is_original (bound depth : Nat) (index : Fin (bound + 1)) :
    posterior bound depth index = PMF.pure index := by
  apply PMF.ext
  intro candidate
  rw [posterior, SourceConditionalHistory.conditional_apply, observed_weight, PMF.pure_apply]
  by_cases same : candidate = index
  · subst candidate
    rw [if_pos rfl, if_pos rfl]
    exact ENNReal.mul_inv_cancel (by simp [historyPMF]) ((historyPMF bound).apply_ne_top index)
  · rw [if_neg (fun equal => same (observe_injective bound depth equal)), if_neg same]

end
end SourceWeightedRecovery.Runtime.Actor.History.Clock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
