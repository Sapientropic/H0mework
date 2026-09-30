import H0mework.Fock.CopyGraph.GrowthTagged
import H0mework.Probability.Source.ConditionalCoarsening

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceHistoryGrowth
noncomputable section
universe u
variable {Observed : Type u}

theorem tagged_old_distribution (depth : Nat) (read : Nat → Observed) :
    ∃ supported : true ∈ ((historyPMF (depth + 1)).map (Prod.snd ∘ taggedRead depth read)).support,
      SourceConditionalHistory.conditional (historyPMF (depth + 1)) (Prod.snd ∘ taggedRead depth read) true supported =
        (historyPMF depth).map (includeActor (Nat.le_succ depth)) := by
  rw [tagged_prior]
  exact ⟨prior_supported (Nat.le_succ depth), prior_conditional_complete (Nat.le_succ depth)⟩

theorem forgetting_conditional (depth : Nat) (read : Nat → Observed) (atom : Observed)
    (supported : atom ∈ (SourceConditionalHistory.observed
      (SourceConditionalHistory.observed (historyPMF (depth + 1)) (taggedRead depth read)) Prod.fst).support) :
    ∃ originalSupported : atom ∈ ((historyPMF (depth + 1)).map (newRead depth read)).support,
      SourceConditionalHistory.Coarsening.mixture (historyPMF (depth + 1)) (taggedRead depth read) Prod.fst atom supported =
        SourceConditionalHistory.conditional (historyPMF (depth + 1)) (newRead depth read) atom originalSupported := by
  simpa only [tagged_forget] using SourceConditionalHistory.Coarsening.mixture_is_conditional
    (historyPMF (depth + 1)) (taggedRead depth read) Prod.fst atom supported

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
