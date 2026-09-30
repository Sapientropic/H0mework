import H0mework.Fock.ClockCoarsening.Source

/-! The source-generated pulse collapse consumes the complete old conditional mixture. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePulseCoarsening

open SourceGeneratedRuntimeHistoryProbability SourceConditionalHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem observed_source_square (bound : Nat) :
    observed (observed (historyPMF bound) (observe bound)) forget =
      observed (historyPMF bound) (nextObserve bound) := by
  rw [observed, PMF.map_comp]
  congr 1
  funext point
  exact (next_observe_source bound point).symm

theorem coarse_supported (bound : Nat) :
    (0 : ZMod 2) ∈ (observed (observed (historyPMF bound) (observe bound)) forget).support := by
  rw [observed_source_square]
  exact next_supported bound

def generatedMixture (bound : Nat) : PMF (Fin (bound + 1)) :=
  Coarsening.mixture (historyPMF bound) (observe bound) forget 0 (coarse_supported bound)

theorem generatedMixture_is_full (bound : Nat) : generatedMixture bound = historyPMF bound := by
  obtain ⟨supported, equality⟩ := Coarsening.mixture_is_conditional
    (historyPMF bound) (observe bound) forget 0 (coarse_supported bound)
  have square : forget ∘ observe bound = nextObserve bound := funext fun point => (next_observe_source bound point).symm
  change generatedMixture bound = _ at equality
  simp only [square] at equality
  exact equality.trans (next_conditional_full bound)

theorem mixture_actual_next (bound : Nat) :
    (generatedMixture bound).map (fun point => ((history runtimeSeed bound).stageAt point).next) =
      (historyPMF bound).map (fun point => (runtimeSeed.advance point.val).tick.next) := by
  rw [generatedMixture_is_full]
  rfl

end
end SourcePulseCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
