import H0mework.Probability.Source.ConditionalNextImageEntropy
import H0mework.Probability.Information.Entropy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreInformation

open SourceUniformFibreVariance SourceGeneratedRuntimeHistoryProbability
open scoped Classical
noncomputable section
universe u v
variable {Observed : Type u} [DecidableEq Observed] {Next : Type v}
attribute [local instance] SourceConditionalNext.Image.valuesFintype
  SourceConditionalNext.Image.valuesMeasurable SourceConditionalNext.Image.valuesSingleton

local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

theorem source_entropy_average (bound : Nat) (query : Fin (bound + 1) → Observed)
    (positive : ∀ point, point ∈ (historyPMF bound).support) :
    (∑ point, (historyPMF bound point).toReal *
      entropy (SourceConditionalHistory.conditional (historyPMF bound) query (query point)
        (SourceWeightedRecovery.observed_supported (historyPMF bound) query point (positive point)))) =
      conditionalEntropy bound query := by
  rw [conditional_entropy_formula]
  simp_rw [fibre_entropy, source_weight]
  have grouped := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin (bound + 1)))) (t := outputs bound query) (g := query)
    (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (fun value => 1 / (bound + 1 : ℝ) * Real.log (fibre bound query value).card)
  rw [← grouped]
  apply Finset.sum_congr rfl
  intro value _
  simp only [fibre, Finset.sum_const, nsmul_eq_mul]
  ring

theorem image_conditional_entropy (bound : Nat) (query : Fin (bound + 1) → Observed)
    (nextRead : Fin (bound + 1) → Next) (injective : Function.Injective nextRead)
    (positive : ∀ point, point ∈ (historyPMF bound).support) :
    SourceConditionalNext.conditionalEntropy (historyPMF bound) query
      (SourceConditionalNext.Image.actual nextRead) positive = conditionalEntropy bound query := by
  unfold SourceConditionalNext.conditionalEntropy SourceConditionalNext.conditionalNext
  simp only [SourceConditionalNext.Image.entropy_injective _ nextRead injective]
  exact source_entropy_average bound query positive

end
end SourceUniformFibreInformation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
