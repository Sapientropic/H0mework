import H0mework.Probability.Source.HistoryGrowth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open scoped Classical
noncomputable section

variable {old fresh : Nat} (retained : old ≤ fresh)

def priorTag (old fresh : Nat) (index : Fin (fresh + 1)) : Bool := decide (index.val < old + 1)

include retained

theorem prior_fibre :
    fibre fresh (priorTag old fresh) true = Finset.univ.image (includeActor retained) := by
  ext index
  rw [fibre_mem]
  constructor
  · intro prior
    have inside : index.val < old + 1 := by simpa [priorTag] using prior
    exact Finset.mem_image.mpr ⟨⟨index.val, inside⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro present
    obtain ⟨before, _, rfl⟩ := Finset.mem_image.mp present
    change decide (before.val < old + 1) = true
    simpa only [decide_eq_true_eq] using before.isLt

theorem prior_card : (fibre fresh (priorTag old fresh) true).card = old + 1 := by
  rw [prior_fibre retained, Finset.card_image_of_injective _ (includeActor retained).injective]
  simp

theorem prior_supported : true ∈ ((historyPMF fresh).map (priorTag old fresh)).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨includeActor retained 0, source_positive fresh _, ?_⟩
  change decide (0 < old + 1) = true
  simp

theorem prior_mass : ((historyPMF fresh).map (priorTag old fresh) true).toReal = fraction old fresh := by
  rw [observed_weight, prior_card retained]
  simp [fraction]

def priorConditional : PMF (Fin (fresh + 1)) :=
  SourceConditionalHistory.conditional (historyPMF fresh) (priorTag old fresh) true (prior_supported retained)

theorem prior_conditional_complete :
    priorConditional retained = (historyPMF old).map (includeActor retained) := by
  apply PMF.ext
  intro index
  apply (ENNReal.toReal_eq_toReal_iff' ((priorConditional retained).apply_ne_top index)
    (((historyPMF old).map (includeActor retained)).apply_ne_top index)).mp
  change (SourceConditionalHistory.conditional (historyPMF fresh) (priorTag old fresh) true
    (prior_supported retained) index).toReal = _
  rw [conditional_weight, prior_card retained]
  by_cases inside : index.val < old + 1
  · let before : Fin (old + 1) := ⟨index.val, inside⟩
    have same : includeActor retained before = index := Fin.ext rfl
    have beforeWeight : (historyPMF old).map (includeActor retained) (includeActor retained before) =
        historyPMF old before := by
      rw [PMF.map_apply, tsum_fintype]
      simp [(includeActor retained).injective.eq_iff]
    have present : includeActor retained before ∈ fibre fresh (priorTag old fresh) true := by
      rw [fibre_mem]
      change decide (before.val < old + 1) = true
      simpa only [decide_eq_true_eq] using before.isLt
    rw [← same, beforeWeight, source_weight, if_pos present]
    simp [one_div]
  · have absent : index ∉ fibre fresh (priorTag old fresh) true := by
      simpa [fibre_mem, priorTag] using inside
    have notImage : ∀ before : Fin (old + 1), index ≠ includeActor retained before := by
      intro before same
      have values := congrArg Fin.val same
      have bounded := before.isLt
      apply inside
      change index.val = before.val at values
      omega
    rw [if_neg absent, PMF.map_apply, tsum_fintype]
    simp [notImage]

end
end SourceHistoryGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
