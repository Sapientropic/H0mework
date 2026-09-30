import H0mework.Fock.HistoryConditional.PosteriorSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorReadback

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
universe u v

theorem recovered_support (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) (actor : Actors runtime) :
    readWeight runtime (SourceConditionalVector.estimate runtime query value supported) actor ≠ 0 ↔ query actor = value := by
  rw [weight_estimate]
  change actor ∈ (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported).support ↔ _
  rw [SourceConditionalHistory.conditional_support]
  change (query actor = value ∧ actor ∈ (historyPMF (inventoryBound runtime)).support) ↔ query actor = value
  exact and_iff_left (SourceUniformFibreVariance.source_positive _ actor)

theorem estimates_equal_iff (runtime : LivingRuntimeState process) {Left : Type u} {Right : Type v}
    (left : Actors runtime → Left) (right : Actors runtime → Right) (leftValue : Left) (rightValue : Right)
    (leftSupported : leftValue ∈ ((historyPMF (inventoryBound runtime)).map left).support)
    (rightSupported : rightValue ∈ ((historyPMF (inventoryBound runtime)).map right).support) :
    SourceConditionalVector.estimate runtime left leftValue leftSupported = SourceConditionalVector.estimate runtime right rightValue rightSupported ↔
      SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) left leftValue leftSupported =
        SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) right rightValue rightSupported := by
  constructor
  · intro same
    apply PMF.ext
    intro actor
    exact (weight_estimate runtime left leftValue leftSupported actor).symm.trans
      ((congrArg (fun model => readWeight runtime model actor) same).trans (weight_estimate runtime right rightValue rightSupported actor))
  · intro same
    simp only [SourceConditionalVector.estimate, same]

theorem source_weight (runtime : LivingRuntimeState process) (index actor : Actors runtime) :
    readWeight runtime (SourceConditionalModel.nextRead runtime index) actor = PMF.pure index actor := by
  rw [readWeight, ← SourceConditionalInventory.values_original, SourceGInformationCost.coordinate_actual, PMF.pure_apply]
  by_cases same : actor = index
  · subst actor
    simp only [ite_true, Complex.one_re, ENNReal.ofReal_one]
  · simp only [if_neg same, if_neg (Ne.symm same), Complex.zero_re, ENNReal.ofReal_zero]

theorem estimate_eq_source_iff (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) (index : Actors runtime) :
    SourceConditionalVector.estimate runtime query value supported = SourceConditionalModel.nextRead runtime index ↔
      SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported = PMF.pure index := by
  constructor
  · intro same
    apply PMF.ext
    intro actor
    exact (weight_estimate runtime query value supported actor).symm.trans
      ((congrArg (fun model => readWeight runtime model actor) same).trans (source_weight runtime index actor))
  · intro pure
    rw [SourceConditionalVector.estimate, pure, Finset.sum_eq_single index]
    · simp only [PMF.pure_apply, ite_true, ENNReal.toReal_one, Complex.ofReal_one, one_smul]
    · intro other _ different
      rw [PMF.pure_apply, if_neg different]
      simp only [ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul]
    · intro absent
      exact (absent (Finset.mem_univ _)).elim

theorem mixture_not_actual (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support)
    (left right : Actors runtime) (leftSeen : query left = value) (rightSeen : query right = value) (different : left ≠ right) :
    SourceConditionalVector.estimate runtime query value supported ∉ Set.range (SourceConditionalModel.nextRead runtime) := by
  rintro ⟨index, same⟩
  have identifies (actor : Actors runtime) (seen : query actor = value) : actor = index := by
    have nonzero := (recovered_support runtime query value supported actor).mpr seen
    rw [← same, source_weight, PMF.pure_apply] at nonzero
    by_contra distinct
    exact nonzero (if_neg distinct)
  exact different ((identifies left leftSeen).trans (identifies right rightSeen).symm)

end
end SourcePosteriorReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
