import H0mework.Fock.HistoryConditional.NativeMergeCount
import H0mework.Probability.Source.ConditionalCoarsening

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeMerge

open SourceConditionalNativeObservers (generate)
open SourceUniformFibreVariance (outputs)
open SourceGeneratedRuntimeHistoryProbability (historyPMF)
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem row_generated (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) (value : Coarse)
    (actor : Fin (bound + 1)) :
    (merge read forget bound (generate read bound) value).2 actor = (generate (forget ∘ read) bound value).2 actor := by
  dsimp only [merge, inventoryMerge]
  rw [show inventoryCount (outputs bound (fun actor => read actor.val)) forget bound (generate read bound) value =
    count read forget bound (generate read bound) value from rfl]
  conv_rhs => rw [SourceConditionalNativePosterior.weight_fibre]
  rw [Finset.sum_eq_single (read actor.val)]
  · simp only [SourceConditionalNativePosterior.weight_fibre, ite_true, count_generated, Function.comp_apply]
    have fineNonzero : ((generate read bound (read actor.val)).1 : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (SourceConditionalNativePosterior.count_positive read bound _ actor rfl).ne'
    by_cases selected : forget (read actor.val) = value
    · simp only [if_pos selected]
      have coarseNonzero : ((generate (forget ∘ read) bound value).1 : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (SourceConditionalNativePosterior.count_positive (forget ∘ read) bound value actor selected).ne'
      field_simp
    · simp only [if_neg selected]
  · intro other _ different
    simp only [SourceConditionalNativePosterior.weight_fibre, if_neg (Ne.symm different), mul_zero, ite_self]
  · intro absent
    exact (absent (Finset.mem_image.mpr ⟨actor, Finset.mem_univ _, rfl⟩)).elim

theorem merged_generated (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) :
    merge read forget bound (generate read bound) = generate (forget ∘ read) bound := by
  funext value
  apply Prod.ext
  · exact count_generated read forget bound value
  · exact funext (row_generated read forget bound value)

theorem merge_next (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) :
    merge read forget (bound + 1) (SourceConditionalNativeObservers.advance read bound (generate read bound)) =
      SourceConditionalNativeObservers.advance (forget ∘ read) bound (merge read forget bound (generate read bound)) := by
  rw [← SourceConditionalNativeObservers.generated_next, merged_generated, merged_generated,
    SourceConditionalNativeObservers.generated_next]

theorem mixture_weight (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) (value : Coarse)
    (supported : value ∈ (SourceConditionalHistory.observed
      (SourceConditionalHistory.observed (historyPMF bound) (fun actor : Fin (bound + 1) => read actor.val)) forget).support)
    (actor : Fin (bound + 1)) :
    ((merge read forget bound (generate read bound) value).2 actor : ℝ) =
      (SourceConditionalHistory.Coarsening.mixture (historyPMF bound) (fun index => read index.val)
        forget value supported actor).toReal := by
  obtain ⟨coarseSupported, paid⟩ := SourceConditionalHistory.Coarsening.mixture_is_conditional
    (historyPMF bound) (fun index : Fin (bound + 1) => read index.val) forget value supported
  rw [paid, row_generated]
  exact SourceConditionalNativePosterior.posterior (forget ∘ read) bound value coarseSupported actor

end SourceConditionalNativeMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
