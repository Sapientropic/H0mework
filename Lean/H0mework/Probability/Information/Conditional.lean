import H0mework.Probability.Information.Variance

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreVariance

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open scoped Classical ENNReal
noncomputable section

variable {Observed : Type*} [DecidableEq Observed]

def fibre (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed) : Finset (Fin (bound + 1)) :=
  Finset.univ.filter (fun index => query index = value)

def outputs (bound : Nat) (query : Fin (bound + 1) → Observed) : Finset Observed :=
  Finset.univ.image query

theorem fibre_mem (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed)
    (index : Fin (bound + 1)) : index ∈ fibre bound query value ↔ query index = value := by
  simp [fibre]

theorem fibre_nonempty (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed)
    (present : value ∈ outputs bound query) : (fibre bound query value).Nonempty := by
  obtain ⟨index, _, same⟩ := Finset.mem_image.mp present
  exact ⟨index, (fibre_mem bound query value index).mpr same⟩

theorem positive_card (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed)
    (present : value ∈ outputs bound query) : 0 < ((fibre bound query value).card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr (fibre_nonempty bound query value present)

theorem fibre_card_sum (bound : Nat) (query : Fin (bound + 1) → Observed) :
    (∑ value ∈ outputs bound query, (fibre bound query value).card) = bound + 1 := by
  have original := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin (bound + 1)))) (t := outputs bound query) (g := query)
    (fun index _ => Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩) (fun _ => (1 : Nat))
  simpa only [fibre, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] using original

theorem source_weight (bound : Nat) (index : Fin (bound + 1)) :
    (historyPMF bound index).toReal = 1 / (bound + 1 : ℝ) := by
  rw [historyPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp [one_div]

theorem source_positive (bound : Nat) (index : Fin (bound + 1)) : historyPMF bound index ≠ 0 := by
  simp [historyPMF_apply]

theorem output_supported (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed)
    (present : value ∈ outputs bound query) : value ∈ ((historyPMF bound).map query).support := by
  obtain ⟨index, _, same⟩ := Finset.mem_image.mp present
  exact (PMF.mem_support_map_iff query (historyPMF bound) value).mpr ⟨index, source_positive bound index, same⟩

theorem supported_output (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF bound).map query).support) : value ∈ outputs bound query := by
  obtain ⟨index, _, same⟩ := (PMF.mem_support_map_iff query (historyPMF bound) value).mp supported
  exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, same⟩

theorem observed_weight (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed) :
    ((historyPMF bound).map query value).toReal = (fibre bound query value).card / (bound + 1 : ℝ) := by
  have raw : (historyPMF bound).map query value =
      ∑ index ∈ fibre bound query value, historyPMF bound index := by
    rw [PMF.map_apply, tsum_fintype, fibre, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro index _
    by_cases same : query index = value
    · simp only [if_pos same, if_pos same.symm]
    · simp only [if_neg same, if_neg (Ne.symm same)]
  rw [raw]
  simp only [historyPMF_apply, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_inv, div_eq_mul_inv]
  simp only [Nat.cast_add, Nat.cast_one]

theorem conditional_weight (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF bound).map query).support) (index : Fin (bound + 1)) :
    (SourceConditionalHistory.conditional (historyPMF bound) query value supported index).toReal =
      if index ∈ fibre bound query value then ((fibre bound query value).card : ℝ)⁻¹ else 0 := by
  have cardNonzero := (positive_card bound query value (supported_output bound query value supported)).ne'
  have countNonzero : (bound + 1 : ℝ) ≠ 0 := by positivity
  rw [SourceConditionalHistory.conditional_apply]
  by_cases same : query index = value
  · rw [if_pos same, if_pos ((fibre_mem bound query value index).mpr same),
      ENNReal.toReal_mul, ENNReal.toReal_inv, source_weight, observed_weight]
    field_simp
  · rw [if_neg same, if_neg (fun inside => same ((fibre_mem bound query value index).mp inside)),
      ENNReal.toReal_zero]

private theorem uniform_real_mean {A : Type*} [Fintype A] [DecidableEq A]
    (indices : Finset A) (task : A → ℝ) :
    (∑ index : A, (if index ∈ indices then (indices.card : ℝ)⁻¹ else 0) • (task index : ℂ)) =
      (((∑ index ∈ indices, task index) / indices.card : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.smul_re, Complex.ofReal_re, smul_eq_mul, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have selected : Finset.univ.filter (fun index => index ∈ indices) = indices := by ext index; simp
    rw [selected, ← Finset.mul_sum]
    ring
  · simp only [Complex.im_sum, Complex.smul_im, Complex.ofReal_im, smul_zero, Finset.sum_const_zero]

variable [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem optimalDecoder_fibre_mean (bound : Nat) (query : Fin (bound + 1) → Observed)
    (task : Fin (bound + 1) → ℝ) (value : Observed)
    (supported : value ∈ ((historyPMF bound).map query).support) :
    optimalDecoder (historyPMF bound) query (fun index => (task index : ℂ)) value =
      (((∑ index ∈ fibre bound query value, task index) / (fibre bound query value).card : ℝ) : ℂ) := by
  rw [optimal_is_conditional (historyPMF bound) query _ value supported, conditionalMean]
  simp_rw [conditional_weight]
  exact uniform_real_mean (fibre bound query value) task

end
end SourceUniformFibreVariance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
