import H0mework.Probability.Source.ConditionalAction

/-! Coarsened observations retain the full source-generated mixture of the old conditional fibres. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalHistory.Coarsening

open scoped Classical
noncomputable section
universe u v w
variable {Source : Type u} {Fine : Type v} {Coarse : Type w}
variable (source : PMF Source) (read : Source → Fine) (forget : Fine → Coarse)
variable (value : Coarse) (supported : value ∈ (observed (observed source read) forget).support)

theorem fine_supported (fine : Fine)
    (member : fine ∈ (conditional (observed source read) forget value supported).support) :
    fine ∈ (observed source read).support :=
  (show forget fine = value ∧ fine ∈ (observed source read).support by
    simpa only [conditional_support, Set.mem_inter_iff, Set.mem_ofPred_eq] using member).2

def mixture : PMF Source :=
  (conditional (observed source read) forget value supported).bindOnSupport
    (fun fine member => conditional source read fine (fine_supported source read forget value supported fine member))

theorem mixture_is_conditional :
    ∃ coarseSupported : value ∈ (observed source (forget ∘ read)).support,
      mixture source read forget value supported = conditional source (forget ∘ read) value coarseSupported := by
  have composite : observed (observed source read) forget = observed source (forget ∘ read) := PMF.map_comp _ _ _
  have coarseSupported : value ∈ (observed source (forget ∘ read)).support := composite ▸ supported
  refine ⟨coarseSupported, ?_⟩
  apply PMF.ext
  intro point
  rw [mixture, PMF.bindOnSupport_apply, tsum_eq_single (read point)]
  · split_ifs with zero
    · rw [mul_zero, conditional_apply]
      change (0 : ENNReal) = if forget (read point) = value then _ else _
      by_cases selected : forget (read point) = value
      · have absent : source point = 0 := by
          apply (source.apply_eq_zero_iff point).mpr
          intro inSource
          have retained : read point ∈ (conditional (observed source read) forget value supported).support := by
            rw [conditional_support]
            exact ⟨selected, (PMF.mem_support_map_iff _ _ _).mpr ⟨point, inSource, rfl⟩⟩
          exact retained zero
        rw [if_pos selected, absent, zero_mul]
      · exact (if_neg selected).symm
    · have selected : forget (read point) = value ∧ read point ∈ (observed source read).support := by
        simpa only [conditional_support, Set.mem_inter_iff, Set.mem_ofPred_eq] using
          (show read point ∈ (conditional (observed source read) forget value supported).support from zero)
      rw [conditional_apply (observed source read) forget value supported (read point), if_pos selected.1,
        conditional_apply source (forget ∘ read) value coarseSupported point]
      change _ = if forget (read point) = value then _ else _
      rw [if_pos selected.1, ← composite]
      calc
        _ = (observed (observed source read) forget value)⁻¹ *
          ((observed source read (read point)) *
            conditional source read (read point) (fine_supported source read forget value supported _ zero) point) := by ac_rfl
        _ = _ := by rw [weighted_conditional, if_pos rfl]; ac_rfl
  · intro other different
    split_ifs with zero
    · exact mul_zero _
    · rw [conditional_apply source read other
        (fine_supported source read forget value supported other zero) point,
        if_neg different.symm, mul_zero]

end
end SourceConditionalHistory.Coarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
