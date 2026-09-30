import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Reachable observations generate complete conditional source distributions and exact recombination. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalHistory

open scoped Classical

noncomputable section

universe u v w

variable {Source : Type u} {Observed : Type v} {Target : Type w}
variable (source : PMF Source) (read : Source → Observed)

abbrev observed : PMF Observed := source.map read

def conditional (value : Observed) (supported : value ∈ (observed source read).support) : PMF Source :=
  source.filter {point | read point = value} (by
    obtain ⟨point, member, equality⟩ := (PMF.mem_support_map_iff read source value).mp supported
    exact ⟨point, equality, member⟩)

theorem conditional_support (value : Observed) (supported : value ∈ (observed source read).support) :
    (conditional source read value supported).support = {point | read point = value} ∩ source.support :=
  PMF.support_filter _

theorem conditional_apply (value : Observed) (supported : value ∈ (observed source read).support)
    (point : Source) :
    conditional source read value supported point =
      if read point = value then source point * (observed source read value)⁻¹ else 0 := by
  have normalizer : (∑' point, ({point | read point = value}.indicator source) point) =
      observed source read value := by
    simp only [observed, PMF.map_apply, Set.indicator_apply, Set.mem_ofPred_eq]
    apply tsum_congr
    intro point
    by_cases same : read point = value
    · simp [same]
    · simp [same, Ne.symm same]
  rw [conditional, PMF.filter_apply, normalizer]
  by_cases same : read point = value <;> simp [same]

theorem weighted_conditional (value : Observed) (supported : value ∈ (observed source read).support)
    (point : Source) :
    observed source read value * conditional source read value supported point =
      if read point = value then source point else 0 := by
  rw [conditional_apply]
  split_ifs with same
  · calc
      _ = source point * (observed source read value * (observed source read value)⁻¹) := by ac_rfl
      _ = source point := by
        rw [ENNReal.mul_inv_cancel supported ((observed source read).apply_ne_top value), mul_one]
  · exact mul_zero _

theorem recombine :
    (observed source read).bindOnSupport (conditional source read) = source := by
  apply PMF.ext
  intro point
  rw [PMF.bindOnSupport_apply, tsum_eq_single (read point)]
  · split_ifs with zero
    · have vanished : source point = 0 := by
        apply (source.apply_eq_zero_iff point).mpr
        intro member
        exact ((PMF.mem_support_map_iff read source (read point)).mpr ⟨point, member, rfl⟩) zero
      simp only [mul_zero, vanished]
    · simpa only [ite_true] using weighted_conditional source read (read point) zero point
  · intro other distinct
    split_ifs with zero
    · exact mul_zero _
    · exact (weighted_conditional source read other zero point).trans (if_neg (Ne.symm distinct))

theorem recombine_map (targetRead : Source → Target) :
    (observed source read).bindOnSupport
        (fun value supported => (conditional source read value supported).map targetRead) = source.map targetRead := by
  have associative := PMF.bindOnSupport_bindOnSupport (observed source read) (conditional source read)
    (fun point _ => PMF.pure (targetRead point))
  simp only [PMF.bindOnSupport_eq_bind] at associative
  change ((observed source read).bindOnSupport (conditional source read)).map targetRead = _ at associative
  rw [recombine] at associative
  exact associative.symm

end
end SourceConditionalHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
