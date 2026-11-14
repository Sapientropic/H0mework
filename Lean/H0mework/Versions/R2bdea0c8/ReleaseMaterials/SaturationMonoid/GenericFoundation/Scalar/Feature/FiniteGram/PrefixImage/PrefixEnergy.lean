import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.PrefixImage

open scoped InnerProductSpace Topology
open Filter Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The total cost is computed from the actual finite effects of the admitted data. -/
def totalEnergy (source : Nat → H) (data : Admitted source) : ℝ :=
  sSup (range (energy source data.val))

def remainingEnergy (source : Nat → H) (data : Admitted source) (n : Nat) : ℝ :=
  totalEnergy source data - energy source data.val n

private theorem realized_projection (source : Nat → H) (data : Admitted source) (n : Nat) :
    approximate source data.val n =
      (Projection.sourceSpan (fun i : Fin n => source i.val)).starProjection (realize source data) :=
  (congrArg (fun stream => approximate source stream n) (read_realized source data).symm).trans
    (PrefixReadback.inverse_actual_rhs (fun i : Fin n => source i.val) (realize source data))

theorem total_energy (source : Nat → H) (data : Admitted source) :
    totalEnergy source data = ‖realize source data‖^2 := by
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨n,rfl⟩
    change ‖approximate source data.val n‖^2 ≤ _
    rw [realized_projection]
    exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2
  · have recovered : Tendsto (approximate source data.val) atTop (𝓝 (realize source data)) :=
      (cauchy_from_budget source data).tendsto_limUnder
    have cost : Tendsto (energy source data.val) atTop (𝓝 (‖realize source data‖^2)) :=
      recovered.norm.pow 2
    exact le_of_tendsto' cost (fun n => le_csSup data.property.2 ⟨n,rfl⟩)

/-- The full source error is exactly the energy missing from the actual prefix. -/
theorem error_squared (source : Nat → H) (data : Admitted source) (n : Nat) :
    ‖realize source data - approximate source data.val n‖^2 = remainingEnergy source data n := by
  let S := Projection.sourceSpan (fun i : Fin n => source i.val)
  let current := realize source data
  have projection : approximate source data.val n = S.starProjection current :=
    realized_projection source data n
  have pythag := S.norm_sq_eq_add_norm_sq_starProjection current
  rw [Submodule.starProjection_orthogonal_val,← projection] at pythag
  rw [remainingEnergy,total_energy]
  change ‖current - approximate source data.val n‖^2 =
    ‖current‖^2 - ‖approximate source data.val n‖^2
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans pythag.symm)

omit [CompleteSpace H] in
private theorem small_remainder (source : Nat → H) (data : Admitted source) (ε : ℝ) (positive : 0 < ε) :
    ∃ n, remainingEnergy source data n < ε^2 := by
  have tolerance : totalEnergy source data - ε^2 < sSup (range (energy source data.val)) :=
    sub_lt_self _ (pow_pos positive 2)
  obtain ⟨_,⟨n,rfl⟩,inside⟩ :=
    exists_lt_of_lt_csSup (range_nonempty (energy source data.val)) tolerance
  exact ⟨n,by unfold remainingEnergy; linarith only [inside]⟩

/-- The first sufficient prefix is selected by the actual retained energy gap. -/
def firstWithin (source : Nat → H) (data : Admitted source) (ε : ℝ) (positive : 0 < ε) : Nat :=
  open Classical in Nat.find (small_remainder source data ε positive)

theorem first_within (source : Nat → H) (data : Admitted source) (ε : ℝ) (positive : 0 < ε) :
    let n := firstWithin source data ε positive
    ‖realize source data - approximate source data.val n‖ < ε ∧
      ∀ m < n, ε ≤ ‖realize source data - approximate source data.val m‖ := by
  classical
  let existsSmall := small_remainder source data ε positive
  let n := firstWithin source data ε positive
  have found : remainingEnergy source data n < ε^2 := Nat.find_spec existsSmall
  refine ⟨(sq_lt_sq₀ (norm_nonneg _) positive.le).mp
    ((error_squared source data n).trans_lt found),?_⟩
  intro m earlier
  have large : ε^2 ≤ remainingEnergy source data m := le_of_not_gt (Nat.find_min existsSmall earlier)
  exact (sq_le_sq₀ positive.le (norm_nonneg _)).mp
    (large.trans_eq (error_squared source data m).symm)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Every actual continuous output can be paid directly by a finite current prefix. -/
theorem output_bound (source : Nat → H) (data : Admitted source) (n : Nat)
    (output : H →L[ℂ] V) :
    ‖output (realize source data) - output (approximate source data.val n)‖ ≤
      ‖output‖ * Real.sqrt (remainingEnergy source data n) := by
  rw [← map_sub,← error_squared,Real.sqrt_sq (norm_nonneg _)]
  exact output.le_opNorm _

end SourceGeneratedFiniteGram.PrefixImage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
