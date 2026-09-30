import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false
open Filter
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeStrongOperatorLimit

noncomputable section

variable {I E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (f : Filter I) [f.NeBot] (family : I → E →L[ℝ] F)
  (contractive : ∀ i, ‖family i‖ ≤ 1)
  (pointwise : ∀ x, ∃ y, Tendsto (fun i => family i x) f (𝓝 y))

private def value (x : E) : F := Classical.choose (pointwise x)

omit [f.NeBot] in
private theorem value_tendsto (x : E) :
    Tendsto (fun i => family i x) f (𝓝 (value f family pointwise x)) :=
  Classical.choose_spec (pointwise x)

include contractive in
private theorem value_bound (x : E) : ‖value f family pointwise x‖ ≤ ‖x‖ := by
  apply le_of_tendsto (value_tendsto f family pointwise x |>.norm)
  exact Eventually.of_forall fun i => by
    simpa using (family i).le_of_opNorm_le (contractive i) x

/-- The same filter fixes one whole linear operator; the pointwise witnesses
are used only to select their uniquely determined values. -/
def limitOperator : E →L[ℝ] F :=
  (linearMapOfTendsto (value f family pointwise) (fun i => (family i).toLinearMap)
    (tendsto_pi_nhds.mpr (value_tendsto f family pointwise))).mkContinuous 1
      (fun x => by simpa using value_bound f family contractive pointwise x)

theorem limitOperator_tendsto (x : E) :
    Tendsto (fun i => family i x) f (𝓝 (limitOperator f family contractive pointwise x)) :=
  value_tendsto f family pointwise x

theorem limitOperator_bound (x : E) :
    ‖limitOperator f family contractive pointwise x‖ ≤ ‖x‖ :=
  value_bound f family contractive pointwise x

theorem limitOperator_norm : ‖limitOperator f family contractive pointwise‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using limitOperator_bound f family contractive pointwise x

theorem limitOperator_unique (candidate : E →L[ℝ] F)
    (converges : ∀ x, Tendsto (fun i => family i x) f (𝓝 (candidate x))) :
    candidate = limitOperator f family contractive pointwise := by
  ext x
  exact tendsto_nhds_unique (converges x) (limitOperator_tendsto f family contractive pointwise x)

include contractive pointwise in
theorem existsUnique_limitOperator :
    ∃! output : E →L[ℝ] F, ‖output‖ ≤ 1 ∧
      ∀ x, Tendsto (fun i => family i x) f (𝓝 (output x)) :=
  ⟨limitOperator f family contractive pointwise,
    ⟨limitOperator_norm f family contractive pointwise,
      limitOperator_tendsto f family contractive pointwise⟩,
    fun output h => limitOperator_unique f family contractive pointwise output h.2⟩

/-- Uniform contraction controls the moving-input error before the fixed-input
strong limit is consumed. No operator-norm convergence is required. -/
theorem moving_load {load : I → E} {target : E} (moving : Tendsto load f (𝓝 target)) :
    Tendsto (fun i => family i (load i)) f
      (𝓝 (limitOperator f family contractive pointwise target)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have loadError : Tendsto (fun i => ‖load i - target‖) f (𝓝 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mp moving
  have fixedError : Tendsto
      (fun i => ‖family i target - limitOperator f family contractive pointwise target‖) f (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (limitOperator_tendsto f family contractive pointwise target)
  apply squeeze_zero (fun i => norm_nonneg _) _ (by simpa using loadError.add fixedError)
  intro i
  calc
    _ = ‖family i (load i - target) +
        (family i target - limitOperator f family contractive pointwise target)‖ := by
      rw [map_sub]
      congr 1
      abel
    _ ≤ ‖family i (load i - target)‖ +
        ‖family i target - limitOperator f family contractive pointwise target‖ := norm_add_le _ _
    _ ≤ ‖load i - target‖ +
        ‖family i target - limitOperator f family contractive pointwise target‖ := by
      apply add_le_add _ le_rfl
      simpa using (family i).le_of_opNorm_le (contractive i) (load i - target)

variable (outer : I → F →L[ℝ] G) (outer_contractive : ∀ i, ‖outer i‖ ≤ 1)
  (outer_pointwise : ∀ y, ∃ z, Tendsto (fun i => outer i y) f (𝓝 z))

theorem composition_tendsto (x : E) :
    Tendsto (fun i => (outer i).comp (family i) x) f
      (𝓝 ((limitOperator f outer outer_contractive outer_pointwise).comp
        (limitOperator f family contractive pointwise) x)) :=
  moving_load f outer outer_contractive outer_pointwise
    (limitOperator_tendsto f family contractive pointwise x)

include contractive outer_contractive in
theorem composition_contractive (i : I) : ‖(outer i).comp (family i)‖ ≤ 1 := by
  apply ((outer i).opNorm_comp_le (family i)).trans
  exact (mul_le_mul (outer_contractive i) (contractive i) (norm_nonneg _) zero_le_one).trans (by simp)

include contractive pointwise outer_contractive outer_pointwise in
theorem composition_pointwise (x : E) : ∃ z, Tendsto (fun i => (outer i).comp (family i) x) f (𝓝 z) :=
  ⟨_, composition_tendsto f family contractive pointwise outer outer_contractive outer_pointwise x⟩

theorem composition_limit :
    limitOperator f (fun i => (outer i).comp (family i))
      (composition_contractive family contractive outer outer_contractive)
      (composition_pointwise f family contractive pointwise outer outer_contractive outer_pointwise) =
    (limitOperator f outer outer_contractive outer_pointwise).comp
      (limitOperator f family contractive pointwise) := by
  symm
  apply limitOperator_unique
  exact composition_tendsto f family contractive pointwise outer outer_contractive outer_pointwise

end
end SaturationMonoid.NavierStokes.NativeStrongOperatorLimit
