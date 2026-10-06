import H0mework.Realization.Perfectification.Quantum.Forms.Graph

/-! The same graph projection generates a positive contractive resolvent.
No spectral bounds are supplied separately from the derivative graph. -/

set_option autoImplicit false

open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.Quantum.Forms.Graph

noncomputable section

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)

theorem projection_positive : (projection A closed).IsPositive := by
  let : CompleteSpace (graph A) := (graph_closed A closed).completeSpace_coe
  exact ContinuousLinearMap.IsPositive.of_isStarProjection (isStarProjection_starProjection (U := graph A))

theorem resolvent_positive : (resolvent A closed).IsPositive :=
  (projection_positive A closed).adjoint_conj lift

theorem resolvent_norm_le_one : ‖resolvent A closed‖ ≤ 1 := by
  let : CompleteSpace (graph A) := (graph_closed A closed).completeSpace_coe
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [resolvent_apply, one_mul]
  calc
    _ ≤ ‖projection A closed (lift x)‖ := WithLp.norm_fst_le H _
    _ ≤ ‖lift (F := F) x‖ := (graph A).norm_starProjection_apply_le _
    _ = ‖x‖ := by rw [lift_apply, WithLp.prod_norm_eq_of_L2]; simp

end
end SaturationMonoid.Quantum.Forms.Graph
