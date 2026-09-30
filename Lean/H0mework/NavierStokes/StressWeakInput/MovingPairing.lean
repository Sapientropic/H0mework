import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
open Filter
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWeakMovingPairing

variable {I E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The changing test is controlled in the original norm and along the same
filter as the weak input. Completeness is not needed. -/
theorem weak_moving_test (f : Filter I) (family : I → E) (target : E) (cap : ℝ)
    (bounded : ∀ i, ‖family i‖ ≤ cap)
    (weak : ∀ test : E, Tendsto (fun i => inner ℝ (family i) test) f (𝓝 (inner ℝ target test)))
    {tests : I → E} {test : E} (strong : Tendsto tests f (𝓝 test)) :
    Tendsto (fun i => inner ℝ (family i) (tests i)) f (𝓝 (inner ℝ target test)) := by
  have testError : Tendsto (fun i => ‖tests i - test‖) f (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp strong
  have error : Tendsto (fun i => inner ℝ (family i) (tests i - test)) f (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun i => norm_nonneg _) _ (by simpa using testError.const_mul cap)
    intro i
    exact (norm_inner_le_norm (family i) (tests i - test)).trans
      (mul_le_mul_of_nonneg_right (bounded i) (norm_nonneg _))
  simpa only [inner_sub_right, sub_add_cancel, zero_add] using error.add (weak test)

/-- The canonical adjoint supplies the moving test for the original output
pairing. Hilbert completeness here is required by Mathlib's adjoint itself. -/
theorem adjoint_output_test [CompleteSpace E] [CompleteSpace F]
    (f : Filter I) (family : I → E) (target : E) (cap : ℝ)
    (bounded : ∀ i, ‖family i‖ ≤ cap)
    (weak : ∀ test : E, Tendsto (fun i => inner ℝ (family i) test) f (𝓝 (inner ℝ target test)))
    (operators : I → E →L[ℝ] F) (operator : E →L[ℝ] F) (test : F)
    (adjointStrong : Tendsto (fun i => (operators i).adjoint test) f (𝓝 (operator.adjoint test))) :
    Tendsto (fun i => inner ℝ (operators i (family i)) test) f (𝓝 (inner ℝ (operator target) test)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_right] using
    weak_moving_test f family target cap bounded weak adjointStrong

end SaturationMonoid.NavierStokes.NativeWeakMovingPairing
