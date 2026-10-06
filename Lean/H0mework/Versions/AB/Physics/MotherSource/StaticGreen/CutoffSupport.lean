import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.CutoffFamily

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Metric Filter
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel
open scoped ContDiff Topology
noncomputable section

theorem cutoff_first_zero_inside (radius : ℝ) (positive : 0 < radius) (point : Point)
    (inside : ‖point‖ < radius) (index : Fin 3) : spatialFirst (cutoff radius) index point = 0 := by
  have same : cutoff radius =ᶠ[𝓝 point] (fun _ => 1) := by
    filter_upwards [isOpen_ball.mem_nhds (show point ∈ ball 0 radius by simpa using inside)] with other member
    have near : ‖other‖ < radius := by simpa using member
    exact cutoff_one radius positive other near.le
  unfold spatialFirst
  rw [same.fderiv_eq]
  simp

theorem cutoff_tsupport (radius : ℝ) (positive : 0 < radius) :
    tsupport (cutoff radius) ⊆ closedBall (0 : Point) (2*radius) := by
  apply closure_minimal _ isClosed_closedBall
  intro point member
  change ‖point-0‖ ≤ 2*radius
  simp only [sub_zero]
  by_contra outside
  have zero := cutoff_zero radius positive point (le_of_lt (lt_of_not_ge outside))
  exact member zero

theorem cutoff_first_zero_outside (radius : ℝ) (positive : 0 < radius) (point : Point)
    (outside : 2*radius < ‖point‖) (index : Fin 3) : spatialFirst (cutoff radius) index point = 0 := by
  have absent : point ∉ tsupport (cutoff radius) := by
    intro member
    have inside := cutoff_tsupport radius positive member
    exact (not_le_of_gt outside) (by simpa using inside)
  unfold spatialFirst
  rw [fderiv_of_notMem_tsupport ℝ absent]
  rfl

theorem gradientSquare_nonnegative (f : Point → ℝ) (point : Point) : 0 ≤ gradientSquare f point :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem gradientSquare_continuous {f : Point → ℝ} (smooth : ContDiff ℝ ∞ f) : Continuous (gradientSquare f) :=
  continuous_finsetSum _ (fun index _ => (spatialFirst_smooth smooth index).continuous.pow 2)

theorem gradientSquare_integrable {f : Point → ℝ} (smooth : ContDiff ℝ ∞ f) (support : HasCompactSupport f) :
    Integrable (gradientSquare f) :=
  integrable_finsetSum _ (fun index _ => compact_square_integrable
    (spatialFirst_smooth smooth index).continuous (compact_first_support support index))

theorem cutoff_gradient_bound (radius : ℝ) (positive : 0 < radius) (point : Point) :
    gradientSquare (cutoff radius) point ≤ 3*(cutoffDerivativeBound/radius)^2 := by
  have each (index : Fin 3) : (spatialFirst (cutoff radius) index point)^2 ≤ (cutoffDerivativeBound/radius)^2 := by
    have bound := cutoff_first_bound radius positive point index
    have nonnegative : 0 ≤ cutoffDerivativeBound/radius := (div_pos cutoffDerivativeBound_positive positive).le
    have squared := (sq_le_sq₀ (norm_nonneg _) nonnegative).mpr bound
    simpa only [Real.norm_eq_abs, sq_abs] using squared
  apply (Finset.sum_le_sum (fun index _ => each index)).trans_eq
  simp

theorem cutoff_gradient_zero_inside (radius : ℝ) (positive : 0 < radius) (point : Point) (inside : ‖point‖ < radius) :
    gradientSquare (cutoff radius) point = 0 := by
  simp [gradientSquare, cutoff_first_zero_inside radius positive point inside]

theorem cutoff_gradient_zero_outside (radius : ℝ) (positive : 0 < radius) (point : Point) (outside : 2*radius < ‖point‖) :
    gradientSquare (cutoff radius) point = 0 := by
  simp [gradientSquare, cutoff_first_zero_outside radius positive point outside]

theorem cutoff_product_gradient_inside (f : Point → ℝ) (smooth : ContDiff ℝ ∞ f)
    (radius : ℝ) (positive : 0 < radius) (point : Point) (inside : ‖point‖ < radius) :
    gradientSquare (fun p => cutoff radius p*f p) point = gradientSquare f point := by
  simp only [gradientSquare, spatialFirst_mul (cutoff_smooth radius) smooth,
    cutoff_first_zero_inside radius positive point inside, cutoff_one radius positive point inside.le,
    zero_mul, one_mul, zero_add]

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
