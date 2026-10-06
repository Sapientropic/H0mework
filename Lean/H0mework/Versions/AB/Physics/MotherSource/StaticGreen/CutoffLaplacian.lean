import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.CutoffSupport

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Metric Filter
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel
open scoped ContDiff Topology
noncomputable section

theorem spatialFirst_scaled (f : Point → ℝ) (smooth : ContDiff ℝ ∞ f) (scale : ℝ) (point : Point) (index : Fin 3) :
    spatialFirst (fun p => f (scale • p)) index point = scale*spatialFirst f index (scale • point) := by
  have generated := ((smooth.differentiable (by simp)) (scale • point)).hasFDerivAt.comp point
    ((scale : ℝ) • (ContinuousLinearMap.id ℝ Point)).hasFDerivAt
  change HasFDerivAt (fun p => f (scale • p)) _ point at generated
  unfold spatialFirst
  rw [generated.fderiv]
  simp

theorem spatialFirst_const_mul (coefficient : ℝ) (f : Point → ℝ) (smooth : ContDiff ℝ ∞ f) (point : Point) (index : Fin 3) :
    spatialFirst (fun p => coefficient*f p) index point = coefficient*spatialFirst f index point := by
  unfold spatialFirst
  rw [(((smooth.differentiable (by simp)) point).hasFDerivAt.const_mul coefficient).fderiv]
  rfl

theorem cutoff_second (radius : ℝ) (point : Point) (index : Fin 3) :
    spatialFirst (spatialFirst (cutoff radius) index) index point =
      radius⁻¹^2*spatialFirst (spatialFirst cutoffSeed index) index (radius⁻¹ • point) := by
  have same : spatialFirst (cutoff radius) index = fun p => radius⁻¹*spatialFirst cutoffSeed index (radius⁻¹ • p) :=
    funext (fun p => cutoff_first radius p index)
  have smooth : ContDiff ℝ ∞ (fun p => spatialFirst cutoffSeed index (radius⁻¹ • p)) :=
    (spatialFirst_smooth cutoffSeed_smooth index).comp (((radius⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ Point)).contDiff)
  rw [same, spatialFirst_const_mul _ _ smooth, spatialFirst_scaled _ (spatialFirst_smooth cutoffSeed_smooth index)]
  ring

theorem cutoff_laplacian (radius : ℝ) (point : Point) :
    spatialLap (cutoff radius) point = radius⁻¹^2*spatialLap cutoffSeed (radius⁻¹ • point) := by
  simp only [spatialLap, cutoff_second, Finset.mul_sum]

theorem compact_spatialLap {f : Point → ℝ} (support : HasCompactSupport f) : HasCompactSupport (spatialLap f) := by
  have result := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun index : Fin 3 => spatialFirst (spatialFirst f index) index)
    (fun index _ => compact_first_support (compact_first_support support index) index)
  convert result using 1 <;> rfl

theorem cutoffSeed_laplacian_bounded : ∃ bound : ℝ, ∀ point : Point, ‖spatialLap cutoffSeed point‖ ≤ bound :=
  (compact_spatialLap cutoffSeed.hasCompactSupport).exists_bound_of_continuous (spatialLap_smooth cutoffSeed_smooth).continuous

def cutoffLaplacianBound : ℝ := max 1 cutoffSeed_laplacian_bounded.choose

theorem cutoff_laplacian_bound (radius : ℝ) (point : Point) :
    ‖spatialLap (cutoff radius) point‖ ≤ radius⁻¹^2*cutoffLaplacianBound := by
  rw [cutoff_laplacian, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    ((cutoffSeed_laplacian_bounded.choose_spec _).trans (le_max_right _ _)) (sq_nonneg _)

theorem cutoff_second_zero_inside (radius : ℝ) (positive : 0 < radius) (point : Point)
    (inside : ‖point‖ < radius) (index : Fin 3) : spatialFirst (spatialFirst (cutoff radius) index) index point = 0 := by
  have same : spatialFirst (cutoff radius) index =ᶠ[𝓝 point] (fun _ => 0) := by
    filter_upwards [isOpen_ball.mem_nhds (show point ∈ ball 0 radius by simpa using inside)] with other member
    exact cutoff_first_zero_inside radius positive other (by simpa using member) index
  change (fderiv ℝ (spatialFirst (cutoff radius) index) point) (axis index) = 0
  rw [same.fderiv_eq]
  simp

theorem cutoff_laplacian_zero_inside (radius : ℝ) (positive : 0 < radius) (point : Point) (inside : ‖point‖ < radius) :
    spatialLap (cutoff radius) point = 0 := by
  simp only [spatialLap, cutoff_second_zero_inside radius positive point inside, Finset.sum_const_zero]

theorem cutoff_laplacian_zero_outside (radius : ℝ) (positive : 0 < radius) (point : Point)
    (outside : 2*radius < ‖point‖) : spatialLap (cutoff radius) point = 0 := by
  unfold spatialLap
  apply Finset.sum_eq_zero
  intro index _
  have absent : point ∉ tsupport (spatialFirst (cutoff radius) index) := by
    intro member
    have original := tsupport_fderiv_apply_subset ℝ (axis index) member
    have near := cutoff_tsupport radius positive original
    exact (not_le_of_gt outside) (by simpa using near)
  change (fderiv ℝ (spatialFirst (cutoff radius) index) point) (axis index) = 0
  rw [fderiv_of_notMem_tsupport ℝ absent]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
