import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.CutoffSupport

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Filter
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel
open scoped Topology
noncomputable section

theorem cutoff_norm_bound (radius : ℝ) (point : Point) : ‖cutoff radius point‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (cutoff_nonnegative radius point)]
  exact cutoff_le_one radius point

theorem cutoff_mul_integrable (f : Point → ℝ) (integrable : Integrable f) (radius : ℝ) :
    Integrable (fun point => cutoff radius point*f point) :=
  integrable.bdd_mul (cutoff_smooth radius).continuous.aestronglyMeasurable
    (Eventually.of_forall (cutoff_norm_bound radius))

theorem cutoff_mul_tendsto (f : Point → ℝ) (integrable : Integrable f) :
    Tendsto (fun radius : ℝ => ∫ point : Point, cutoff radius point*f point) atTop (𝓝 (∫ point : Point, f point)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun point => ‖f point‖)
  · exact Eventually.of_forall (fun radius => (cutoff_mul_integrable f integrable radius).aestronglyMeasurable)
  · exact Eventually.of_forall (fun radius => Eventually.of_forall (fun point => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_norm_bound radius point)))
  · exact integrable.norm
  · apply Eventually.of_forall
    intro point
    have same : (fun radius : ℝ => cutoff radius point*f point) =ᶠ[atTop] (fun _ => f point) := by
      filter_upwards [eventually_ge_atTop (‖point‖+1)] with radius large
      rw [cutoff_one radius (by linarith [norm_nonneg point]) point (by linarith), one_mul]
    exact tendsto_const_nhds.congr' same.symm

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
