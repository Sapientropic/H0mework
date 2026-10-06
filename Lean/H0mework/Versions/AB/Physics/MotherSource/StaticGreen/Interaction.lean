import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Potential

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
noncomputable section

/-- The interaction functional of the generated Green solution; its equality with field energy is a separate Gauss/Legendre theorem. -/
def interactionEnergy (current : Point → ℝ) : ℝ :=
  (1/2 : ℝ)*(∫ points : Point × Point, current points.1*current points.2*green (points.2-points.1))

theorem current_potential_integrable (current : Point → ℝ) (integrable : Integrable current)
    (bound : ℝ) (bounded : ∀ point, ‖current point‖ ≤ bound) :
    Integrable (fun point : Point => current point*potential current point) := by
  have joint := green_pair_integrable current current integrable integrable bound bounded
  have jointProd : Integrable (fun points : Point × Point => current points.1*current points.2*green (points.2-points.1))
      ((volume : Measure Point).prod volume) := by
    rw [← Measure.volume_eq_prod]
    convert joint using 1
  have result := jointProd.integral_prod_left
  have same (point : Point) :
      (∫ other : Point, current point*current other*green (other-point)) = -current point*potential current point := by
    unfold potential
    simp_rw [green_sub_comm _ point]
    rw [neg_mul_neg, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with other
    ring
  simp_rw [same] at result
  have negated := result.neg
  change Integrable (fun point : Point => -(-current point*potential current point)) at negated
  simpa only [neg_mul, neg_neg] using negated

theorem interaction_potential (current : Point → ℝ) (integrable : Integrable current)
    (bound : ℝ) (bounded : ∀ point, ‖current point‖ ≤ bound) :
    interactionEnergy current = -(1/2 : ℝ)*(∫ point : Point, current point*potential current point) := by
  have joint := green_pair_integrable current current integrable integrable bound bounded
  have jointProd : Integrable (fun points : Point × Point => current points.1*current points.2*green (points.2-points.1))
      ((volume : Measure Point).prod volume) := by
    rw [← Measure.volume_eq_prod]
    convert joint using 1
  unfold interactionEnergy
  rw [Measure.volume_eq_prod, integral_prod _ jointProd]
  have same (point : Point) :
      (∫ other : Point, current point*current other*green (other-point)) = -current point*potential current point := by
    unfold potential
    simp_rw [green_sub_comm _ point]
    rw [neg_mul_neg, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with other
    ring
  simp_rw [same, neg_mul, integral_neg]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
