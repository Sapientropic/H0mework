import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Translation
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Pair

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open scoped SchwartzMap
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
open Stage9C.Material.SpinPair
noncomputable section

theorem green_pair_integrable (first second : Point → ℝ)
    (firstIntegrable : Integrable first) (secondIntegrable : Integrable second)
    (bound : ℝ) (secondBounded : ∀ point, ‖second point‖ ≤ bound) :
    Integrable (fun points : Point × Point =>
      first points.1*second points.2*green (points.2-points.1)) := by
  simp_rw [green_kernel, ← mul_div_assoc]
  exact (pair_integrable first second firstIntegrable secondIntegrable bound secondBounded).div_const _

theorem green_sub_comm (first second : Point) : green (first-second) = green (second-first) := by
  simp only [green_kernel, kernel, distance]
  congr 3
  apply Finset.sum_congr rfl
  intro index _
  simp only [Pi.sub_apply]
  ring

/-- The source Gauss equation is Kφ+j=0, so its generated potential is the negative Green convolution. -/
def potential (current : Point → ℝ) (point : Point) : ℝ :=
  -(∫ sourcePoint : Point, current sourcePoint*green (point-sourcePoint))

theorem potential_point_integrable (current : Point → ℝ) (integrable : Integrable current)
    (bound : ℝ) (bounded : ∀ point, ‖current point‖ ≤ bound) (point : Point) :
    Integrable (fun sourcePoint : Point => current sourcePoint*green (point-sourcePoint)) := by
  simp_rw [green_sub_comm point, green_kernel, ← mul_div_assoc]
  exact (integrable_mul_shifted_kernel current integrable bound bounded point).div_const _

theorem potential_weak_gauss (current : Point → ℝ) (integrable : Integrable current)
    (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, potential current point*(-(2*lapse)*testLaplacian test point)) =
      -(∫ point : Point, current point*test point) := by
  let laplace : 𝓢(Point, ℝ) := (-(2*lapse)) • testLaplacian test
  have laplace_value (point : Point) : laplace point = -(2*lapse)*testLaplacian test point := rfl
  have joint := green_pair_integrable current laplace integrable laplace.integrable
    (SchwartzMap.seminorm ℝ 0 0 laplace) (SchwartzMap.norm_le_seminorm ℝ laplace)
  have jointProd : Integrable (Function.uncurry
      (fun sourcePoint point : Point => current sourcePoint*laplace point*green (point-sourcePoint)))
      ((volume : Measure Point).prod volume) := by
    rw [← Measure.volume_eq_prod]
    convert joint using 1 <;> rfl
  have swap := integral_integral_swap jointProd
  have value (sourcePoint : Point) :
      (∫ point : Point, current sourcePoint*laplace point*green (point-sourcePoint)) =
        current sourcePoint*test sourcePoint := by
    have same : (fun point : Point => current sourcePoint*laplace point*green (point-sourcePoint)) =
        fun point => current sourcePoint*(green (point-sourcePoint)*(-(2*lapse)*testLaplacian test point)) := by
      funext point
      rw [laplace_value]
      ring
    rw [same, integral_const_mul, green_shifted_fundamental]
  have reverse (point : Point) :
      (∫ sourcePoint : Point, current sourcePoint*laplace point*green (point-sourcePoint)) =
        -potential current point*laplace point := by
    unfold potential
    rw [neg_neg, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with sourcePoint
    ring
  simp_rw [value, reverse, laplace_value, neg_mul, integral_neg] at swap
  have result := congrArg Neg.neg swap
  simpa only [neg_neg, neg_mul] using result.symm

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
