import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Potential
import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Source

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource
open scoped SchwartzMap
noncomputable section

/-- Native current of the original D3 contraction in the original U coordinate slice. -/
def sourceCurrent (point : Point) : ℝ :=
  (ChargedSource.classicalCurrentDensity 1 (spatialSlice 0 point)).re

theorem sourceCurrent_value (point : Point) : sourceCurrent point = -4*spinScale*sourceDensity point := by
  unfold sourceCurrent
  rw [ChargedSource.classical_D3_current, slice_coordinates]
  simp

theorem sourceCurrent_integrable : Integrable sourceCurrent := by
  have same : sourceCurrent = fun point => -4*spinScale*sourceDensity point := funext sourceCurrent_value
  rw [same]
  exact sourceDensity_integrable.const_mul _

theorem sourceCurrent_bound (point : Point) :
    ‖sourceCurrent point‖ ≤ ‖-4*spinScale‖*sourceBilinearBound zeroJet zeroJet := by
  rw [sourceCurrent_value, norm_mul]
  exact mul_le_mul_of_nonneg_left (source_bilinear_uniform_bound zeroJet zeroJet point) (norm_nonneg _)

def sourcePotential : Point → ℝ := potential sourceCurrent

theorem sourcePotential_point_integrable (point : Point) :
    Integrable (fun sourcePoint : Point => sourceCurrent sourcePoint*green (point-sourcePoint)) :=
  potential_point_integrable sourceCurrent sourceCurrent_integrable _ sourceCurrent_bound point

theorem sourcePotential_density (point : Point) :
    sourcePotential point = 4*spinScale*(∫ sourcePoint : Point, sourceDensity sourcePoint*green (point-sourcePoint)) := by
  unfold sourcePotential potential
  simp_rw [sourceCurrent_value, mul_assoc]
  rw [integral_const_mul, integral_const_mul]
  ring

/-- The generated potential directly satisfies the original full U Euler's weak equation with the original D3 current. -/
theorem original_D3_weak_gauss (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, sourcePotential point*sourceEuler test point) +
      (∫ point : Point, sourceCurrent point*test point) = 0 := by
  simp_rw [sourceEuler_laplacian]
  rw [sourcePotential, potential_weak_gauss sourceCurrent sourceCurrent_integrable]
  ring

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
