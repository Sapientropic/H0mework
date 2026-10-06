import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Translation
import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Source
import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Potential

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb
open Stage9C.Material.SpinPair
open scoped SchwartzMap
noncomputable section

theorem shifted_green_test_integrable (centre : Point) (test : 𝓢(Point, ℝ)) :
    Integrable (fun point : Point => green (point-centre)*test point) := by
  have original := (integrable_mul_shifted_kernel test test.integrable _ (SchwartzMap.norm_le_seminorm ℝ test) centre).div_const (8*Real.pi*lapse)
  have same : (fun point : Point => green (point-centre)*test point) =
      fun point => (test point*kernel (point-centre))/(8*Real.pi*lapse) := by
    funext point
    rw [green_kernel]
    ring
  rw [same]
  exact original

def pointSourcePotential {count : ℕ} (positions : Fin count → Point) (charges : Fin count → ℝ) (point : Point) : ℝ :=
  -∑ atom : Fin count, charges atom*green (point-positions atom)

theorem pointSource_test_integrable {count : ℕ} (positions : Fin count → Point) (charges : Fin count → ℝ)
    (test : 𝓢(Point, ℝ)) : Integrable (fun point => pointSourcePotential positions charges point*test point) := by
  have each := integrable_finsetSum Finset.univ (fun atom _ => (shifted_green_test_integrable (positions atom) test).const_mul (charges atom))
  convert each.neg using 1
  try rfl
  funext point
  simp only [pointSourcePotential, neg_mul, Finset.sum_mul, mul_assoc, Pi.neg_apply]

/-- A finite source acts on the original full U Euler test operator through its generated Green function. -/
theorem pointSource_original_weak_gauss {count : ℕ} (positions : Fin count → Point) (charges : Fin count → ℝ)
    (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, pointSourcePotential positions charges point*sourceEuler test point)+
      ∑ atom : Fin count, charges atom*test (positions atom) = 0 := by
  have each (atom : Fin count) : Integrable (fun point : Point => charges atom*(green (point-positions atom)*(-(2*lapse)*testLaplacian test point))) := by
    convert ((shifted_green_test_integrable (positions atom) (testLaplacian test)).const_mul (-(2*lapse))).const_mul (charges atom) using 1
    try rfl
    funext point
    ring
  have same : (fun point => pointSourcePotential positions charges point*sourceEuler test point) =
      fun point => -(∑ atom : Fin count, charges atom*(green (point-positions atom)*(-(2*lapse)*testLaplacian test point))) := by
    funext point
    simp only [pointSourcePotential, sourceEuler_laplacian, neg_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro atom _
    ring
  rw [same, integral_neg, integral_finsetSum Finset.univ (fun atom _ => each atom)]
  simp_rw [integral_const_mul, green_shifted_fundamental]
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
