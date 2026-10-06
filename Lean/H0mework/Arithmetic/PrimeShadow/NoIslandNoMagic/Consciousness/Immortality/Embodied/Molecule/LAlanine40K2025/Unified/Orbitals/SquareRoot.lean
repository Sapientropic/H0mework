import H0mework.Chemistry.LAlanineSignedEvaluator.Arithmetic
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceSignedEvaluator

def piLower : ℚ := 314159265358979323846 / 100000000000000000000
def piUpper : ℚ := 314159265358979323847 / 100000000000000000000

theorem pi_bounds : (piLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper : ℝ) := by
  constructor
  · convert! Real.pi_gt_d20.le using 1
    norm_num [piLower]
  · convert! Real.pi_lt_d20.le using 1
    norm_num [piUpper]

/-- Square-root material is checked against rational squares and independently proved pi bounds. -/
theorem sqrt_pi_contains (gamma lower upper : ℚ) (positive : 0 < gamma)
    (upper_nonnegative : 0 ≤ upper)
    (lower_square : lower^2*gamma ≤ piLower)
    (upper_square : piUpper ≤ upper^2*gamma) :
    Holds (lower,upper) (Real.sqrt (Real.pi/gamma)) := by
  have gammaPositive : (0 : ℝ) < gamma := by exact_mod_cast positive
  have lowerBound : (lower : ℝ)^2 * gamma ≤ (piLower : ℝ) := by exact_mod_cast lower_square
  have upperBound : (piUpper : ℝ) ≤ (upper : ℝ)^2 * gamma := by exact_mod_cast upper_square
  constructor
  · exact Real.le_sqrt_of_sq_le ((le_div_iff₀ gammaPositive).mpr (lowerBound.trans pi_bounds.1))
  · apply (Real.sqrt_le_left (by exact_mod_cast upper_nonnegative)).mpr
    exact (div_le_iff₀ gammaPositive).mpr (pi_bounds.2.trans upperBound)

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
