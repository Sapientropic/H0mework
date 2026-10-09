import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def polynomial (A : Matrix ι ι ℂ) (N : ℕ) : Matrix ι ι ℂ :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹) • A^n

theorem term_bound (A : Matrix ι ι ℂ) (r : ℝ) (size : ‖A‖ ≤ r) (N n : ℕ) :
    ‖(((n+N).factorial : ℂ)⁻¹) • A^(n+N)‖ ≤ (r^N/(N.factorial : ℝ))*r^n := by
  rw [norm_smul,norm_inv,Complex.norm_natCast]
  have denominator : (N.factorial : ℝ) ≤ ((n+N).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_left N n)
  have coefficient : ((n+N).factorial : ℝ)⁻¹ ≤ (N.factorial : ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast Nat.factorial_pos N) denominator
  have power : ‖A^(n+N)‖ ≤ r^(n+N) := (norm_pow_le A _).trans (pow_le_pow_left₀ (norm_nonneg A) size _)
  calc
    _ ≤ (N.factorial : ℝ)⁻¹*r^(n+N) := mul_le_mul coefficient power (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem polynomial_error (A : Matrix ι ι ℂ) (r : ℝ) (rpos : 0 ≤ r) (small : r < 1)
    (size : ‖A‖ ≤ r) (N : ℕ) : ‖NormedSpace.exp A-polynomial A N‖ ≤ (r^N/(N.factorial : ℝ))/(1-r) := by
  have series := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have split := series.summable.sum_add_tsum_nat_add N
  rw [series.tsum_eq] at split
  have tail : NormedSpace.exp A-polynomial A N=∑' n : ℕ, (((n+N).factorial : ℂ)⁻¹) • A^(n+N) := by
    unfold polynomial
    exact (eq_sub_of_add_eq' split).symm
  rw [tail]
  have geometric := (hasSum_geometric_of_lt_one rpos small).mul_left (r^N/(N.factorial : ℝ))
  have bound := tsum_of_norm_bounded geometric (term_bound A r size N)
  simpa only [div_eq_mul_inv] using bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
