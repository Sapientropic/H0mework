import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapReducedState
import Mathlib.Tactic.Linarith

/-!
# Energy-population and heat readouts of the same collision

Diagonal bath populations produce mixing only after contracting the actual
joint state. Both reduced targets are retained, and their energy transfers
cancel for the same system/bath Hamiltonian.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Collision

open scoped Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

def diagonalState (population : ι → ℝ) : SystemMatrix ι :=
  Matrix.diagonal (fun i => (population i : ℂ))

theorem diagonalState_trace (population : ι → ℝ) (normalized : ∑ i, population i = 1) :
    Matrix.trace (diagonalState population) = 1 := by
  unfold diagonalState
  rw [Matrix.trace_diagonal]
  exact_mod_cast normalized

theorem systemDiagonal_mixing (rho : SystemMatrix ι) (weights : ι → ℂ) (c s : ℝ)
    (rhoTrace : Matrix.trace rho = 1) (normalized : ∑ i, weights i = 1) (i : ι) :
    systemNext rho (Matrix.diagonal weights) c s i i =
      (c : ℂ) ^ 2 * rho i i + (s : ℂ) ^ 2 * weights i := by
  rw [systemNext_eq rho _ c s rhoTrace (by simpa using normalized)]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]
  ring

theorem bathDiagonal_mixing (rho : SystemMatrix ι) (weights : ι → ℂ) (c s : ℝ)
    (rhoTrace : Matrix.trace rho = 1) (normalized : ∑ i, weights i = 1) (i : ι) :
    bathNext rho (Matrix.diagonal weights) c s i i =
      (c : ℂ) ^ 2 * weights i + (s : ℂ) ^ 2 * rho i i := by
  rw [bathNext_eq rho _ c s rhoTrace (by simpa using normalized)]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]
  ring

theorem systemPopulation_mixing (rho : SystemMatrix ι) (population : ι → ℝ) (c s : ℝ)
    (rhoTrace : Matrix.trace rho = 1) (normalized : ∑ i, population i = 1) (i : ι) :
    (systemNext rho (diagonalState population) c s i i).re =
      c ^ 2 * (rho i i).re + s ^ 2 * population i := by
  have complexNormalized : ∑ i, (population i : ℂ) = 1 := by exact_mod_cast normalized
  change (systemNext rho (Matrix.diagonal (fun i => (population i : ℂ))) c s i i).re = _
  rw [systemDiagonal_mixing rho _ c s rhoTrace complexNormalized]
  simp [Complex.mul_re, pow_two]

theorem bathPopulation_mixing (rho : SystemMatrix ι) (population : ι → ℝ) (c s : ℝ)
    (rhoTrace : Matrix.trace rho = 1) (normalized : ∑ i, population i = 1) (i : ι) :
    (bathNext rho (diagonalState population) c s i i).re =
      c ^ 2 * population i + s ^ 2 * (rho i i).re := by
  have complexNormalized : ∑ i, (population i : ℂ) = 1 := by exact_mod_cast normalized
  change (bathNext rho (Matrix.diagonal (fun i => (population i : ℂ))) c s i i).re = _
  rw [bathDiagonal_mixing rho _ c s rhoTrace complexNormalized]
  simp [Complex.mul_re, pow_two]

theorem collisionProbability_range (c s : ℝ) (circle : c ^ 2 + s ^ 2 = 1) :
    0 ≤ s ^ 2 ∧ s ^ 2 ≤ 1 ∧ c ^ 2 = 1 - s ^ 2 := by
  refine ⟨sq_nonneg s, ?_, ?_⟩ <;> linarith [sq_nonneg c]

/-- Both marginal states are conserved together, including their opposite coherence terms. -/
theorem reduced_sum_conserved (rho tau : SystemMatrix ι) (c s : ℝ)
    (circle : c ^ 2 + s ^ 2 = 1) (rhoTrace : Matrix.trace rho = 1)
    (tauTrace : Matrix.trace tau = 1) :
    systemNext rho tau c s + bathNext rho tau c s = rho + tau := by
  rw [systemNext_eq rho tau c s rhoTrace tauTrace, bathNext_eq rho tau c s rhoTrace tauTrace]
  have complexCircle : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast circle
  calc
    _ = ((c : ℂ) ^ 2 + (s : ℂ) ^ 2) • (rho + tau) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    _ = rho + tau := by rw [complexCircle, one_smul]

def energy (hamiltonian state : SystemMatrix ι) : ℝ :=
  (Matrix.trace (hamiltonian * state)).re

theorem reducedEnergy_conserved (hamiltonian rho tau : SystemMatrix ι) (c s : ℝ)
    (circle : c ^ 2 + s ^ 2 = 1) (rhoTrace : Matrix.trace rho = 1)
    (tauTrace : Matrix.trace tau = 1) :
    energy hamiltonian (systemNext rho tau c s) + energy hamiltonian (bathNext rho tau c s) =
      energy hamiltonian rho + energy hamiltonian tau := by
  unfold energy
  rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add,
    reduced_sum_conserved rho tau c s circle rhoTrace tauTrace,
    Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem heatBalance (hamiltonian rho tau : SystemMatrix ι) (c s : ℝ)
    (circle : c ^ 2 + s ^ 2 = 1) (rhoTrace : Matrix.trace rho = 1)
    (tauTrace : Matrix.trace tau = 1) :
    (energy hamiltonian (systemNext rho tau c s) - energy hamiltonian rho) +
      (energy hamiltonian (bathNext rho tau c s) - energy hamiltonian tau) = 0 := by
  linarith [reducedEnergy_conserved hamiltonian rho tau c s circle rhoTrace tauTrace]

def jointHamiltonian (hamiltonian : SystemMatrix ι) : JointMatrix ι :=
  Matrix.kronecker hamiltonian 1 + Matrix.kronecker 1 hamiltonian

private theorem swap_tensor_commutes (left right : SystemMatrix ι) :
    swapOperator * Matrix.kronecker left right = Matrix.kronecker right left * swapOperator := by
  have swapped := congrArg (fun matrix : JointMatrix ι => matrix * swapOperator)
    (swap_kronecker_swap left right)
  simpa only [Matrix.mul_assoc, swap_squared, Matrix.mul_one] using swapped

theorem swap_jointHamiltonian_commutes (hamiltonian : SystemMatrix ι) :
    swapOperator * jointHamiltonian hamiltonian = jointHamiltonian hamiltonian * swapOperator := by
  simp only [jointHamiltonian, Matrix.mul_add, Matrix.add_mul, swap_tensor_commutes]
  exact add_comm _ _

/-- Equal bare Hamiltonians make the actual swap coupling energy conserving. -/
theorem partialSwap_jointHamiltonian_commutes (hamiltonian : SystemMatrix ι) (c s : ℝ) :
    jointHamiltonian hamiltonian * partialSwap c s =
      partialSwap c s * jointHamiltonian hamiltonian := by
  simp only [partialSwap, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm,
    smul_mul_assoc, Matrix.mul_one, Matrix.one_mul]
  rw [swap_jointHamiltonian_commutes]

theorem jointEnergy_conserved (hamiltonian rho tau : SystemMatrix ι) (c s : ℝ)
    (circle : c ^ 2 + s ^ 2 = 1) :
    Matrix.trace (jointHamiltonian hamiltonian * jointNext rho tau c s) =
      Matrix.trace (jointHamiltonian hamiltonian * Matrix.kronecker rho tau) := by
  unfold jointNext
  have rearrange : jointHamiltonian hamiltonian *
      (partialSwap c s * Matrix.kronecker rho tau * (partialSwap c s)ᴴ) =
        partialSwap c s * (jointHamiltonian hamiltonian * Matrix.kronecker rho tau) *
          (partialSwap c s)ᴴ := by
    calc
      _ = (jointHamiltonian hamiltonian * partialSwap c s) *
          Matrix.kronecker rho tau * (partialSwap c s)ᴴ := by simp only [Matrix.mul_assoc]
      _ = (partialSwap c s * jointHamiltonian hamiltonian) *
          Matrix.kronecker rho tau * (partialSwap c s)ᴴ := by
            rw [partialSwap_jointHamiltonian_commutes]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [rearrange, Matrix.trace_mul_cycle]
  have inverse := (partialSwap_unitary (ι := ι) c s circle).1
  change (partialSwap c s)ᴴ * partialSwap c s = 1 at inverse
  rw [inverse, Matrix.one_mul]

end

end LAlanine40K2025.Thermal.Collision
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
