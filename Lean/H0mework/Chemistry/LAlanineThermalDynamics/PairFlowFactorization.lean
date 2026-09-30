import H0mework.Chemistry.LAlanineThermalDynamics.PairHamiltonian
import H0mework.Chemistry.LAlanineThermalDynamics.SwapExponential

/-! # The same pair flow factors into its free phase and exchange rotation -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Dynamics

open Collision
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

open scoped Matrix.Norms.Operator in
theorem pairPropagatorMatrix_eq_exp (H : SystemMatrix ι) (g time : ℝ) :
    pairPropagatorMatrix H g time =
      NormedSpace.exp ((-Complex.I * (time : ℂ)) • pairH H g) := by
  let : NormedAlgebra ℚ (PairOperator ι) := .restrictScalars ℚ ℂ (PairOperator ι)
  have continuousInverse : Continuous (pairMatrixOperatorEquiv (ι := ι)).symm :=
    (pairMatrixOperatorEquiv (ι := ι)).symm.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  unfold pairPropagatorMatrix pairPropagator
  rw [NormedSpace.map_exp _ continuousInverse]
  congr 1
  simp only [map_smul, pairHamiltonianOperator, StarAlgEquiv.symm_apply_apply, smul_smul]
  congr 1
  ring

theorem pairPropagatorMatrix_factorization (H : SystemMatrix ι) (g time : ℝ) :
    pairPropagatorMatrix H g time =
      NormedSpace.exp ((-Complex.I * (time : ℂ)) • freePairH H) *
        partialSwap (Real.cos (g * time)) (Real.sin (g * time)) := by
  rw [pairPropagatorMatrix_eq_exp, pairH, smul_add, smul_smul]
  rw [Matrix.exp_add_of_commute _ _
    (((freePairH_commute_swap H).smul_left (-Complex.I * (time : ℂ))).smul_right
      ((-Complex.I * (time : ℂ)) * (g : ℂ)))]
  have phase : (-Complex.I * (time : ℂ)) * (g : ℂ) =
      -Complex.I * ((g * time : ℝ) : ℂ) := by push_cast; ring
  rw [phase, swap_exponential]

omit [Fintype ι] in
theorem freePairH_diagonal (energy : ι → ℝ) :
    freePairH (Matrix.diagonal (fun i => (energy i : ℂ))) =
      Matrix.diagonal (fun ia : ι × ι => ((energy ia.1 + energy ia.2 : ℝ) : ℂ)) := by
  unfold freePairH jointHamiltonian
  simp only [Matrix.kronecker]
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
    Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_add]
  congr 1
  ext ia
  simp

theorem pairPropagatorMatrix_diagonal (energy : ι → ℝ) (g time : ℝ) :
    pairPropagatorMatrix (Matrix.diagonal (fun i => (energy i : ℂ))) g time =
      Matrix.diagonal (fun ia : ι × ι =>
        Complex.exp (-Complex.I * (time : ℂ) * ((energy ia.1 + energy ia.2 : ℝ) : ℂ))) *
      partialSwap (Real.cos (g * time)) (Real.sin (g * time)) := by
  rw [pairPropagatorMatrix_factorization, freePairH_diagonal, ← Matrix.diagonal_smul,
    Matrix.exp_diagonal]
  congr 1
  congr 1
  ext ia
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]

theorem pairPropagatorMatrix_diagonal_entry (energy : ι → ℝ) (g time : ℝ)
    (i a j b : ι) :
    pairPropagatorMatrix (Matrix.diagonal (fun k => (energy k : ℂ))) g time (i, a) (j, b) =
      Complex.exp (-Complex.I * (time : ℂ) * ((energy i + energy a : ℝ) : ℂ)) *
        partialSwap (Real.cos (g * time)) (Real.sin (g * time)) (i, a) (j, b) := by
  rw [pairPropagatorMatrix_diagonal, Matrix.diagonal_mul]

end

end LAlanine40K2025.Thermal.Dynamics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
