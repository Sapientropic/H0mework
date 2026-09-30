import H0mework.Chemistry.LAlanineThermalDynamics.FiniteControllerFlow

/-! # Spectral density readout bounds every observable by its operator norm -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.StrictThermal

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conjugation_norm (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    ‖Unitary.conjStarAlgAut ℂ _ U A‖ = ‖A‖ := by
  exact NonUnitalStarAlgHom.norm_map (Unitary.conjStarAlgAut ℂ _ U)
    (Unitary.conjStarAlgAut ℂ _ U).injective A

theorem matrix_entry_norm_le (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let v : EuclideanSpace ℂ ι := PiLp.single 2 j (1 : ℂ)
  have coordinate := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A v) i
  have bound := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm v
  have read : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A v) i = A i j := by
    change (A *ᵥ Pi.single j (1 : ℂ)) i = A i j
    simp
  rw [read] at coordinate
  exact coordinate.trans (by
    simpa only [v, PiLp.norm_single, norm_one, mul_one,
      Matrix.l2_opNorm_toEuclideanCLM] using bound)

theorem energy_abs_le_norm (O rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) : |Collision.energy O rho| ≤ ‖O‖ := by
  let U := star positive.isHermitian.eigenvectorUnitary
  let A := Unitary.conjStarAlgAut ℂ _ U O
  have read : Collision.energy O rho = ∑ i, (A i i).re * positive.isHermitian.eigenvalues i := by
    rw [← Work.Capacity.energy_unitary_conjugation O rho U]
    change Collision.energy A
      (Unitary.conjStarAlgAut ℂ _ (star positive.isHermitian.eigenvectorUnitary) rho) = _
    rw [positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
    simp [Collision.energy, Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Complex.mul_re]
  rw [read]
  calc
    _ ≤ ∑ i, |(A i i).re| * positive.isHermitian.eigenvalues i := by
      simpa only [abs_mul, abs_of_nonneg (positive.eigenvalues_nonneg _)] using
        Finset.abs_sum_le_sum_abs (fun i => (A i i).re * positive.isHermitian.eigenvalues i)
          Finset.univ
    _ ≤ ∑ i, ‖O‖ * positive.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (positive.eigenvalues_nonneg i)
      exact (Complex.abs_re_le_norm _).trans
        ((matrix_entry_norm_le A i i).trans_eq (conjugation_norm U O))
    _ = _ := by
      rw [← Finset.mul_sum, Thermal.Quantum.eigenvalues_normalized rho positive normalized, mul_one]

end

end LAlanine40K2025.Thermal.Load.Producer.StrictThermal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
