import H0mework.Chemistry.LAlanineJointNext.RegressionRealCounterexample
import H0mework.Chemistry.LAlanineThermalDynamics.SwapExponential
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropyInvariance

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.RealRestriction.Counterexample

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section

def realHamiltonian : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def hamiltonian : Matrix (Fin 2) (Fin 2) ℂ := complexify realHamiltonian

theorem realHamiltonian_symmetric : realHamiltonian.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem hamiltonian_hermitian : hamiltonian.IsHermitian :=
  complexify_hermitian realHamiltonian realHamiltonian_symmetric

theorem hamiltonian_squared : hamiltonian * hamiltonian = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hamiltonian, complexify, realHamiltonian, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]

def pulse (time : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp ((-Complex.I * (time : ℂ)) • hamiltonian)

theorem pulse_unitary (time : ℝ) : pulse time ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  let : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := .restrictScalars ℚ ℂ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff, star_smul, hamiltonian_hermitian.isSelfAdjoint.star_eq]
  simp only [star_mul, star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  module

theorem pulse_explicit (time : ℝ) : pulse time =
    !![(Real.cos time : ℂ), -Complex.I * (Real.sin time : ℂ);
      -Complex.I * (Real.sin time : ℂ), (Real.cos time : ℂ)] := by
  rw [pulse, Thermal.Dynamics.exp_neg_I_smul_involution hamiltonian hamiltonian_squared]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, complexify, realHamiltonian]

def evolved (time : ℝ) (D : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  pulse time * D * star (pulse time)

theorem evolved_positive (time : ℝ) (D : Matrix (Fin 2) (Fin 2) ℂ)
    (positive : D.PosSemidef) : (evolved time D).PosSemidef :=
  positive.mul_mul_conjTranspose_same (pulse time)

theorem evolved_trace (time : ℝ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    (evolved time D).trace = D.trace :=
  Thermal.Quantum.unitary_conjugate_trace D ⟨pulse time, pulse_unitary time⟩

theorem plus_population (time : ℝ) :
    (evolved time (state 1) 0 0).re = 1 / 2 + Real.cos time * Real.sin time := by
  rw [evolved, pulse_explicit, plus_explicit]
  norm_num [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq time]

theorem minus_population (time : ℝ) :
    (evolved time (state (-1)) 0 0).re = 1 / 2 - Real.cos time * Real.sin time := by
  rw [evolved, pulse_explicit, minus_explicit]
  norm_num [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq time]

theorem plus_quarter_population : (evolved (Real.pi / 4) (state 1) 0 0).re = 1 := by
  rw [plus_population, Real.cos_pi_div_four, Real.sin_pi_div_four]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem minus_quarter_population : (evolved (Real.pi / 4) (state (-1)) 0 0).re = 0 := by
  rw [minus_population, Real.cos_pi_div_four, Real.sin_pi_div_four]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The same real Hamiltonian exposes history invisible to every current real scalar readout. -/
theorem no_realPart_future_population :
    ¬∃ readFuture : Matrix (Fin 2) (Fin 2) ℝ → ℝ,
      ∀ D, D.PosSemidef → D.trace = 1 →
        (evolved (Real.pi / 4) D 0 0).re = readFuture (realPart D) := by
  rintro ⟨readFuture, reads⟩
  have plus := reads (state 1) (state_positive 1) plus_normalized
  have minus := reads (state (-1)) (state_positive (-1)) minus_normalized
  rw [plus_quarter_population, same_realPart] at plus
  rw [minus_quarter_population] at minus
  linarith

end
end LAlanine40K2025.JointNext.RealRestriction.Counterexample
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
