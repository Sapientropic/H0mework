import H0mework.Physics.GaugeSpectrum.Hilbert

/-! The bottom spectral projector is a polynomial of the source phase
Hamiltonian. Trace normalization prepares its entire ground eigenspace;
no basis vector or state is supplied by a caller. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
  LAlanine40K2025.Thermal.Preparation
open scoped ComplexOrder

noncomputable section

def groundProjector : State.Observable :=
  (1 / 2 : ℂ) • (1 - (frequency : ℂ)⁻¹ • phaseHamiltonian)

theorem groundProjector_normalForm : groundProjector =
    diagonal (fun index : Source.Index => if index.1.val < 2 then 1 else 0) := by
  have nonzero : (frequency : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt Dynamics.frequency_positive
  ext row column
  by_cases same : row = column
  · subst column
    rcases row with ⟨spin, color⟩
    fin_cases spin <;> norm_num [groundProjector, phaseHamiltonian, Dynamics.rate, nonzero]
  · simp [groundProjector, phaseHamiltonian, same]

theorem groundProjector_hermitian : groundProjector.IsHermitian := by
  rw [groundProjector_normalForm]
  change _ᴴ = _
  simp

theorem groundProjector_square : groundProjector * groundProjector = groundProjector := by
  rw [groundProjector_normalForm, Matrix.diagonal_mul_diagonal]
  congr 1
  funext index
  split_ifs <;> norm_num

theorem groundProjector_trace : groundProjector.trace = 4 := by
  rw [groundProjector_normalForm]
  rw [Matrix.trace_diagonal]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two]
  norm_num

theorem groundProjector_nonzero : groundProjector ≠ 0 := by
  intro zero
  have four := groundProjector_trace
  simp [zero] at four

theorem groundProjector_ground : phaseHamiltonian * groundProjector =
    -(frequency : ℂ) • groundProjector := by
  rw [groundProjector_normalForm, phaseHamiltonian, Matrix.diagonal_mul_diagonal]
  ext row column
  by_cases same : row = column
  · subst column
    rcases row with ⟨spin, color⟩
    fin_cases spin <;> simp [Dynamics.rate]
  · simp [same]

theorem phaseHamiltonian_lowerBound :
    (phaseHamiltonian + (frequency : ℂ) • 1).PosSemidef := by
  have form : phaseHamiltonian + (frequency : ℂ) • (1 : State.Observable) =
      diagonal (fun index : Source.Index =>
        if index.1.val < 2 then (0 : ℂ) else ((2 * frequency : ℝ) : ℂ)) := by
    ext row column
    by_cases same : row = column
    · subst column
      rcases row with ⟨spin, color⟩
      fin_cases spin <;> simp [phaseHamiltonian, Dynamics.rate] <;> ring
    · simp [phaseHamiltonian, same]
  rw [form]
  apply Matrix.PosSemidef.diagonal
  intro index
  change (0 : ℂ) ≤ if index.1.val < 2 then 0 else ((2 * frequency : ℝ) : ℂ)
  split_ifs
  · exact le_rfl
  · exact_mod_cast le_of_lt spectralFrequency_pos

def groundDensity : State.Observable := normalizedGram groundProjector

theorem groundDensity_normalForm : groundDensity = (1 / 4 : ℂ) • groundProjector := by
  have gram_eq : groundProjector * groundProjectorᴴ = groundProjector := by
    rw [groundProjector_hermitian.eq, groundProjector_square]
  have mass : gramMass groundProjector = 4 := by
    change (groundProjector * groundProjectorᴴ).trace.re = 4
    rw [gram_eq, groundProjector_trace]
    rfl
  change (gramMass groundProjector)⁻¹ • (groundProjector * groundProjectorᴴ) = _
  rw [mass, gram_eq]
  ext row column
  simp [Complex.real_smul]

theorem groundDensity_positive : groundDensity.PosSemidef := normalizedGram_posSemidef _

theorem groundDensity_trace : groundDensity.trace = 1 :=
  normalizedGram_trace _ groundProjector_nonzero

def groundEvaluation : State.Observable →ₗ[ℂ] ℂ where
  toFun observable := (groundDensity * observable).trace
  map_add' first second := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' scalar observable := by simp

theorem groundEvaluation_diagonal (observable : State.Observable) :
    groundEvaluation observable =
      (observable (0, 0) (0, 0) + observable (0, 1) (0, 1) +
        observable (1, 0) (1, 0) + observable (1, 1) (1, 1)) / 4 := by
  simp [groundEvaluation, groundDensity_normalForm, groundProjector_normalForm,
    Matrix.trace, Fintype.sum_prod_type,
    Fin.sum_univ_four, Fin.sum_univ_two, Matrix.diagonal_mul]
  ring

theorem groundEvaluation_one : groundEvaluation 1 = 1 := by
  change (groundDensity * 1).trace = 1
  rw [Matrix.mul_one, groundDensity_trace]

theorem groundEvaluation_positive (observable : State.Observable) (positive : observable.PosSemidef) :
    0 ≤ groundEvaluation observable := by
  rw [groundEvaluation_diagonal]
  exact div_nonneg
    (add_nonneg (add_nonneg (add_nonneg positive.diag_nonneg positive.diag_nonneg)
      positive.diag_nonneg) positive.diag_nonneg) (by norm_num)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
