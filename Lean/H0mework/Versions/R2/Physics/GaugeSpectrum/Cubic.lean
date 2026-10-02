import H0mework.Versions.R2.Physics.GaugeSpectrum.Ground

/-! The oriented antisymmetric cubic of the three actual magnetic responses
calculates to a color-singlet Dirac exchange. The six-term contraction is
fixed by the source triad's orientation. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF
open scoped Kronecker

noncomputable section

def orientedCubic {ι : Type*} [Fintype ι] (fields : Fin 3 → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (-Complex.I / 6) •
    (fields 0 * fields 1 * fields 2 + fields 1 * fields 2 * fields 0 + fields 2 * fields 0 * fields 1 -
      fields 0 * fields 2 * fields 1 - fields 2 * fields 1 * fields 0 - fields 1 * fields 0 * fields 2)

def cubic (point : BasePoint) : State.Observable := orientedCubic (dualCurvature point)

theorem dualCurvature_triple (point : BasePoint) (first second third : Fin 3) :
    dualCurvature point first * dualCurvature point second * dualCurvature point third =
      ((curvatureScale : ℂ) ^ 3) • (exchange ⊗ₖ (pauli first * pauli second * pauli third)) := by
  simp only [dualCurvature_normalForm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.mul_kronecker_mul, exchange_square, Matrix.one_mul]
  congr 1
  ring

theorem cubic_normalForm (point : BasePoint) :
    cubic point = ((curvatureScale : ℂ) ^ 3) • (exchange ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold cubic orientedCubic
  simp_rw [dualCurvature_triple]
  ext ⟨spin, color⟩ ⟨other, input⟩
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  rw [pauli_explicit]
  fin_cases color <;> fin_cases input <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq]
  all_goals ring_nf; simp [Complex.I_sq]; ring

theorem cubic_hermitian (point : BasePoint) : (cubic point).IsHermitian := by
  rw [cubic_normalForm]
  change _ᴴ = _
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker, exchange_hermitian.eq]

theorem cubic_square (point : BasePoint) : cubic point * cubic point =
    ((curvatureScale : ℂ) ^ 6) • 1 := by
  rw [cubic_normalForm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.mul_kronecker_mul, exchange_square, Matrix.one_mul, Matrix.one_kronecker_one]
  congr 1
  ring

theorem cubic_colorSinglet (point : BasePoint) (colorAction : Matrix (Fin 2) (Fin 2) ℂ) :
    cubic point * ((1 : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) ⊗ₖ colorAction) =
      ((1 : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) ⊗ₖ colorAction) * cubic point := by
  simp only [cubic_normalForm, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

def movedCubic (element : SU7ExteriorMatterRepresentation.SU7MotherGroup)
    (point : BasePoint) : State.Observable := orientedCubic (movedDualCurvature element point)

theorem movedCubic_eq (element : SU7ExteriorMatterRepresentation.SU7MotherGroup)
    (point : BasePoint) : movedCubic element point = cubic point := by
  simp only [movedCubic, orientedCubic, movedDualCurvature_eq, cubic]

theorem cubic_ground_mean (point : BasePoint) : groundEvaluation (cubic point) = 0 := by
  rw [groundEvaluation_diagonal, cubic_normalForm]
  simp [exchange, Stage9DEF.Compatibility.spinFlip]

theorem cubic_ground_secondMoment (point : BasePoint) :
    groundEvaluation (star (cubic point) * cubic point) = (curvatureScale : ℂ) ^ 6 := by
  rw [Matrix.star_eq_conjTranspose, (cubic_hermitian point).eq, cubic_square,
    map_smul, groundEvaluation_one, smul_eq_mul, mul_one]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
