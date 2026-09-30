import H0mework.NavierStokes.CartanAction.ContorsionSupport
import H0mework.NavierStokes.MaterialAction.PauliJet

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanClifford

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource StageNineLorentzConnectionVariation
open StageNineCoframeLocalDifferentiability Stage9C.Material.SpinPair SU7ExteriorBreakingYukawa
open NativePauliControl NativePauliMotherAction NativePauliJet

noncomputable section

def bivectorBlock : Fin 6 → Block :=
  ![-pauli 0, -pauli 1, -pauli 2, Complex.I • pauli 0, Complex.I • pauli 1, Complex.I • pauli 2]

def blockAction (matrix block : Block) : Block :=
  fun row column => ∑ middle : Fin 2, matrix row middle * block middle column

theorem blockAction_sum {Index : Type} [Fintype Index] (matrix : Index → Block) (block : Block) :
    blockAction (∑ index, matrix index) block = ∑ index, blockAction (matrix index) block := by
  ext row column
  simp only [blockAction, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem blockAction_smul (scalar : ℂ) (matrix block : Block) :
    blockAction (scalar • matrix) block = scalar • blockAction matrix block := by
  ext row column
  simp [blockAction, mul_assoc, mul_add]

theorem bivector_action (pair : Fin 6) (block : Block) :
    diracMatrixMatterAction (diracGamma (lorentzBivectorFirst pair) * diracGamma (lorentzBivectorSecond pair))
      (lowerMatter block) = lowerMatter (blockAction (bivectorBlock pair) block) := by
  rw [lowerMatter_apply, sourceColorDiracMatter_matrix, lowerMatter_apply]
  apply congrArg sourceColorDiracMatter
  funext spin color
  fin_cases pair <;> fin_cases spin <;> fin_cases color <;>
    simp [lorentzBivectorFirst, lorentzBivectorSecond, lowerCoefficients, bivectorBlock, blockAction,
      pauli, diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, Fin.sum_univ_two]

def spinBlock (coordinates : LorentzBivectorOneForm) (direction : Fin 4) : Block :=
  ∑ pair : Fin 6, ((coordinates direction pair / 2 : ℝ) : ℂ) • bivectorBlock pair

theorem spinBlock_action (coordinates : LorentzBivectorOneForm) (direction : Fin 4) (block : Block) :
    diracMatrixMatterAction (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm coordinates) direction)
      (lowerMatter block) = lowerMatter (blockAction (spinBlock coordinates direction) block) := by
  simp only [diracSpinConnectionLift, loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    Fin.sum_univ_six, coframeDiracMatrixMatterAction_add_matrix,
    coframeDiracMatrixMatterAction_smul_matrix, bivector_action]
  simp only [← map_smul, ← map_add]
  congr 1
  ext row column
  simp [blockAction, spinBlock, Fin.sum_univ_six, Fin.sum_univ_two]
  ring

theorem skew_phase_zero (velocity : Vector) (matrix : Block) (skew : matrix.conjTranspose = -matrix) :
    phaseResidual velocity (blockAction matrix (hermitianBlock velocity)) = 0 := by
  have diagonal_zero (index : Fin 2) : (matrix index index).re = 0 := by
    have equation := congrArg (fun value : Block => (value index index).re) skew
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def, Complex.conj_re, Complex.neg_re] at equation
    linarith
  have off : matrix 1 0 = -star (matrix 0 1) := by
    have equation := congrArg (fun value : Block => value 1 0) skew
    simpa only [Matrix.conjTranspose_apply, Matrix.neg_apply, neg_neg] using (congrArg Neg.neg equation).symm
  simp [phaseResidual, realScalar, realVector, blockAction, hermitianBlock, pauli,
    Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, off, diagonal_zero]
  ring

/-- The canonical phase sees no Lorentz bivector with three distinct Clifford indices. -/
theorem bivector_phase_zero (velocity : Vector) (direction : Fin 4) (pair : Fin 6)
    (first : direction ≠ lorentzBivectorFirst pair) (second : direction ≠ lorentzBivectorSecond pair) :
    phaseResidual velocity (spinAction (blockAction (bivectorBlock pair) (hermitianBlock velocity)) direction) = 0 := by
  have skew : (blockAction (spinPrincipal direction) (bivectorBlock pair)).conjTranspose =
      -blockAction (spinPrincipal direction) (bivectorBlock pair) := by
    fin_cases direction <;> fin_cases pair <;>
      simp_all [lorentzBivectorFirst, lorentzBivectorSecond, spinPrincipal, bivectorBlock, pauli]
    all_goals
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [blockAction, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  have associate : spinAction (blockAction (bivectorBlock pair) (hermitianBlock velocity)) direction =
      blockAction (blockAction (spinPrincipal direction) (bivectorBlock pair)) (hermitianBlock velocity) := by
    change spinPrincipal direction * (bivectorBlock pair * hermitianBlock velocity) =
      (spinPrincipal direction * bivectorBlock pair) * hermitianBlock velocity
    rw [mul_assoc]
  rw [associate]
  exact skew_phase_zero velocity _ skew

end
end SaturationMonoid.NavierStokes.NativeCartanClifford
