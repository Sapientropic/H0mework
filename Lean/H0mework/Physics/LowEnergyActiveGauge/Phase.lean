import H0mework.Physics.LowEnergyActive.Triplet
import H0mework.Physics.SpinPair.Phase
import H0mework.Physics.SpinPair.Actual

/-! The original upper/lower phases form the same-sided primal and independent-dual rotation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction
noncomputable section

def rotation (point : BasePoint) : DiracMatrix :=
  Matrix.diagonal ![upperPhase point, upperPhase point, lowerPhase point, lowerPhase point]

def inverseRotation (point : BasePoint) : DiracMatrix :=
  Matrix.diagonal ![lowerPhase point, lowerPhase point, upperPhase point, upperPhase point]

theorem rotation_zero : rotation 0 = 1 := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [rotation, upperPhase, lowerPhase, phase_zero]

theorem rotation_inverse (point : BasePoint) : rotation point*inverseRotation point = 1 := by
  rw [rotation, inverseRotation, Matrix.diagonal_mul_diagonal]
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [upper_lower_product, mul_comm (lowerPhase point)]

theorem rotation_gamma_swap (point : BasePoint) (internal : LorentzianIndex) :
    rotation point*diracGamma internal = diracGamma internal*inverseRotation point := by
  ext row col
  fin_cases internal <;> fin_cases row <;> fin_cases col <;>
    simp [rotation, inverseRotation, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> ring

theorem inverseRotation_gamma_swap (point : BasePoint) (internal : LorentzianIndex) :
    inverseRotation point*diracGamma internal = diracGamma internal*rotation point := by
  ext row col
  fin_cases internal <;> fin_cases row <;> fin_cases col <;>
    simp [rotation, inverseRotation, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> ring

theorem rotation_gamma_rotation (point : BasePoint) (internal : LorentzianIndex) :
    rotation point*diracGamma internal*rotation point = diracGamma internal := by
  rw [rotation_gamma_swap, Matrix.mul_assoc]
  have inverse : inverseRotation point*rotation point = 1 := by
    have commute : inverseRotation point*rotation point = rotation point*inverseRotation point := by
      simp only [rotation, inverseRotation, Matrix.diagonal_mul_diagonal]
      congr 1
      funext row
      exact mul_comm _ _
    rw [commute, rotation_inverse]
  rw [inverse, Matrix.mul_one]

theorem rotation_spin_commutes (point : BasePoint) (first second : LorentzianIndex) :
    rotation point*(diracGamma first*diracGamma second) =
      (diracGamma first*diracGamma second)*rotation point := by
  rw [← Matrix.mul_assoc, rotation_gamma_swap, Matrix.mul_assoc, inverseRotation_gamma_swap,
    ← Matrix.mul_assoc]

def rotationVelocity (point : BasePoint) : DiracMatrix :=
  (-Complex.I*(frequency : ℂ)) • (diracGammaFive*rotation point)

theorem rotation_phase_term (point : BasePoint) (internal : LorentzianIndex) :
    Complex.I • (rotation point*diracGamma internal*rotationVelocity point) =
      (frequency : ℂ) • (diracGamma internal*diracGammaFive) := by
  have commute : diracGammaFive*rotation point = rotation point*diracGammaFive := by
    simp only [diracGammaFive, rotation, Matrix.diagonal_mul_diagonal]
    congr 1
    funext row
    exact mul_comm _ _
  simp only [rotationVelocity, Matrix.mul_smul, smul_smul]
  rw [commute, ← Matrix.mul_assoc, rotation_gamma_rotation]
  congr 1
  simp [← mul_assoc]

theorem rotation_live_gamma_phase (point : BasePoint) (coefficient : LorentzianIndex → ℂ) :
    Complex.I • (rotation point*(∑ internal, coefficient internal • diracGamma internal)*rotationVelocity point) =
      (frequency : ℂ) • ((∑ internal, coefficient internal • diracGamma internal)*diracGammaFive) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro internal _
  rw [smul_comm Complex.I (coefficient internal), rotation_phase_term, smul_comm]

theorem rotation_entry_derivative (point : BasePoint) (mu row col : LorentzianIndex) :
    fieldDirectionalDerivative (fun p => rotation p row col) point mu =
      if mu = 0 then (-Complex.I*(frequency : ℂ))*(diracGammaFive*rotation point) row col else 0 := by
  by_cases diagonal : row = col
  · subst col
    fin_cases row
    all_goals first
      | change fieldDirectionalDerivative (phase frequency) point mu = _
      | change fieldDirectionalDerivative (phase (-frequency)) point mu = _
    all_goals rw [phase_directionalDerivative]
    all_goals simp [diracGammaFive, rotation, upperPhase, lowerPhase]
    all_goals split_ifs <;> ring
  · have equal : (fun p : BasePoint => rotation p row col) = fun _ => (0:ℂ) := by
      funext p
      simp [rotation, diagonal]
    rw [equal]
    simp [fieldDirectionalDerivative, diracGammaFive, rotation, diagonal]

theorem original_matter_rotation (point : BasePoint) :
    actual.matter point = diracMatrixMatterAction (rotation point) (spinPairMatter 1 1) := by
  rw [actual_matter]
  funext spin
  fin_cases spin <;>
    simp [rotation, diracMatrixMatterAction, Matrix.diagonal_apply, spinPairMatter,
      sourceColorDiracMatter, spinPairCoefficients, Fin.sum_univ_two, smul_smul]

theorem original_dual_rotation (point : BasePoint) :
    actual.conjugateMatter point =
      (spinPairDual (spinScale : ℂ) (spinScale : ℂ)).comp (diracMatrixMatterAction (rotation point)) := by
  rw [actual_conjugateMatter]
  apply LinearMap.ext
  intro matter
  simp [spinPairDual, sourceColorDiracDual, spinPairCoefficients, LinearMap.comp_apply,
    diracMatrixMatterAction, rotation, Matrix.diagonal_apply, Fin.sum_univ_four, Fin.sum_univ_two,
    map_smul, upperDualPhase, lowerDualPhase]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge
