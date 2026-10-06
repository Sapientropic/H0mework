import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.Source

/-! The concrete occupied Hamiltonian is read from the original spin and gauge connections. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation Stage9C.Material.SpinPair SU7MotherLieAlgebra
open PointwiseDiracSpinConnectionLift Stage9C.Dynamics.Homogeneous
open scoped Matrix Kronecker BigOperators
noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def occupiedConnection (j : Fin 3) : SourceMatrix :=
  (diracSpinConnectionLift (actual.gravityConnection 0) j.succ) ⊗ₖ
      (1 : Matrix (Fin 3) (Fin 3) ℂ) +
    (1 : DiracMatrix) ⊗ₖ ((actual.gaugeConnection 0 j.succ).1 : Matrix (Fin 3) (Fin 3) ℂ)

theorem occupiedConnection_readback (j : Fin 3) :
    occupiedConnection j =
      ((spinScale : ℂ)/2) • (spinRotation j ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) +
      (gaugeScale : ℂ) • ((1 : DiracMatrix) ⊗ₖ
        ((sourceColorP286Generator j).1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
  unfold occupiedConnection
  rw [actual_gravityConnection,actual_gaugeConnection,homogeneousSpinLift]
  have gauge : gaugePotential gaugeScale j.succ=gaugeScale • sourceColorP286Generator j := by
    fin_cases j <;> rfl
  change _ + (1 : DiracMatrix) ⊗ₖ ((gaugePotential gaugeScale j.succ).1 : Matrix (Fin 3) (Fin 3) ℂ) = _
  rw [gauge]
  simp [Matrix.smul_kronecker,Matrix.kronecker_smul]

def occupiedDiracConstant : SourceMatrix :=
  Complex.I • ∑ j, (diracGamma j.succ ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))*occupiedConnection j +
    (((frequency/lapse : ℝ) : ℂ)) •
      ((diracGammaZero*diracGammaFive) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))

theorem spin_connection_sum :
    Complex.I • ∑ j : Fin 3, diracGammaZero*diracGamma j.succ*spinRotation j =
      (3 : ℂ) • diracGammaFive := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [spinRotation,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      diracGammaFive,Fin.sum_univ_three,Fin.sum_univ_four,Matrix.mul_apply]
  all_goals norm_num [mul_add,Complex.I_mul_I,mul_neg]

private theorem tensor_sum (A : Fin 3 → DiracMatrix) :
    (∑ j, A j) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) =
      ∑ j, A j ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext a b
  simp [Matrix.kroneckerMap_apply,Matrix.sum_apply,Finset.sum_mul]

private theorem temporal_spin_square : diracGammaZero*(diracGammaZero*diracGammaFive) =
    -diracGammaFive := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [diracGammaZero,diracGammaFive,Matrix.mul_apply,Fin.sum_univ_four,
      Matrix.vecMul,dotProduct,Matrix.diagonal_apply]

theorem sourceConstant_from_original_connection :
    (lapse : ℂ) • ((diracGammaZero ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))*occupiedDiracConstant) =
      sourceConstant := by
  simp only [occupiedDiracConstant,occupiedConnection_readback,mul_add,Finset.mul_sum,
    Matrix.mul_smul,smul_add,Finset.smul_sum,← Matrix.mul_kronecker_mul,Matrix.one_mul,
    Matrix.mul_one]
  rw [Finset.sum_add_distrib]
  have spin := congrArg (fun M : DiracMatrix => M ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))
    spin_connection_sum
  simp only [Matrix.smul_kronecker,tensor_sum,mul_assoc] at spin
  simp only [← Finset.smul_sum,temporal_spin_square]
  have reorder (M : SourceMatrix) :
      (lapse : ℂ) • Complex.I • ((spinScale : ℂ)/2) • M =
        ((lapse : ℂ)*(spinScale : ℂ)/2) • (Complex.I • M) := by
    simp only [smul_smul]
    congr 1
    ring
  rw [reorder,spin]
  unfold sourceConstant sourceCharge sourceColorTerm
  have negTensor : (-diracGammaFive) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) =
      -(diracGammaFive ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
    ext a b
    simp [Matrix.kroneckerMap_apply]
  rw [negTensor]
  simp only [← Finset.smul_sum,smul_neg,smul_smul]
  push_cast
  have nonzero : (lapse : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt lapse_pos
  field_simp
  module

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
