import H0mework.Versions.R2.Physics.SpinPair.DiracActual
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Instances.Matrix

/-! The occupied source coefficients, in the original physical momentum convention. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation Stage9C.Material.SpinPair SU7MotherLieAlgebra
open scoped Matrix Kronecker BigOperators
noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

abbrev SourceIndex := DiracSpinorIndex × Fin 3
abbrev Momentum := Fin 3 → ℝ
abbrev SourceMatrix := Matrix SourceIndex SourceIndex ℂ

def sourceCharge : SourceMatrix := diracGammaFive ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)

def sourceSpatial (j : Fin 3) : SourceMatrix :=
  -(lapse : ℂ) • ((diracGammaZero*diracGamma j.succ) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))

def sourceColorTerm (j : Fin 3) : SourceMatrix :=
  Complex.I • ((diracGammaZero*diracGamma j.succ) ⊗ₖ
    ((sourceColorP286Generator j).1 : Matrix (Fin 3) (Fin 3) ℂ))

def sourceConstant : SourceMatrix :=
  (((3*lapse*spinScale/2-frequency : ℝ) : ℂ)) • sourceCharge+
    ((lapse*gaugeScale : ℝ) : ℂ) • ∑ j, sourceColorTerm j

def sourceHamiltonian (k : Momentum) : SourceMatrix :=
  sourceConstant+∑ j, (k j : ℂ) • sourceSpatial j

def fourierHamiltonian (xi : Momentum) : SourceMatrix :=
  sourceHamiltonian (fun j => 2*Real.pi*xi j)

theorem sourceCharge_hermitian : sourceCharge.conjTranspose=sourceCharge := by
  rw [sourceCharge,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGammaFive,Matrix.conjTranspose_apply]

theorem sourceSpatial_hermitian (j : Fin 3) :
    (sourceSpatial j).conjTranspose=sourceSpatial j := by
  simp [sourceSpatial,Matrix.conjTranspose_smul,Matrix.conjTranspose_kronecker,
    (diracGammaZero_mul_spatial_isHermitian j).eq]

theorem sourceColorTerm_hermitian (j : Fin 3) :
    (sourceColorTerm j).conjTranspose=sourceColorTerm j := by
  have color : ((sourceColorP286Generator j).1 : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose=
      -((sourceColorP286Generator j).1 : Matrix (Fin 3) (Fin 3) ℂ) :=
    specialUnitaryLieMatrix_star _
  simp [sourceColorTerm,Matrix.conjTranspose_smul,Matrix.conjTranspose_kronecker,
    (diracGammaZero_mul_spatial_isHermitian j).eq,color]
  ext a b
  simp [Matrix.kroneckerMap_apply]

theorem sourceConstant_hermitian : sourceConstant.conjTranspose=sourceConstant := by
  simp [sourceConstant,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    sourceCharge_hermitian,Matrix.conjTranspose_sum,sourceColorTerm_hermitian]

theorem sourceHamiltonian_hermitian (k : Momentum) :
    (sourceHamiltonian k).conjTranspose=sourceHamiltonian k := by
  simp [sourceHamiltonian,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul,sourceConstant_hermitian,sourceSpatial_hermitian]

theorem sourceHamiltonian_continuous : Continuous sourceHamiltonian := by
  unfold sourceHamiltonian
  fun_prop

theorem fourierHamiltonian_hermitian (xi : Momentum) :
    (fourierHamiltonian xi).conjTranspose=fourierHamiltonian xi :=
  sourceHamiltonian_hermitian _

theorem fourierHamiltonian_continuous : Continuous fourierHamiltonian := by
  apply sourceHamiltonian_continuous.comp
  fun_prop

private theorem spin_commutes (j : Fin 3) :
    diracGammaFive*(diracGammaZero*diracGamma j.succ) =
      (diracGammaZero*diracGamma j.succ)*diracGammaFive := by
  have first : diracGammaFive*diracGammaZero= -(diracGammaZero*diracGammaFive) :=
    eq_neg_of_add_eq_zero_left (diracGammaFive_anticommutes 0)
  have second := eq_neg_of_add_eq_zero_left (diracGammaFive_anticommutes j.succ)
  calc
    _ = (diracGammaFive*diracGammaZero)*diracGamma j.succ := (mul_assoc _ _ _).symm
    _ = -(diracGammaZero*(diracGammaFive*diracGamma j.succ)) := by rw [first]; noncomm_ring
    _ = _ := by rw [second]; noncomm_ring

theorem sourceCharge_squared : sourceCharge*sourceCharge=1 := by
  rw [sourceCharge,← Matrix.mul_kronecker_mul,diracGammaFive_sq,Matrix.one_mul]
  exact Matrix.one_kronecker_one

theorem sourceSpatial_commutes_charge (j : Fin 3) :
    sourceCharge*sourceSpatial j=sourceSpatial j*sourceCharge := by
  simp only [sourceCharge,sourceSpatial,Matrix.mul_smul,Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul,Matrix.mul_one,spin_commutes]

theorem sourceColorTerm_commutes_charge (j : Fin 3) :
    sourceCharge*sourceColorTerm j=sourceColorTerm j*sourceCharge := by
  simp only [sourceCharge,sourceColorTerm,Matrix.mul_smul,Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one,spin_commutes]

theorem sourceHamiltonian_commutes_charge (k : Momentum) :
    sourceCharge*sourceHamiltonian k=sourceHamiltonian k*sourceCharge := by
  simp only [sourceHamiltonian,sourceConstant,mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Finset.mul_sum,Finset.sum_mul,sourceColorTerm_commutes_charge,sourceSpatial_commutes_charge]

def originalHamiltonian (k : Momentum) : SourceMatrix :=
  sourceHamiltonian k+(frequency : ℂ) • sourceCharge

theorem originalHamiltonian_hermitian (k : Momentum) :
    (originalHamiltonian k).conjTranspose=originalHamiltonian k := by
  simp [originalHamiltonian,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    sourceHamiltonian_hermitian,sourceCharge_hermitian]

theorem originalHamiltonian_continuous : Continuous originalHamiltonian := by
  exact sourceHamiltonian_continuous.add continuous_const

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
