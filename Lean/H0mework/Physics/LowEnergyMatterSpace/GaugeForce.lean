import H0mework.Physics.LowEnergyMatterSpace.GaugeLift
import H0mework.Physics.LowEnergyMatterSpace.GeneratorSchwartz

/-! Original P286 data generate the Hermitian force used by the spatial response. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction SU7MotherLieAlgebra
open Stage9C.Material.SpinPair Fermion
open scoped Matrix Kronecker
noncomputable section
attribute [local instance] instLinearOrderSourceIndex

def gaugeHamiltonianMatrix (data : LorentzianIndex → P286LieBlockData) : SourceMatrix :=
  diracTimeRead*gaugeDiracMatrix data

theorem tripletGaugeMatrix_skew (data : P286LieBlockData) :
    (tripletGaugeMatrix data).conjTranspose= -(tripletGaugeMatrix data) := by
  have color : (data.1 : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose= -data.1 :=
    specialUnitaryLieMatrix_star data.1
  have hyper : star (data.2.2.1 : ℂ)= -data.2.2.1 := data.2.2.property
  simp [tripletGaugeMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    color,hyper]
  abel

theorem gaugeHamiltonianMatrix_terms (data : LorentzianIndex → P286LieBlockData) :
    gaugeHamiltonianMatrix data=
      (-Complex.I) • ((1 : DiracMatrix) ⊗ₖ tripletGaugeMatrix (data 0))+
        (Complex.I*(lapse : ℂ)) • ∑ j : Fin 3,
          (diracGammaZero*diracGamma j.succ) ⊗ₖ tripletGaugeMatrix (data j.succ) := by
  simp only [gaugeHamiltonianMatrix,diracTimeRead,gaugeDiracMatrix,Fin.sum_univ_succ,
    sourceInverseGamma,Fin.succ_ne_zero,if_false,if_true,Complex.ofReal_one,one_smul,
    smul_add,mul_add,Matrix.smul_mul,Matrix.mul_smul,Finset.mul_sum,Finset.smul_sum,
    Matrix.smul_kronecker,← Matrix.mul_kronecker_mul,Matrix.one_mul]
  have temporal : diracGammaZero*diracGamma 0= -(1 : DiracMatrix) := diracGammaZero_sq
  rw [temporal]
  have nt : (lapse : ℂ)≠0 := by exact_mod_cast ne_of_gt lapse_pos
  ext a b
  simp [Matrix.kroneckerMap_apply,Matrix.one_apply]
  field_simp

theorem gaugeHamiltonianMatrix_hermitian (data : LorentzianIndex → P286LieBlockData) :
    (gaugeHamiltonianMatrix data).conjTranspose=gaugeHamiltonianMatrix data := by
  rw [gaugeHamiltonianMatrix_terms]
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,tripletGaugeMatrix_skew,
    (diracGammaZero_mul_spatial_isHermitian _).eq]
  ext a b
  simp [Matrix.kroneckerMap_apply,Matrix.sum_apply,Finset.mul_sum]

def gaugeForceOperator (data : LorentzianIndex → P286LieBlockData) :
    MatterFiber →L[ℂ] MatterFiber := (-Complex.I) • hamiltonianOperator (gaugeHamiltonianMatrix data)

theorem gaugeHamiltonian_original (data : LorentzianIndex → P286LieBlockData)
    (v : SourceIndex → ℂ) :
    tripletLift (gaugeHamiltonianMatrix data*ᵥv)=
      (lapse : ℂ) • diracMatrixMatterAction diracGammaZero
        (tripletLift (gaugeDiracMatrix data*ᵥv)) := by
  rw [gaugeHamiltonianMatrix,diracTimeRead,Matrix.smul_mul,Matrix.smul_mulVec,
    map_smul,← Matrix.mulVec_mulVec,tripletLift_tensor]
  simp [tripletLift,Matrix.one_apply]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
