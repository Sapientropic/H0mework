import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.GaugeCurrent
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.DualPairing

/-! The original gauge current keeps its kinetic weight, separately from the force Hamiltonian. -/
set_option autoImplicit false
open MeasureTheory
open scoped Matrix Kronecker InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction SU7MotherLieAlgebra
open StageNineFullDiracAdjointMaterial Stage9C.Material.SpinPair Fermion
noncomputable section
attribute [local instance] instLinearOrderSourceIndex

private theorem charge_spin_commutes (j : Fin 3) :
    diracGammaFive*(diracGammaZero*diracGamma j.succ)=
      (diracGammaZero*diracGamma j.succ)*diracGammaFive := by
  have temporal : diracGammaFive*diracGammaZero= -(diracGammaZero*diracGammaFive) :=
    eq_neg_of_add_eq_zero_left (diracGammaFive_anticommutes 0)
  have spatial := eq_neg_of_add_eq_zero_left (diracGammaFive_anticommutes j.succ)
  calc
    _=(diracGammaFive*diracGammaZero)*diracGamma j.succ := (mul_assoc _ _ _).symm
    _= -(diracGammaZero*(diracGammaFive*diracGamma j.succ)) := by rw [temporal]; noncomm_ring
    _=_ := by rw [spatial]; noncomm_ring

theorem gaugeHamiltonian_commutes_charge (data : LorentzianIndex → P286LieBlockData) :
    sourceCharge*gaugeHamiltonianMatrix data=gaugeHamiltonianMatrix data*sourceCharge := by
  simp only [sourceCharge,gaugeHamiltonianMatrix_terms,mul_add,add_mul,Matrix.mul_smul,
    Matrix.smul_mul,Finset.mul_sum,Finset.sum_mul,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,charge_spin_commutes]

def gaugeCurrentMatrix (data : LorentzianIndex → P286LieBlockData) : SourceMatrix :=
  ((spinScale*lapse : ℝ) : ℂ) • (sourceExchange*gaugeDiracMatrix data)

theorem gaugeCurrentMatrix_weight (data : LorentzianIndex → P286LieBlockData) :
    gaugeCurrentMatrix data= -(spinScale : ℂ) • (sourceCharge*gaugeHamiltonianMatrix data) := by
  have spin : diracGammaFive*diracGammaZero= -diracAdjointSpinSwap := by
    have value := congrArg (fun A : DiracMatrix => A*diracGammaZero) Kinetic.exchange_gamma_time
    change (diracAdjointSpinSwap*diracGammaZero)*diracGammaZero=diracGammaFive*diracGammaZero at value
    rw [mul_assoc,diracGammaZero_sq,mul_neg,Matrix.mul_one] at value
    exact value.symm
  have time : sourceCharge*diracTimeRead= -(lapse : ℂ) • sourceExchange := by
    simp only [sourceCharge,diracTimeRead,sourceExchange,Matrix.mul_smul,
      ← Matrix.mul_kronecker_mul,Matrix.one_mul,spin]
    ext a b
    simp [Matrix.kroneckerMap_apply]
  rw [gaugeHamiltonianMatrix,← mul_assoc,time,Matrix.smul_mul]
  simp only [gaugeCurrentMatrix,smul_smul,neg_mul_neg,Complex.ofReal_mul]

theorem gaugeCurrentMatrix_hermitian (data : LorentzianIndex → P286LieBlockData) :
    (gaugeCurrentMatrix data).conjTranspose=gaugeCurrentMatrix data := by
  rw [gaugeCurrentMatrix_weight]
  simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,gaugeHamiltonianMatrix_hermitian,
    sourceCharge_hermitian,← gaugeHamiltonian_commutes_charge]
  simp

private theorem operator_scaled_product (c : ℂ) (A B : SourceMatrix) (v : MatterFiber) :
    hamiltonianOperator (c • (A*B)) v=c • hamiltonianOperator A (hamiltonianOperator B v) := by
  unfold hamiltonianOperator
  rw [map_smul,map_mul]
  rfl

theorem gaugeCurrent_canonical (data : LorentzianIndex → P286LieBlockData) (v : MatterFiber) :
    gaugeCurrentValue data v ((spinScale : ℂ) • fullCanonicalDiracAdjoint (tripletLift v))=
      (inner ℂ v (hamiltonianOperator (gaugeCurrentMatrix data) v)).re := by
  rw [gaugeCurrentMatrix,operator_scaled_product,inner_smul_right,gaugeCurrentValue,LinearMap.smul_apply]
  have paired := triplet_canonical_dual v (hamiltonianOperator (gaugeDiracMatrix data) v)
  change fullCanonicalDiracAdjoint (tripletLift v) (tripletLift (gaugeDiracMatrix data*ᵥv))=_ at paired
  rw [paired]
  simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

def spatialCurrentOperator (data : LorentzianIndex → P286LieBlockData) : MatterL2 →L[ℂ] MatterL2 :=
  (hamiltonianOperator (gaugeCurrentMatrix data)).compLpL 2 volume

theorem spatial_matrix_selfAdjoint (A : SourceMatrix) (hermitian : A.conjTranspose=A) :
    IsSelfAdjoint ((hamiltonianOperator A).compLpL 2 volume : MatterL2 →L[ℂ] MatterL2) := by
  have finite : IsSelfAdjoint (hamiltonianOperator A) := by
    change star (hamiltonianOperator A)=hamiltonianOperator A
    unfold hamiltonianOperator
    rw [← map_star]
    exact congrArg (Matrix.toEuclideanCLM (n := SourceIndex) (𝕜 := ℂ)) hermitian
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hamiltonianOperator A).coeFn_compLpL u,
    (hamiltonianOperator A).coeFn_compLpL v] with x hu hv
  change inner ℂ (((hamiltonianOperator A).compLpL 2 volume) u x) (v x)=
    inner ℂ (u x) (((hamiltonianOperator A).compLpL 2 volume) v x)
  rw [hu,hv]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp finite) (u x) (v x)

theorem spatialCurrent_selfAdjoint (data : LorentzianIndex → P286LieBlockData) :
    IsSelfAdjoint (spatialCurrentOperator data) :=
  spatial_matrix_selfAdjoint _ (gaugeCurrentMatrix_hermitian data)

def spatialGaugeHamiltonian (data : LorentzianIndex → P286LieBlockData) : MatterL2 →L[ℂ] MatterL2 :=
  (hamiltonianOperator (gaugeHamiltonianMatrix data)).compLpL 2 volume

theorem spatialGaugeHamiltonian_selfAdjoint (data : LorentzianIndex → P286LieBlockData) :
    IsSelfAdjoint (spatialGaugeHamiltonian data) :=
  spatial_matrix_selfAdjoint _ (gaugeHamiltonianMatrix_hermitian data)

theorem spatialCurrent_inner (data : LorentzianIndex → P286LieBlockData) (v : MatterL2) :
    (inner ℂ v (spatialCurrentOperator data v)).re=
      (∫ x, inner ℂ (v x) (hamiltonianOperator (gaugeCurrentMatrix data) (v x))).re := by
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hamiltonianOperator (gaugeCurrentMatrix data)).coeFn_compLpL v] with x hx
  rw [show spatialCurrentOperator data v x=
    (hamiltonianOperator (gaugeCurrentMatrix data)) (v x) from hx]

theorem spatialCurrent_integrable (data : LorentzianIndex → P286LieBlockData) (v : MatterL2) :
    Integrable (fun x => inner ℂ (v x) (hamiltonianOperator (gaugeCurrentMatrix data) (v x))) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ) v (spatialCurrentOperator data v)).congr
  filter_upwards [(hamiltonianOperator (gaugeCurrentMatrix data)).coeFn_compLpL v] with x hx
  rw [show spatialCurrentOperator data v x=
    (hamiltonianOperator (gaugeCurrentMatrix data)) (v x) from hx]

theorem spatialCurrent_original (data : LorentzianIndex → P286LieBlockData) (v : MatterL2) :
    (inner ℂ v (spatialCurrentOperator data v)).re=
      ∫ x, gaugeCurrentValue data (v x)
        ((spinScale : ℂ) • fullCanonicalDiracAdjoint (tripletLift (v x))) := by
  rw [spatialCurrent_inner]
  change RCLike.re (∫ x, inner ℂ (v x) (hamiltonianOperator (gaugeCurrentMatrix data) (v x)))=_
  rw [← integral_re (spatialCurrent_integrable data v)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => (gaugeCurrent_canonical data (v x)).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
