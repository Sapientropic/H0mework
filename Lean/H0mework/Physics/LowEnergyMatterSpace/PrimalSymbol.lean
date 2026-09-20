import H0mework.Physics.LowEnergyMatterSpace.PrimalLift
import H0mework.Physics.LowEnergyMatterSpace.GeneratorSchwartz

/-! The original holonomic operator recovers the same physical-time Hamiltonian. -/
set_option autoImplicit false
open scoped Matrix Kronecker
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open StageNineHolonomicField SU7MotherLieAlgebra SU7MotherGaugeTheory Stage9C.Material.SpinPair
open PointwiseDiracSpinConnectionLift Stage9C.Dynamics.Homogeneous StageNineLorentzConnectionVariation
noncomputable section
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem sourceConnectionMatrix_constant (point : BasePoint) (mu : LorentzianIndex) :
    sourceConnectionMatrix point mu=sourceConnectionMatrix 0 mu := by
  simp only [sourceConnectionMatrix,actual_gravityConnection,actual_gaugeConnection]

theorem sourceConnectionMatrix_time (point : BasePoint) : sourceConnectionMatrix point 0=0 := by
  have spinTime : diracSpinConnectionLift (homogeneousConnection spinScale) 0=0 := by
    simp only [diracSpinConnectionLift,homogeneousConnection,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm]
    simp [homogeneousContorsion,Fin.sum_univ_six]
  simp [sourceConnectionMatrix,actual_gravityConnection,actual_gaugeConnection,spinTime,
    gaugePotential,tripletGaugeMatrix]

theorem sourceConnectionMatrix_spatial (point : BasePoint) (j : Fin 3) :
    sourceConnectionMatrix point j.succ=occupiedConnection j := by
  have hyper : ((actual.gaugeConnection 0 j.succ).2.2.1 : ℂ)=0 := by
    fin_cases j <;> norm_num [actual_gaugeConnection,gaugePotential,sourceColorP286Generator,p286LieBracket]
  rw [sourceConnectionMatrix_constant]
  simp [sourceConnectionMatrix,occupiedConnection,tripletGaugeMatrix,hyper]

def originalDiracConstant : SourceMatrix :=
  Complex.I • ∑ j : Fin 3, diracSpatialMatrix j*occupiedConnection j

theorem originalDiracConstant_hamiltonian :
    diracTimeRead*originalDiracConstant=originalHamiltonian 0 := by
  have phase : diracTimeRead*
      (((frequency/lapse : ℝ) : ℂ) •
        ((diracGammaZero*diracGammaFive) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)))=
        -(frequency : ℂ) • sourceCharge := by
    simp only [diracTimeRead,sourceCharge,Matrix.mul_smul,Matrix.smul_mul,
      ← Matrix.mul_kronecker_mul,Matrix.one_mul,← mul_assoc,diracGammaZero_sq,
      neg_mul,Matrix.one_mul]
    have nonzero : (lapse : ℂ)≠0 := by exact_mod_cast ne_of_gt lapse_pos
    ext a b
    simp [Matrix.kroneckerMap_apply]
    field_simp
  have constant := diracTimeRead_constant
  change diracTimeRead*(originalDiracConstant+_)=sourceConstant at constant
  rw [mul_add,phase] at constant
  simp only [originalHamiltonian,sourceHamiltonian,Pi.zero_apply,Complex.ofReal_zero,
    zero_smul,Finset.sum_const_zero,add_zero]
  rw [neg_smul] at constant
  exact eq_add_of_add_neg_eq constant

theorem primalJet_temporal_spatial (profile : BasePoint → MatterFiber)
    (derivative : BasePoint →L[ℝ] MatterFiber) (point : BasePoint) :
    primalJet profile derivative point=
      Complex.I • ((sourceInverseGamma 0 ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))*ᵥ
        (fun index => derivative (coordinateDirection 0) index))+
      originalDiracConstant*ᵥ(fun index => profile point index)+
      Complex.I • ∑ j : Fin 3, diracSpatialMatrix j*ᵥ
        (fun index => derivative (coordinateDirection j.succ) index) := by
  rw [primalJet,Fin.sum_univ_succ]
  simp only [sourceConnectionMatrix_time,
    Matrix.zero_mulVec,add_zero,sourceConnectionMatrix_spatial,Matrix.mulVec_add,
    smul_add,Finset.sum_add_distrib,Finset.smul_sum]
  have spatial (j : Fin 3) :
      sourceInverseGamma j.succ ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)=diracSpatialMatrix j := by
    simp [sourceInverseGamma,diracSpatialMatrix]
  simp_rw [spatial,Matrix.mulVec_mulVec]
  simp only [originalDiracConstant,Matrix.smul_mulVec,Matrix.sum_mulVec,Finset.smul_sum]
  abel

private theorem temporal_gamma_product :
    Complex.I • (diracTimeRead*(sourceInverseGamma 0 ⊗ₖ
      (1 : Matrix (Fin 3) (Fin 3) ℂ)))=(-Complex.I) • (1 : SourceMatrix) := by
  simp only [diracTimeRead,sourceInverseGamma,if_true,Matrix.smul_kronecker,
    Matrix.smul_mul,Matrix.mul_smul,← Matrix.mul_kronecker_mul,Matrix.one_mul]
  change Complex.I • ((lapse⁻¹ : ℝ) : ℂ) • (lapse : ℂ) •
    ((diracGammaZero*diracGammaZero) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))=_
  rw [diracGammaZero_sq]
  have nonzero : (lapse : ℂ)≠0 := by exact_mod_cast ne_of_gt lapse_pos
  ext a b
  simp [Matrix.kroneckerMap_apply,Matrix.one_apply]
  field_simp
  by_cases spin : a.1=b.1 <;> by_cases color : a.2=b.2 <;> simp [spin,color,Prod.ext_iff]

theorem primalJet_hamiltonian (profile : BasePoint → MatterFiber)
    (derivative : BasePoint →L[ℝ] MatterFiber) (point : BasePoint) :
    diracTimeRead*ᵥprimalJet profile derivative point=
      (-Complex.I) • (fun index => derivative (coordinateDirection 0) index)+
      originalHamiltonian 0*ᵥ(fun index => profile point index)+
      (-Complex.I) • ∑ j : Fin 3, sourceSpatial j*ᵥ
        (fun index => derivative (coordinateDirection j.succ) index) := by
  rw [primalJet_temporal_spatial]
  simp only [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_sum,Matrix.mulVec_mulVec]
  rw [← Matrix.smul_mulVec,temporal_gamma_product,Matrix.smul_mulVec,Matrix.one_mulVec,
    originalDiracConstant_hamiltonian]
  congr 1
  rw [Finset.smul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.smul_mulVec,← Matrix.smul_mulVec,diracTimeRead_spatial]

theorem original_primal_hamiltonian (profile : BasePoint → MatterFiber)
    (derivative : BasePoint →L[ℝ] MatterFiber) (point : BasePoint)
    (differentiates : HasFDerivAt profile derivative point) :
    (lapse : ℂ) • diracMatrixMatterAction diracGammaZero
      (StageNineDiracDualFormNativeMotherAction.generatedContinuumDiracDualMatterVector
        StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource 0 point
        (toContinuumPointField (tripletField profile) point))=
      tripletLift ((-Complex.I) • (fun index => derivative (coordinateDirection 0) index)+
        originalHamiltonian 0*ᵥ(fun index => profile point index)+
        (-Complex.I) • ∑ j : Fin 3, sourceSpatial j*ᵥ
          (fun index => derivative (coordinateDirection j.succ) index)) := by
  rw [original_primal_differential profile derivative point differentiates,← primalJet_hamiltonian,
    diracTimeRead,Matrix.smul_mulVec,map_smul,tripletLift_tensor]
  simp [tripletLift,Matrix.one_apply]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
