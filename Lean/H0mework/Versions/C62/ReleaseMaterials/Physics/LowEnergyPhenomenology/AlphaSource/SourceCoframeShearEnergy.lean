import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRotationGreen

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalJointGeneratorEnergyReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationVacuumVoltageGaussGreen PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open GaussHistoryHilbert CanonicalGradedSpatialSource
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- The original spacetime shear changes the time column of the source coframe. -/
def sourceShearMatrix (v : Fin 3→ℝ) : LorentzianCoframe :=
  fun mu nu=>if nu=0 then Fin.cases 0 v mu else 0

private def shearDirection (s : ActionState) (v : Fin 3→ℝ) : ActionState :=
  (s.1*sourceShearMatrix v,(fun mu=>if mu=0 then ∑j : Fin 3,v j • s.2.1 j.succ else 0),0)

/-- Coframe and connection are varied together by the actual source one-form shear. -/
def sourceActualShearDirection (v : Fin 3→ℝ) : ActionState:=shearDirection sourceVoltageActualState v

/-- The same spacetime Jacobian pulls back both original source one-forms. -/
def sourceActualShearState (v : Fin 3→ℝ) (t : ℝ) : ActionState :=
  (sourceVoltageActualState.1*(1+t • sourceShearMatrix v),
    (fun mu=>∑nu : Fin 4,(1+t • sourceShearMatrix v) nu mu • sourceVoltageActualState.2.1 nu),
    sourceVoltageActualState.2.2)

theorem sourceActualShearState_line (v : Fin 3→ℝ) (t : ℝ) :
    sourceActualShearState v t=sourceVoltageActualState+t • sourceActualShearDirection v := by
  apply Prod.ext
  · change sourceVoltageActualState.1*(1+t • sourceShearMatrix v)=
      sourceVoltageActualState.1+t • (sourceVoltageActualState.1*sourceShearMatrix v)
    rw [mul_add,mul_one,mul_smul_comm]
  · apply Prod.ext
    · funext mu
      change (∑nu : Fin 4,(1+t • sourceShearMatrix v) nu mu • sourceVoltageActualState.2.1 nu)=
        sourceVoltageActualState.2.1 mu+t • (if mu=0 then ∑j : Fin 3,v j • sourceVoltageActualState.2.1 j.succ else 0)
      simp only [Matrix.add_apply,Matrix.one_apply,Matrix.smul_apply,add_smul,ite_smul,one_smul,zero_smul,
        Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,sourceShearMatrix]
      by_cases time : mu=0
      · subst mu
        simp only [ite_true]
        rw [Fin.sum_univ_succ]
        simp only [Fin.cases_zero,Fin.cases_succ,smul_eq_mul,mul_zero,zero_smul,zero_add,Finset.smul_sum,smul_smul]
      · simp only [if_neg time,smul_eq_mul,mul_zero,zero_smul,Finset.sum_const_zero,smul_zero,add_zero]
    · change sourceVoltageActualState.2.2=sourceVoltageActualState.2.2+t • (0:SourceMatrix)
      rw [smul_zero,add_zero]

private theorem coefficient_shear (s : ActionState) (valid : s∈validStates) (v : Fin 3→ℝ) (mu : Fin 4) :
    sourceCoframeCoefficientJet s.1 (s.1*sourceShearMatrix v) mu=
      (-(Fin.cases (motive:=fun _=>ℝ) 0 v mu):ℝ) • coefficientMatrix 0 s.1 := by
  have inverse : -(s.1⁻¹*(s.1*sourceShearMatrix v)*s.1⁻¹)= -(sourceShearMatrix v*s.1⁻¹) := by
    rw [←mul_assoc,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr valid.1),one_mul]
  have entry (a : Fin 4) : (-(sourceShearMatrix v*s.1⁻¹)) mu a=
      -(Fin.cases (0:ℝ) v mu)*(s.1⁻¹) 0 a := by
    simp only [Matrix.neg_apply,Matrix.mul_apply,sourceShearMatrix,ite_mul,zero_mul,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true,neg_mul]
  rw [sourceCoframeCoefficientJet,inverse,sourceCoframeCoefficientLinear_original]
  simp only [sourceCoframeCoefficientLinear,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  change (∑a : Fin 4,(-(sourceShearMatrix v*s.1⁻¹)) mu a •
    (Complex.I • spinCoordinates (DiracCliffordRepresentation.diracGamma a)))=
    (-(Fin.cases (motive:=fun _=>ℝ) 0 v mu):ℝ) •
      ∑a : Fin 4,(s.1⁻¹) 0 a • (Complex.I • spinCoordinates (DiracCliffordRepresentation.diracGamma a))
  simp only [entry,Finset.smul_sum,smul_smul]

private theorem lower_shear (s : ActionState) (valid : s∈validStates) (v : Fin 3→ℝ) :
    sourceLowerJet s (shearDirection s v)=0 := by
  rw [sourceLowerJet,Fin.sum_univ_succ]
  simp only [shearDirection,coefficient_shear s valid,
    Fin.cases_zero,Fin.cases_succ,neg_zero,zero_smul,zero_mul,Fin.succ_ne_zero,ite_true,ite_false,
    mul_zero,add_zero,zero_add,Finset.mul_sum,mul_smul_comm,smul_mul_assoc]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [neg_smul]
  abel

private theorem inverse_shear (s : ActionState) (valid : s∈validStates) (v : Fin 3→ℝ) :
    sourcePrincipalInverseJet s (shearDirection s v)=0 := by
  simp only [sourcePrincipalInverseJet,shearDirection,coefficient_shear s valid,Fin.cases_zero,
    neg_zero,zero_smul,mul_zero,zero_mul,neg_zero]

/-- The source connection term cancels the coframe-induced lower variation, leaving exactly the spatial translation energy. -/
theorem sourceActualShearEnergy_coefficients (v : Fin 3→ℝ) (k : Fin 4) :
    sourceHamiltonianJetMatrix sourceVoltageActualState (sourceActualShearDirection v) k=
      Fin.cases 0 (fun j=>-(v j) • (1:SourceMatrix)) k := by
  have valid:=PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint
  cases k using Fin.cases
  · simp only [sourceHamiltonianJetMatrix,sourceActualShearDirection,Fin.cases_zero,inverse_shear _ valid,
      lower_shear _ valid,zero_mul,mul_zero,add_zero,smul_zero]
  · rename_i j
    simp only [sourceHamiltonianJetMatrix,sourceActualShearDirection,Fin.cases_succ]
    rw [inverse_shear _ valid]
    simp only [zero_mul,zero_add,shearDirection,coefficient_shear _ valid,Fin.cases_succ]
    rw [mul_smul_comm,←principalMatrix_coefficient,
      Ring.inverse_mul_cancel _ (principalMatrix_regular _ valid.2)]

/-- This is the derivative of the original full Hamiltonian along that same source shear. -/
theorem sourceActualShearEnergy_generated (v : Fin 3→ℝ) (k : Fin 4) :
    HasDerivAt (fun t : ℝ=>stateHamiltonian (sourceActualShearState v t) k)
      (Fin.cases 0 (fun j=>-(v j) • (1:SourceMatrix)) k) 0 := by
  simpa only [sourceActualShearState_line,sourceActualShearEnergy_coefficients] using
    sourceHamiltonianJetMatrix_derivative sourceVoltageActualState (sourceActualShearDirection v)
      (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint) k

theorem sourceActualShearEnergy_symbol (v : Fin 3→ℝ) (p : PhysicalMomentum) :
    affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState (sourceActualShearDirection v)) p=
      -((∑j : Fin 3,p j*v j:ℝ):ℂ) • (1:SourceMatrix) := by
  simp only [affineMatrix,sourceActualShearEnergy_coefficients,Fin.cases_zero,Fin.cases_succ,zero_add,
    RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]
  change (∑j : Fin 3,((p j:ℂ)*((-v j:ℝ):ℂ)) • (1:SourceMatrix))=
    -((∑j : Fin 3,p j*v j:ℝ):ℂ) • (1:SourceMatrix)
  simp only [Complex.ofReal_neg,mul_neg,←Finset.sum_smul,←Complex.ofReal_mul]
  rw [Finset.sum_neg_distrib,←Complex.ofReal_sum]

end LowEnergy.PreparationPhysicalJointGeneratorEnergyReturn
