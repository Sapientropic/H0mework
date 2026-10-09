import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Electromagnetic.CanonicalCoframe
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.Lapse
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.BosonCausal.Metric

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNormalizedFullField
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open Stage9C.Material.SpinPair StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open Stage9C.Dynamics.Homogeneous
open scoped Matrix Matrix.Norms.L2Operator BigOperators
local instance channelTwoQuantumIndexDecidable : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def sourceChannelTwoLorentz (v : Fin 4→ℝ) : StageNineLorentzConnectionVariation.LorentzBivectorOneForm :=
  let r:=Real.sqrt 2*Real.sqrt 15
  !![(2*r/15)*v 1,(2*r/15)*v 2,(2*r/15)*v 3,0,0,0;
     (5*r/27)*v 0,0,0,0,(10/9:ℝ)*v 3,-(10/9:ℝ)*v 2;
     0,(5*r/27)*v 0,0,-(10/9:ℝ)*v 3,0,(10/9:ℝ)*v 1;
     0,0,(5*r/27)*v 0,(10/9:ℝ)*v 2,-(10/9:ℝ)*v 1,0]

/-- The third source channel's complete spin connection before the exterior-matter lift. -/
def sourceChannelTwoSpinConnection (v : Fin 4→ℂ) (mu : Fin 4) : DiracMatrix :=
  let spatial (i : Fin 3):=((5*(Real.sqrt 30:ℂ)/54)*v 0) • (diracGammaZero*diracGamma i.succ)-
    (5/9:ℂ) • (∑j : Fin 3,if j=i then 0 else v j.succ • (diracGamma i.succ*diracGamma j.succ))
  ![(((Real.sqrt 30:ℂ)/15) • (∑j : Fin 3,v j.succ • (diracGammaZero*diracGamma j.succ))),
    spatial 0,spatial 1,spatial 2] mu

theorem sourceChannelTwoDiracConnection_generated (v : Fin 4→ℝ) (mu : Fin 4) :
    diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm (sourceChannelTwoLorentz v)) mu=
      sourceChannelTwoSpinConnection (fun k=>(v k:ℂ)) mu := by
  have roots : Real.sqrt 2*Real.sqrt 15=Real.sqrt 30 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  unfold diracSpinConnectionLift
  simp only [loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  have swap21 : diracGammaTwo*diracGammaOne= -(diracGammaOne*diracGammaTwo) :=
    eq_neg_of_add_eq_zero_right diracGammaOneTwo_anticommute
  have swap31 : diracGammaThree*diracGammaOne= -(diracGammaOne*diracGammaThree) :=
    eq_neg_of_add_eq_zero_right diracGammaOneThree_anticommute
  have swap32 : diracGammaThree*diracGammaTwo= -(diracGammaTwo*diracGammaThree) :=
    eq_neg_of_add_eq_zero_right diracGammaTwoThree_anticommute
  have fifth {α : Type} (a b c d e f : α) : (![a,b,c,d,e,f] : Fin 6→α) 5=f := rfl
  have third : (2:Fin 3).succ=(3:Fin 4) := rfl
  fin_cases mu <;>
    simp only [sourceChannelTwoLorentz,sourceChannelTwoSpinConnection,roots,
      Fin.sum_univ_six,Fin.sum_univ_three,lorentzBivectorFirst,lorentzBivectorSecond,
      diracGamma,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
      fifth,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,third,-Matrix.cons_val,Fin.reduceEq,if_true,if_false]
  all_goals try simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_zero]
  all_goals try simp only [swap21,swap31,swap32]
  all_goals module

theorem sourceChannelTwoSpin_normal (v : Fin 4→ℂ) :
    (-Complex.I) • sourceChannelTwoSpinConnection v 0+
      (Complex.I*(lapse:ℂ)) • (∑j : Fin 3,
        diracGammaZero*diracGamma j.succ*sourceChannelTwoSpinConnection v j.succ)=
      (Complex.I*v 0) • (1:DiracMatrix)-
        (Complex.I*(Real.sqrt 30:ℂ)/5) •
          (∑j : Fin 3,v j.succ • (diracGammaZero*diracGamma j.succ)) := by
  have root : (Real.sqrt 30:ℂ)^2=30 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have space_square (i : Fin 3) : diracGamma i.succ*diracGamma i.succ=(1:DiracMatrix) := by
    fin_cases i
    · exact diracGammaOne_sq
    · exact diracGammaTwo_sq
    · exact diracGammaThree_sq
  have swap (i : Fin 3) : diracGamma i.succ*diracGammaZero= -(diracGammaZero*diracGamma i.succ) := by
    fin_cases i
    · exact eq_neg_of_add_eq_zero_right diracGammaZeroOne_anticommute
    · exact eq_neg_of_add_eq_zero_right diracGammaZeroTwo_anticommute
    · exact eq_neg_of_add_eq_zero_right diracGammaZeroThree_anticommute
  have square (i : Fin 3) : (diracGammaZero*diracGamma i.succ)*
      (diracGammaZero*diracGamma i.succ)=(1:DiracMatrix) := by
    calc
      _=diracGammaZero*(diracGamma i.succ*diracGammaZero)*diracGamma i.succ := by noncomm_ring
      _=diracGammaZero*(-(diracGammaZero*diracGamma i.succ))*diracGamma i.succ := by rw [swap]
      _= -(diracGammaZero*diracGammaZero)*(diracGamma i.succ*diracGamma i.succ) := by noncomm_ring
      _=1 := by rw [diracGammaZero_sq,space_square];simp
  have cancel (i j : Fin 3) : (diracGammaZero*diracGamma i.succ)*
      (diracGamma i.succ*diracGamma j.succ)=diracGammaZero*diracGamma j.succ := by
    calc
      _=diracGammaZero*(diracGamma i.succ*diracGamma i.succ)*diracGamma j.succ := by noncomm_ring
      _=_ := by rw [space_square,mul_one]
  have time : sourceChannelTwoSpinConnection v 0=
      ((Real.sqrt 30:ℂ)/15) • (∑j : Fin 3,v j.succ • (diracGammaZero*diracGamma j.succ)) := rfl
  have spatial (i : Fin 3) : sourceChannelTwoSpinConnection v i.succ=
      ((5*(Real.sqrt 30:ℂ)/54)*v 0) • (diracGammaZero*diracGamma i.succ)-
      (5/9:ℂ) • (∑j : Fin 3,if j=i then 0 else v j.succ • (diracGamma i.succ*diracGamma j.succ)) := by
    fin_cases i <;> rfl
  rw [time]
  simp only [spatial,mul_sub,mul_smul_comm,Finset.mul_sum,mul_ite,mul_zero,square,cancel,
    smul_sub,Finset.smul_sum,smul_smul]
  rw [BosonCausal.source_lapse_closed]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Fin.sum_univ_three,Fin.reduceEq,if_true,if_false]
  match_scalars
  all_goals ring_nf
  all_goals simp only [root]
  all_goals ring

private theorem spinCoordinates_mul (A B : DiracMatrix) :
    spinCoordinates (A*B)=spinCoordinates A*spinCoordinates B := by
  change Quantum.operatorMatrix (diracMatrixMatterAction (A*B))=_
  rw [SU7ExteriorBreakingYukawa.diracMatrixMatterAction_mul,Quantum.matrix_composition]
  rfl

private theorem sourcePrincipalInverse_actual :
    Ring.inverse (principalMatrix (actual.coframe 0))=
      (Complex.I*(lapse:ℂ)) • spinCoordinates diracGammaZero := by
  rw [principal_inverse_original _ (actual_noncharacteristic 0),actual_coframe,
    InducedQuantum.lapse_temporal_inverse lapse lapse_pos.ne',map_smul]
  rfl

private theorem sourceSpatialCoefficient_actual (j : Fin 3) :
    coefficientMatrix j.succ (actual.coframe 0)=Complex.I • spinCoordinates (diracGamma j.succ) := by
  simp only [coefficientMatrix,actual_coframe,homogeneousInverseGamma lapse lapse_pos.ne',
    Fin.succ_ne_zero,if_false,one_smul]

/-- The same physical coframe turns an actual Lorentz connection perturbation into its full exterior-matter Hamiltonian. -/
theorem sourceSpinConnectionHamiltonian_original (A : Fin 4→DiracMatrix) :
    (-Complex.I) • (Ring.inverse (principalMatrix (actual.coframe 0))*
      (∑mu : Fin 4,coefficientMatrix mu (actual.coframe 0)*spinCoordinates (A mu)))=
      spinCoordinates ((-Complex.I) • A 0+
        (Complex.I*(lapse:ℂ)) • (∑j : Fin 3,diracGammaZero*diracGamma j.succ*A j.succ)) := by
  rw [Fin.sum_univ_succ,mul_add,←principalMatrix_coefficient,←mul_assoc,
    Ring.inverse_mul_cancel _ (principalMatrix_regular _ (actual_noncharacteristic 0)),one_mul,
    smul_add,map_add,map_smul]
  congr 1
  rw [sourcePrincipalInverse_actual,map_smul,map_sum]
  simp only [Finset.mul_sum,Finset.smul_sum,sourceSpatialCoefficient_actual,
    mul_smul_comm,smul_mul_assoc,smul_smul,spinCoordinates_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [←mul_assoc,neg_mul,Complex.I_mul_I]
  ring
  all_goals simp only [mul_assoc]

end LowEnergy.PreparationPhysicalNormalizedFullField
