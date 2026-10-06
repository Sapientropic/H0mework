import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalVelocityPrimary

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeLegendreSource
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineBlockwiseConstitutive StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineTopologicalFourFormPairing
open PreparationVacuumGravityLegendreSource PreparationVacuumNativeFullGravityReturn
open PreparationVacuumJointFieldResponse SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert SourceQuantumConfigurationHilbert
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def sourceGaussCoframe (z : SourceCoordinateSlice) : LorentzianCoframe:=
  GaussNativeEnergy.coframe GaussNativeEnergy.sourceTime z.1

def sourceTriadVelocity (v : Coframe) : LorentzianCoframe:=GaussNativeEnergy.coframe (fun _=>0) v

theorem sourceTriadVelocity_original (q v : Coframe) (r : ℝ) :
    GaussNativeEnergy.coframe GaussNativeEnergy.sourceTime (q+r • v)=
      GaussNativeEnergy.coframe GaussNativeEnergy.sourceTime q+r • sourceTriadVelocity v:=by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GaussNativeEnergy.coframe,sourceTriadVelocity]

theorem sourceTriadVelocity_fullBasis (v : Coframe) :
    sourceTriadVelocity v=∑i : Fin 6,v i • sourceTriadVelocity (EuclideanSpace.single i 1):=by
  ext a mu
  fin_cases a <;> fin_cases mu <;>
    simp [sourceTriadVelocity,GaussNativeEnergy.coframe,Matrix.sum_apply,Matrix.smul_apply,Fin.sum_univ_six]

def sourceGaussVelocityMatrix (z : SourceCoordinateSlice) : Matrix LorentzIndex (Fin 6) ℝ:=fun i j=>
  sourceCoframeVelocityLoad (sourceGaussCoframe z) (sourceTriadVelocity (EuclideanSpace.single j 1)) i

theorem sourceGaussVelocityMatrix_generated (z : SourceCoordinateSlice) (v : Coframe) :
    sourceCoframeVelocityLoad (sourceGaussCoframe z) (sourceTriadVelocity v)=(sourceGaussVelocityMatrix z).mulVec (fun i=>v i):=by
  have actual:=congrArg (sourceCoframeVelocityLinear (sourceGaussCoframe z)) (sourceTriadVelocity_fullBasis v)
  simp only [map_sum,map_smul,smul_eq_mul] at actual
  funext i
  have component:=congrFun actual i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at component
  change sourceCoframeVelocityLoad (sourceGaussCoframe z) (sourceTriadVelocity v) i=
    ∑j : Fin 6,v j*sourceCoframeVelocityLoad (sourceGaussCoframe z) (sourceTriadVelocity (EuclideanSpace.single j 1)) i at component
  change sourceCoframeVelocityLoad (sourceGaussCoframe z) (sourceTriadVelocity v) i=
    ∑j : Fin 6,sourceCoframeVelocityLoad (sourceGaussCoframe z) (sourceTriadVelocity (EuclideanSpace.single j 1)) i*v j
  rw [component]
  apply Finset.sum_congr rfl
  intro j _
  ring

private def sourceGaussGammaCoefficients (q : Coframe) : Matrix LorentzIndex (Fin 6) ℝ:=fun i j=>
  ![![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]], ![![0, 0, -1*q 5, 0, 0, -1*q 2], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]], ![![0, q 5, 0, 0, 0, q 1], ![-1*q 5, 0, 0, 0, 0, -1*q 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]], ![![0, -1*q 4, q 3, q 2, -1*q 1, 0], ![q 4, 0, 0, 0, q 0, 0], ![-1*q 2, 0, -1*q 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]] i.1 i.2 j

theorem sourceGaussVelocityLoad_coefficients (z : SourceCoordinateSlice) (v : Coframe) :
    sourceCoframeVelocityLoad (sourceGaussCoframe z) (sourceTriadVelocity v)=
      (sourceGaussGammaCoefficients z.1).mulVec (fun j=>v j):=by
  funext i
  rcases i with ⟨mu,a⟩
  fin_cases mu <;> fin_cases a <;>
    simp only [sourceCoframeVelocityLoad,sourceGaussCoframe,sourceTriadVelocity,
      GaussNativeEnergy.coframe,sourceGaussGammaCoefficients,sourceBFBoundaryFirst,sourceBFBoundary,
      sourceConnectionBasis,wedgeFirst,gravityInternalDualEquiv,gravityInternalDualLinear,
      internalBivectorDual,lorentzianCoframeHodge,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,PiLp.single_apply,
      Fin.sum_univ_six,minkowskiInternalSign,lorentzianTwoFormSign,pairFirst,pairSecond,twoFormComplement,
      Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.cons_val_fin_one,Fin.isValue,Fin.ext_iff,Fin.val_zero,Fin.val_one,Fin.val_mk,Fin.val_ofNat,Fin.val_natCast,Fin.reduceEq,
      Prod.mk.injEq,reduceIte,eq_self,and_false,false_and,and_true,true_and,
      Pi.zero_apply,ite_self,sub_self,mul_zero,zero_mul,mul_one,one_mul,add_zero,zero_add,
      neg_zero,zero_sub,sub_zero,neg_one_mul,neg_neg]
  all_goals norm_num only [Matrix.of_apply,Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.cons_val_fin_one,Fin.val_ofNat,Fin.val_natCast]
  all_goals norm_num [Fin.val_ofNat,Fin.val_natCast]
  all_goals simp only [Matrix.mulVec,dotProduct,sourceGaussGammaCoefficients,Fin.sum_univ_six,
    Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,mul_zero,zero_mul,mul_one,one_mul,add_zero,zero_add]
  all_goals ring

attribute [local irreducible] sourceGaussGammaCoefficients sourceGaussVelocityMatrix sourceLorentzInverseNumerator sourceGaussCoframe

theorem sourceGaussVelocityMatrix_coefficients (z : SourceCoordinateSlice) :
    sourceGaussVelocityMatrix z=sourceGaussGammaCoefficients z.1:=by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have original:=sourceGaussVelocityMatrix_generated z (WithLp.toLp 2 v)
  have produced:=sourceGaussVelocityLoad_coefficients z (WithLp.toLp 2 v)
  exact original.symm.trans produced

def sourceGaussVelocityHessian (z : SourceCoordinateSlice) : Matrix (Fin 6) (Fin 6) ℝ:=
  -(sourceGaussVelocityMatrix z).transpose*sourceLorentzInverse (sourceGaussCoframe z)*sourceGaussVelocityMatrix z

def sourceGaussVelocityNumerator (z : SourceCoordinateSlice) : Matrix (Fin 6) (Fin 6) ℝ:=
  -(sourceGaussVelocityMatrix z).transpose*sourceLorentzInverseNumerator (sourceGaussCoframe z)*sourceGaussVelocityMatrix z

private def sourceGaussVelocityPolynomial (q : Coframe) : Matrix (Fin 6) (Fin 6) ℝ:=
  !![0, 0, q 0*q 2*q 5^2, 0, 0, q 0*q 2^2*q 5;
    0, (-1/2:ℝ)*q 2^2*q 5^2, (1/2:ℝ)*q 1*q 2*q 5^2, 0, 0, 0;
    q 0*q 2*q 5^2, (1/2:ℝ)*q 1*q 2*q 5^2, (-1/2:ℝ)*q 1^2*q 5^2, 0, 0, q 0^2*q 2*q 5;
    0, 0, 0, (-1/2:ℝ)*q 2^2*q 5^2, (1/2:ℝ)*q 1*q 2*q 5^2, (1/2:ℝ)*q 2^2*q 3*q 5+(-1/2:ℝ)*q 1*q 2*q 4*q 5;
    0, 0, 0, (1/2:ℝ)*q 1*q 2*q 5^2, (-1/2:ℝ)*q 1^2*q 5^2+(-1/2:ℝ)*q 0^2*q 5^2, (-1/2:ℝ)*q 1*q 2*q 3*q 5+(1/2:ℝ)*q 1^2*q 4*q 5+(1/2:ℝ)*q 0^2*q 4*q 5;
    q 0*q 2^2*q 5, 0, q 0^2*q 2*q 5, (1/2:ℝ)*q 2^2*q 3*q 5+(-1/2:ℝ)*q 1*q 2*q 4*q 5, (-1/2:ℝ)*q 1*q 2*q 3*q 5+(1/2:ℝ)*q 1^2*q 4*q 5+(1/2:ℝ)*q 0^2*q 4*q 5, (-1/2:ℝ)*q 2^2*q 3^2+q 1*q 2*q 3*q 4+(-1/2:ℝ)*q 1^2*q 4^2+(-1/2:ℝ)*q 0^2*q 4^2]

theorem sourceGaussVelocityNumerator_coefficients (z : SourceCoordinateSlice) :
    sourceGaussVelocityNumerator z=sourceGaussVelocityPolynomial z.1:=by
  rw [sourceGaussVelocityNumerator,sourceGaussVelocityMatrix_coefficients]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.neg_apply,Fintype.sum_prod_type,
      Fin.sum_univ_four,Fin.sum_univ_six]
  all_goals simp only [sourceGaussGammaCoefficients,Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.isValue,mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul]
  all_goals simp only [sourceLorentzInverseNumerator,sourceFlatLorentzInverse,sourceGaussCoframe,
    GaussNativeEnergy.coframe,GaussNativeEnergy.source_time_generated,Fin.sum_univ_four,
    Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.isValue,
    mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul]
  all_goals norm_num [sourceGaussVelocityPolynomial,Matrix.cons_val_succ,Matrix.cons_val_succ',Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  all_goals ring_nf
  all_goals simp only [true_or]

theorem sourceGaussVelocityHessian_numerator (z : SourceCoordinateSlice) :
    sourceGaussVelocityHessian z=(sourceGaussCoframe z).det⁻¹ • sourceGaussVelocityNumerator z:=by
  simp only [sourceGaussVelocityHessian,sourceLorentzInverse,sourceGaussVelocityNumerator,
    Matrix.mul_smul,Matrix.smul_mul]

theorem sourceGaussVelocityPolynomial_inverse (q : Coframe) :
    sourceGaussVelocityPolynomial q*GaussCoframeKinetic.polynomial q=
      (2*(q 0*q 2*q 5)^2) • (1 : Matrix (Fin 6) (Fin 6) ℝ):=by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGaussVelocityPolynomial,GaussCoframeKinetic.polynomial,Matrix.mul_apply,Fin.sum_univ_six] <;> ring

def sourceGaussVelocityInverse (z : SourceCoordinateSlice) : Matrix (Fin 6) (Fin 6) ℝ:=
  (2:ℝ) • (fun i j=>GaussCoframeKinetic.coefficient i j z)

theorem sourceGaussCoframe_determinant (z : SourceCoordinateSlice) :
    (sourceGaussCoframe z).det=GaussNativeEnergy.sourceTime 0*GaussNativeEnergy.volume z:=by
  rw [sourceGaussCoframe,GaussNativeEnergy.coframe_determinant]
  rfl

theorem sourceGaussCoframe_nondegenerate (z : physicalChart) : (sourceGaussCoframe z.val).det≠0:=by
  rw [sourceGaussCoframe_determinant]
  apply mul_ne_zero
  · rw [GaussNativeEnergy.source_time_generated]
    exact Stage9C.Material.SpinPair.lapse_pos.ne'
  · exact (GaussNativeEnergy.volume_pos z).ne'

theorem sourceGaussVelocityInverse_right (z : physicalChart) :
    sourceGaussVelocityHessian z.val*sourceGaussVelocityInverse z.val=1:=by
  have t : GaussNativeEnergy.sourceTime 0≠0:=by
    rw [GaussNativeEnergy.source_time_generated]
    exact Stage9C.Material.SpinPair.lapse_pos.ne'
  have volume : GaussNativeEnergy.volume z.val≠0:=(GaussNativeEnergy.volume_pos z).ne'
  have original : sourceGaussVelocityInverse z.val=
      (GaussNativeEnergy.sourceTime 0/(2*GaussNativeEnergy.volume z.val)) • GaussCoframeKinetic.polynomial z.val.1:=by
    ext i j
    simp only [sourceGaussVelocityInverse,GaussCoframeKinetic.coefficient,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [sourceGaussVelocityHessian_numerator,sourceGaussVelocityNumerator_coefficients,original,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,sourceGaussVelocityPolynomial_inverse]
  rw [sourceGaussCoframe_determinant,smul_smul]
  change (((GaussNativeEnergy.sourceTime 0*GaussNativeEnergy.volume z.val)⁻¹*
    (GaussNativeEnergy.sourceTime 0/(2*GaussNativeEnergy.volume z.val)))*(2*GaussNativeEnergy.volume z.val^2)) •
      (1 : Matrix (Fin 6) (Fin 6) ℝ)=1
  have coefficient : (GaussNativeEnergy.sourceTime 0*GaussNativeEnergy.volume z.val)⁻¹*
      (GaussNativeEnergy.sourceTime 0/(2*GaussNativeEnergy.volume z.val))*(2*GaussNativeEnergy.volume z.val^2)=1:=by
    field_simp
  rw [coefficient,one_smul]

theorem sourceGaussVelocityInverse_left (z : physicalChart) :
    sourceGaussVelocityInverse z.val*sourceGaussVelocityHessian z.val=1:=
  mul_eq_one_comm.mp (sourceGaussVelocityInverse_right z)

def sourceGaussKineticHamiltonian (z : SourceCoordinateSlice) (p : Fin 6→ℝ) : ℝ:=
  (1/2:ℝ)*(∑i : Fin 6,∑j : Fin 6,p i*sourceGaussVelocityInverse z i j*p j)

theorem sourceGaussKineticHamiltonian_original (z : SourceCoordinateSlice) (p : Fin 6→ℝ) :
    sourceGaussKineticHamiltonian z p=∑i : Fin 6,∑j : Fin 6,GaussCoframeKinetic.coefficient i j z*p i*p j:=by
  simp only [sourceGaussKineticHamiltonian,sourceGaussVelocityInverse,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def sourceGaussVelocityAction (u : JointParameter) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) (v : Coframe) : ℝ:=
  sourceCoframeVelocityAction u (sourceGaussCoframe z) de (sourceTriadVelocity v)

def sourceGaussMomentumShift (u : JointParameter) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) : Fin 6→ℝ:=
  (-(sourceGaussVelocityMatrix z).transpose*sourceLorentzInverse (sourceGaussCoframe z)).mulVec
    (sourceLorentzOriginalLoad u (sourceGaussCoframe z) de)

def sourceGaussActionConstant (u : JointParameter) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) : ℝ:=
  -(1/2:ℝ)*dotProduct (sourceLorentzOriginalLoad u (sourceGaussCoframe z) de)
    ((sourceLorentzInverse (sourceGaussCoframe z)).mulVec (sourceLorentzOriginalLoad u (sourceGaussCoframe z) de))-
      3*(sourceGaussCoframe z).det

theorem sourceGaussVelocityAction_expansion (u : JointParameter) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) (v : Coframe) :
    sourceGaussVelocityAction u z.val de v=
      (1/2:ℝ)*dotProduct (fun i=>v i) ((sourceGaussVelocityHessian z.val).mulVec (fun i=>v i))+
        dotProduct (fun i=>v i) (sourceGaussMomentumShift u z.val de)+sourceGaussActionConstant u z.val de:=by
  let G:=sourceGaussVelocityMatrix z.val
  let K:=sourceLorentzInverse (sourceGaussCoframe z.val)
  let J:=sourceLorentzOriginalLoad u (sourceGaussCoframe z.val) de
  let V : Fin 6→ℝ:=fun i=>v i
  let W:=G.mulVec V
  have symmetric : J ⬝ᵥ K.mulVec W=W ⬝ᵥ K.mulVec J:=by
    have actual:=Matrix.dotProduct_transpose_mulVec K J W
    rw [sourceLorentzInverse_symmetric (sourceGaussCoframe z.val) (sourceGaussCoframe_nondegenerate z)] at actual
    exact actual
  have kinetic : V ⬝ᵥ (sourceGaussVelocityHessian z.val).mulVec V=-(W ⬝ᵥ K.mulVec W):=by
    simp only [sourceGaussVelocityHessian,Matrix.neg_mul,Matrix.neg_mulVec,dotProduct_neg]
    change -(V ⬝ᵥ (G.transpose*K*G).mulVec V)=-(W ⬝ᵥ K.mulVec W)
    rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  have shift : V ⬝ᵥ sourceGaussMomentumShift u z.val de=-(W ⬝ᵥ K.mulVec J):=by
    simp only [sourceGaussMomentumShift,Matrix.neg_mul,Matrix.neg_mulVec,dotProduct_neg]
    change -(V ⬝ᵥ (G.transpose*K).mulVec J)=-(W ⬝ᵥ K.mulVec J)
    rw [←Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  rw [sourceGaussVelocityAction,sourceCoframeVelocityAction,
    sourceLorentzEliminatedAction_original u (sourceGaussCoframe z.val) (sourceGaussCoframe_nondegenerate z),
    sourceTemporalLoad_add,sourceGaussVelocityMatrix_generated]
  change -(1/2:ℝ)*((J+W) ⬝ᵥ K.mulVec (J+W))-3*(sourceGaussCoframe z.val).det=
    (1/2:ℝ)*(V ⬝ᵥ (sourceGaussVelocityHessian z.val).mulVec V)+
      V ⬝ᵥ sourceGaussMomentumShift u z.val de+
        (-(1/2:ℝ)*(J ⬝ᵥ K.mulVec J)-3*(sourceGaussCoframe z.val).det)
  rw [Matrix.mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add,symmetric,kinetic,shift]
  ring

def sourceGaussResolvedVelocity (u : JointParameter) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) (p : Fin 6→ℝ) : Coframe:=
  WithLp.toLp 2 ((sourceGaussVelocityInverse z).mulVec (p-sourceGaussMomentumShift u z de))

theorem sourceGaussResolvedVelocity_equation (u : JointParameter) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) (p : Fin 6→ℝ) :
    (sourceGaussVelocityHessian z.val).mulVec (fun i=>sourceGaussResolvedVelocity u z.val de p i)+
      sourceGaussMomentumShift u z.val de=p:=by
  change (sourceGaussVelocityHessian z.val).mulVec
    ((sourceGaussVelocityInverse z.val).mulVec (p-sourceGaussMomentumShift u z.val de))+
      sourceGaussMomentumShift u z.val de=p
  rw [Matrix.mulVec_mulVec,sourceGaussVelocityInverse_right z,Matrix.one_mulVec]
  abel

theorem sourceGaussOriginalLegendre (u : JointParameter) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) (p : Fin 6→ℝ) :
    dotProduct p (fun i=>sourceGaussResolvedVelocity u z.val de p i)-
      sourceGaussVelocityAction u z.val de (sourceGaussResolvedVelocity u z.val de p)=
        sourceGaussKineticHamiltonian z.val (p-sourceGaussMomentumShift u z.val de)-
          sourceGaussActionConstant u z.val de:=by
  let v:=sourceGaussResolvedVelocity u z.val de p
  have actual:=sourceGaussResolvedVelocity_equation u z de p
  have equation : (sourceGaussVelocityHessian z.val).mulVec (fun i=>v i)=
      p-sourceGaussMomentumShift u z.val de:=by
    have rearranged:=congrArg (fun x=>x-sourceGaussMomentumShift u z.val de) actual
    simpa only [add_sub_cancel_right] using rearranged
  have total : p=(sourceGaussVelocityHessian z.val).mulVec (fun i=>v i)+sourceGaussMomentumShift u z.val de:=actual.symm
  have current : (fun i=>v i)=(sourceGaussVelocityInverse z.val).mulVec (p-sourceGaussMomentumShift u z.val de):=rfl
  let P:=p-sourceGaussMomentumShift u z.val de
  let V : Fin 6→ℝ:=fun i=>v i
  have kinetic : sourceGaussKineticHamiltonian z.val P=(1/2:ℝ)*(V ⬝ᵥ P):=by
    have read : sourceGaussKineticHamiltonian z.val P=
        (1/2:ℝ)*(P ⬝ᵥ (sourceGaussVelocityInverse z.val).mulVec P):=by
      simp only [sourceGaussKineticHamiltonian,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
    rw [read,←current,dotProduct_comm]
  have pairing : p ⬝ᵥ V=V ⬝ᵥ P+V ⬝ᵥ sourceGaussMomentumShift u z.val de:=by
    rw [total,add_dotProduct]
    rw [dotProduct_comm ((sourceGaussVelocityHessian z.val).mulVec V) V,equation,
      dotProduct_comm (sourceGaussMomentumShift u z.val de) V]
  rw [sourceGaussVelocityAction_expansion u z de v]
  change p ⬝ᵥ V-((1/2:ℝ)*(V ⬝ᵥ (sourceGaussVelocityHessian z.val).mulVec V)+
      V ⬝ᵥ sourceGaussMomentumShift u z.val de+sourceGaussActionConstant u z.val de)=
    sourceGaussKineticHamiltonian z.val P-sourceGaussActionConstant u z.val de
  rw [pairing,equation,kinetic]
  ring

end LowEnergy.PreparationVacuumCoframeLegendreSource
