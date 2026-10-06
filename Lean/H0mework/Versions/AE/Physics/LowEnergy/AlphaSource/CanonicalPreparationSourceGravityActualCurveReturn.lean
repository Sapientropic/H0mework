import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceBFJets

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeFullGravityReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineLorentzConnectionVariation StageNineCoframeVariation EmpiricalReferenceScaleCouplingBoundary
open PreparationVacuumNativeSourceRestriction PreparationVacuumNativeLocalWard
open PreparationVacuumNativeFieldInjection PreparationVacuumLorentzFieldInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumSourceFieldFamily PreparationVacuumGaugeSourceInjection
open Filter Set
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def nativeGravityCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (r : ℝ) : StageNineHolonomicConfiguration:=
  configurationRay (primitiveFamily u) (nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u) r

private theorem nativeConnection_lift (a : Fin 6) (theta : ℝ) (u : JointParameter) (x : BasePoint) :
    lorentzSkewConnectionOfBivectorOneForm (nativeLorentzFamilyDirection a (fun _=>theta) u x)=
      (nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).gravityConnection x :=by
  simp only [nativePrimitiveFamily,Fin.addCases_right,lorentzPrimitiveDirection,nativeLorentzFamilyDirection,
    fieldDirectionalDerivative,fderiv_const,zero_apply]
  congr 2
  funext mu
  simp [fieldDirectionalDerivative]

private theorem nativeGravityCurve_connectionDerivative (a : Fin 6) (theta : ℝ) (u : JointParameter) (r : ℝ)
    (mu nu i j : Fin 4) : gravityConnectionDerivative (nativeGravityCurve a theta u r) 0 mu nu i j=0 :=by
  simp [gravityConnectionDerivative,nativeGravityCurve,configurationRay,primitiveFamily,configurationFromFields,
    nativePrimitiveFamily,Fin.addCases_right,lorentzPrimitiveDirection]

private theorem nativeField_connectionDerivative (a : Fin 6) (theta : ℝ) (u : JointParameter)
    (mu nu i j : Fin 4) :
    lorentzConnectionVariationDerivative (nativeLorentzFamilyDirection a (fun _=>theta) u) 0 mu nu i j=0 :=by
  have constant : nativeLorentzFamilyDirection a (fun _=>theta) u=
      fun _=>connectionBivectorDirection a theta 0 (ambientPrimitiveData u).2.2.2:=by
    funext x mu
    simp [nativeLorentzFamilyDirection,connectionBivectorDirection,fieldDirectionalDerivative]
  rw [constant]
  simp [lorentzConnectionVariationDerivative,fieldDirectionalDerivative]

private theorem primitiveConnectionDerivative (u : JointParameter) (mu nu i j : Fin 4) :
    gravityConnectionDerivative (primitiveFamily u) 0 mu nu i j=0 :=by
  change fderiv ℝ (fun _x : BasePoint=>(primitiveFamily u).gravityConnection 0 nu i j) 0 (coordinateDirection mu)=0
  simp

/-- The original curve keeps its quadratic curvature; its tangent is not substituted for the whole path. -/
theorem nativeGravityCurve_curvature (a : Fin 6) (theta : ℝ) (u : JointParameter) (r : ℝ) :
    holonomicGravityCurvature (nativeGravityCurve a theta u r) 0=
      holonomicGravityCurvature (primitiveFamily u) 0+
        r • lorentzConnectionLinearCurvatureVariation (primitiveFamily u)
          (nativeLorentzFamilyDirection a (fun _=>theta) u) 0+
        r^2 • lorentzConnectionQuadraticCurvatureVariation (nativeLorentzFamilyDirection a (fun _=>theta) u) 0 :=by
  funext i p
  simp only [holonomicGravityCurvature,nativeGravityCurve_connectionDerivative,primitiveConnectionDerivative,
    lorentzConnectionLinearCurvatureVariation,lorentzConnectionQuadraticCurvatureVariation,nativeField_connectionDerivative,
    nativeConnection_lift,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    zero_sub,sub_zero]
  simp only [nativeGravityCurve,configurationRay,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,add_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul,Fin.sum_univ_four]
  ring

def actualBFStateCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (r : ℝ) : BFState:=
  ((nativeGravityCurve a theta u r).coframe 0,(nativeGravityCurve a theta u r).gravityAuxiliary 0,
    holonomicGravityCurvature (nativeGravityCurve a theta u r) 0)

theorem actualBFStateCurve_first (a : Fin 6) (theta : ℝ) (u : JointParameter) :
    HasDerivAt (actualBFStateCurve a theta u) (nativeBFDirection a theta u) 0 :=by
  have line (s d : PhysicalBivector) : HasDerivAt (fun r : ℝ=>s+r • d) d 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add s using 1
    simp
  have curvature:=((line (holonomicGravityCurvature (primitiveFamily u) 0)
    (lorentzConnectionLinearCurvatureVariation (primitiveFamily u) (nativeLorentzFamilyDirection a (fun _=>theta) u) 0)).add
      ((hasDerivAt_id (0:ℝ)).pow 2 |>.smul_const
        (lorentzConnectionQuadraticCurvatureVariation (nativeLorentzFamilyDirection a (fun _=>theta) u) 0)))
  have e : HasDerivAt (fun r : ℝ=>(nativeGravityCurve a theta u r).coframe 0)
      ((nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).coframe 0) (0:ℝ):=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const
      ((nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).coframe 0)).const_add ((primitiveFamily u).coframe 0) using 1
    simp
  have B:=line ((primitiveFamily u).gravityAuxiliary 0) ((nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).gravityAuxiliary 0)
  convert! e.prodMk (B.prodMk curvature) using 1
  · funext r
    unfold actualBFStateCurve
    rw [nativeGravityCurve_curvature]
    simp only [nativeGravityCurve,configurationRay,Pi.add_apply,Pi.pow_apply,id_eq]
  · simp only [nativeBFDirection,id_eq,Nat.reduceSub,pow_one,zero_mul,mul_zero,zero_smul,add_zero]

theorem nativeSimplicity_originalCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) :
    HasDerivAt (fun r : ℝ=>generatedGravitySimplicityDensity
      (toContinuumPointField (nativeGravityCurve a theta u r) 0)) (nativeSimplicityTorque a theta u) 0 :=by
  have source:=nativeSimplicityTorque_generated a theta u
  convert! source using 1
  funext r
  rw [nativeGravityDirection_original]
  simp only [generatedGravitySimplicityDensity,generatedGravitySimplicityResidual,gravityPoint,nativeGravityCurve,
    configurationRay,toContinuumPointField,originalGravityState,nativeGravityDirection_original,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd]

private theorem framed_field_smooth (B : BFState→PhysicalBivector) (smooth : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun s : BFState=>framed s.1 (B s)) :=by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro p
  change ContDiff ℝ ∞ (fun s : BFState=>∑j : Fin 6,coframeWedge s.1 p j*B s i j)
  apply ContDiff.sum
  intro j _
  have value :=(contDiff_pi.mp (contDiff_pi.mp smooth i) j)
  apply ContDiff.mul _ value
  simp only [coframeWedge]
  fun_prop

private theorem bfPolynomial_smooth : ContDiff ℝ ∞ bfPolynomial :=by
  have B:ContDiff ℝ ∞ (fun s : BFState=>framed s.1 s.2.1):=
    framed_field_smooth _ (by fun_prop)
  have R:ContDiff ℝ ∞ (fun s : BFState=>framed s.1 s.2.2):=
    framed_field_smooth _ (by fun_prop)
  have dual:ContDiff ℝ ∞ (fun s : BFState=>framed s.1 (internalBivectorDual s.2.1)):=by
    apply framed_field_smooth
    have columns (p : Fin 6) : ContDiff ℝ ∞ (fun s : BFState=>fun i : Fin 6=>s.2.1 i p):=by
      fun_prop
    have each (p : Fin 6) : ContDiff ℝ ∞ (fun s : BFState=>lorentzianCoframeHodge (fun i=>s.2.1 i p)):=
      lorentzianCoframeHodge.toContinuousLinearMap.contDiff.comp (columns p)
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro p
    exact contDiff_pi.mp (each p) i

  unfold bfPolynomial constitutivePair signedPairing
  apply ContDiff.sub
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro p _
    apply ContDiff.mul
    · exact contDiff_const.mul ((contDiff_pi.mp (contDiff_pi.mp B i) p))
    · change ContDiff ℝ ∞ (fun s : BFState=>lorentzianCoframeHodge (framed s.1 s.2.2 i) p)
      exact (contDiff_pi.mp ((lorentzianCoframeHodge.toContinuousLinearMap).contDiff.comp (contDiff_pi.mp R i)) p)
  · apply contDiff_const.mul
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro p _
    apply ContDiff.mul
    · exact contDiff_const.mul ((contDiff_pi.mp (contDiff_pi.mp B i) p))
    · change ContDiff ℝ ∞ (fun s : BFState=>lorentzianCoframeHodge (framed s.1 (internalBivectorDual s.2.1) i) p)
      exact (contDiff_pi.mp ((lorentzianCoframeHodge.toContinuousLinearMap).contDiff.comp (contDiff_pi.mp dual i)) p)

private theorem bfPolynomial_fderiv (s d : BFState) : fderiv ℝ bfPolynomial s d=bfFirst s d :=by
  have line : HasDerivAt (fun r : ℝ=>s+r • d) d 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add s using 1
    simp
  have generated:=((bfPolynomial_smooth.differentiable (by simp)).differentiableAt (x:=s)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 line (by simp)
  exact generated.unique (bfFirst_polynomial_generated s d)

theorem nativeBF_originalCurve (a : Fin 6) (theta : ℝ) (u : JointParameter)
    (nondegenerate : ((primitiveFamily u).coframe 0).det≠0) :
    HasDerivAt (fun r : ℝ=>generatedGravityBFDensity
      (toContinuumPointField (nativeGravityCurve a theta u r) 0)) (nativeBFTorque a theta u) 0 :=by
  have initial : actualBFStateCurve a theta u 0=originalBFState u:=by
    simp only [actualBFStateCurve,nativeGravityCurve,configurationRay,zero_smul,add_zero]
    rfl
  have generated:=((bfPolynomial_smooth.differentiable (by simp)).differentiableAt (x:=originalBFState u)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (actualBFStateCurve_first a theta u) initial.symm
  rw [bfPolynomial_fderiv] at generated
  have regular : ∀ᶠ r : ℝ in 𝓝 0,((actualBFStateCurve a theta u r).1).det≠0:=by
    have continuous :=coframe_det_contDiff.continuous.continuousAt.comp
      ((actualBFStateCurve_first a theta u).continuousAt.fst)
    exact continuous.eventually (isOpen_compl_singleton.mem_nhds (by simpa only [Function.comp_apply,initial,originalBFState,Set.mem_compl_iff,Set.mem_singleton_iff] using nondegenerate))
  have same : (fun r : ℝ=>generatedGravityBFDensity (toContinuumPointField (nativeGravityCurve a theta u r) 0))=ᶠ[𝓝 0]
      (fun r : ℝ=>bfPolynomial (actualBFStateCurve a theta u r)):=by
    filter_upwards [regular] with r hr
    exact (bfPolynomial_original u (actualBFStateCurve a theta u r) hr).symm
  exact generated.congr_of_eventuallyEq same

private theorem bfFirst_joint_smooth : ContDiff ℝ ∞ (fun u : BFState×BFState=>bfFirst u.1 u.2) :=by
  have slope : ContDiff ℝ ∞ (fun u : BFState×BFState=>fderiv ℝ bfPolynomial u.1 u.2):=
    ((bfPolynomial_smooth.fderiv_right (m:=∞) (by simp)).comp contDiff_fst).clm_apply contDiff_snd
  simpa only [bfPolynomial_fderiv] using slope

private theorem bfFirst_joint_fderiv (s d h c : BFState) :
    fderiv ℝ (fun u : BFState×BFState=>bfFirst u.1 u.2) (s,d) (h,c)=bfMixed s d h c :=by
  have line : HasDerivAt (fun r : ℝ=>(s,d)+r • (h,c)) (h,c) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const (h,c)).const_add (s,d) using 1
    simp
  have generated:=((bfFirst_joint_smooth.differentiable (by simp)).differentiableAt (x:=(s,d))).hasFDerivAt.comp_hasDerivAt_of_eq
    0 line (by simp)
  exact generated.unique (bfMixed_generated s d h c)

/-- Literal gravity slots act on the original configuration; its matter and independent dual stay on the same source. -/
def gravityConfigurationForce (force : Field289) : StageNineHolonomicConfiguration where
  coframe _:=fieldCoframe force
  gravityConnection _:=lorentzSkewConnectionOfBivectorOneForm (fieldLorentz force)
  gravityAuxiliary _:=fieldGravityB force
  gravitySimplicityMultiplier _:=fieldMultiplier force
  gaugeConnection:=0
  gaugeAuxiliary:=0
  scalar:=0
  matter:=0
  conjugateMatter:=0

def fieldGravityCurve (u : JointParameter) (force : Field289) (r : ℝ) : StageNineHolonomicConfiguration:=
  configurationRay (primitiveFamily u) (gravityConfigurationForce force) r

def fieldNativeGravityDirection (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) (r : ℝ) :
    StageNineHolonomicConfiguration:=
  lorentzPrimitiveDirection a (fun _=>theta) 0 (fieldGravityCurve u force r)
    (fun _=>ambientPrimitiveData u+r • sourceData force)

def fieldNativeBFCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) (r : ℝ) : BFState×BFState:=
  (((fieldGravityCurve u force r).coframe 0,(fieldGravityCurve u force r).gravityAuxiliary 0,
      holonomicGravityCurvature (fieldGravityCurve u force r) 0),
    ((fieldNativeGravityDirection a theta u force r).coframe 0,
      (fieldNativeGravityDirection a theta u force r).gravityAuxiliary 0,
        lorentzConnectionLinearCurvatureVariation (fieldGravityCurve u force r)
          (fun _=>connectionBivectorDirection a theta 0 ((ambientPrimitiveData u+r • sourceData force).2.2.2)) 0))

def originalBFForce (u : JointParameter) (force : Field289) : BFState:=
  (fieldCoframe force,fieldGravityB force,
    lorentzConnectionLinearCurvatureVariation (primitiveFamily u) (fun _=>fieldLorentz force) 0)

def originalBFContact (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) : BFState:=
  ((theta • frameGenerator a)*fieldCoframe force,bivectorDirection a theta (fieldGravityB force),
    (lorentzConnectionQuadraticCurvatureVariation ((fun _=>fieldLorentz force)+nativeLorentzFamilyDirection a (fun _=>theta) u) 0-
      lorentzConnectionQuadraticCurvatureVariation (fun _=>fieldLorentz force) 0-
        lorentzConnectionQuadraticCurvatureVariation (nativeLorentzFamilyDirection a (fun _=>theta) u) 0)+
      lorentzConnectionLinearCurvatureVariation (primitiveFamily u)
        (fun _ mu=>theta • lorentzBracketCoordinates (Pi.single a 1) (fieldLorentz force mu)) 0)

private theorem nativeMatrixDirection (a : Fin 6) (theta : ℝ)
    (omega : LorentzBivectorOneForm) (mu : Fin 4) :
    lorentzSkewConnectionOfBivectorOneForm (connectionBivectorDirection a theta 0 omega) mu=
      theta • (frameGenerator a*(show LorentzianCoframe from lorentzSkewConnectionOfBivectorOneForm omega mu)-
        (show LorentzianCoframe from lorentzSkewConnectionOfBivectorOneForm omega mu)*frameGenerator a) :=by
  change lorentzMatrix (theta • lorentzBracketCoordinates (Pi.single a 1) (omega mu)-0 • Pi.single a 1)=_
  simp only [zero_smul,sub_zero]
  have scale : lorentzMatrix (theta • lorentzBracketCoordinates (Pi.single a 1) (omega mu))=
      theta • lorentzMatrix (lorentzBracketCoordinates (Pi.single a 1) (omega mu)):=by
    unfold lorentzMatrix
    rw [Pi.single_smul]
    exact congrArg (fun K : PointwiseLorentzSpinConnection=>K 0) (lorentzSkewConnectionOfBivectorOneForm_smul theta _)
  rw [scale,lorentzMatrix_lie]
  rfl

private theorem contactMatrixDirection (a : Fin 6) (theta : ℝ) (force : Field289) (mu : Fin 4) :
    lorentzSkewConnectionOfBivectorOneForm
      (fun nu=>theta • lorentzBracketCoordinates (Pi.single a 1) (fieldLorentz force nu)) mu=
        theta • (frameGenerator a*(show LorentzianCoframe from lorentzSkewConnectionOfBivectorOneForm (fieldLorentz force) mu)-
          (show LorentzianCoframe from lorentzSkewConnectionOfBivectorOneForm (fieldLorentz force) mu)*frameGenerator a) :=by
  have same : (fun nu=>theta • lorentzBracketCoordinates (Pi.single a 1) (fieldLorentz force nu))=
      connectionBivectorDirection a theta 0 (fieldLorentz force):=by
    funext nu
    simp only [connectionBivectorDirection,Pi.zero_apply,zero_smul,sub_zero]
  rw [same,nativeMatrixDirection]

private theorem fieldNativeConnection_affine (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289)
    (r : ℝ) (mu : Fin 4) :
    lorentzSkewConnectionOfBivectorOneForm
      (connectionBivectorDirection a theta 0 ((ambientPrimitiveData u+r • sourceData force).2.2.2)) mu=
        lorentzSkewConnectionOfBivectorOneForm (connectionBivectorDirection a theta 0 (ambientPrimitiveData u).2.2.2) mu+
          r • lorentzSkewConnectionOfBivectorOneForm
            (fun nu=>theta • lorentzBracketCoordinates (Pi.single a 1) (fieldLorentz force nu)) mu :=by
  rw [nativeMatrixDirection,nativeMatrixDirection,contactMatrixDirection]
  change theta • (frameGenerator a*(show LorentzianCoframe from lorentzSkewConnectionOfBivectorOneForm
    ((ambientPrimitiveData u).2.2.2+r • fieldLorentz force) mu)-
      (show LorentzianCoframe from lorentzSkewConnectionOfBivectorOneForm ((ambientPrimitiveData u).2.2.2+r • fieldLorentz force) mu)*frameGenerator a)=_
  rw [lorentzSkewConnectionOfBivectorOneForm_add,lorentzSkewConnectionOfBivectorOneForm_smul]
  simp only [Pi.add_apply,Pi.smul_apply,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_add,smul_sub]
  module

private theorem constantVariationDerivative (eta : LorentzBivectorOneForm) (mu nu i j : Fin 4) :
    lorentzConnectionVariationDerivative (fun _ : BasePoint=>eta) 0 mu nu i j=0 :=by
  simp [lorentzConnectionVariationDerivative,fieldDirectionalDerivative]

private theorem fieldGravityConnectionDerivative (u : JointParameter) (force : Field289) (r : ℝ) (mu nu i j : Fin 4) :
    gravityConnectionDerivative (fieldGravityCurve u force r) 0 mu nu i j=0 :=by
  simp [gravityConnectionDerivative,fieldGravityCurve,configurationRay,primitiveFamily,configurationFromFields,gravityConfigurationForce]

private theorem fieldNativeCurve_curvatureJet (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>lorentzConnectionLinearCurvatureVariation (fieldGravityCurve u force r)
      (fun _=>connectionBivectorDirection a theta 0 ((ambientPrimitiveData u+r • sourceData force).2.2.2)) 0)
      (originalBFContact a theta u force).2.2 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro p
  simp only [lorentzConnectionLinearCurvatureVariation,constantVariationDerivative]
  have connection (nu k l : Fin 4) : HasDerivAt (fun r : ℝ=>(fieldGravityCurve u force r).gravityConnection 0 nu k l)
      ((gravityConfigurationForce force).gravityConnection 0 nu k l) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const ((gravityConfigurationForce force).gravityConnection 0 nu k l)).const_add
      ((primitiveFamily u).gravityConnection 0 nu k l) using 1
    simp only [fieldGravityCurve,configurationRay,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_one,one_mul]
  have native (nu k l : Fin 4) : HasDerivAt (fun r : ℝ=>lorentzSkewConnectionOfBivectorOneForm
      (connectionBivectorDirection a theta 0 ((ambientPrimitiveData u+r • sourceData force).2.2.2)) nu k l)
      (lorentzSkewConnectionOfBivectorOneForm
        (fun mu=>theta • lorentzBracketCoordinates (Pi.single a 1) (fieldLorentz force mu)) nu k l) 0:=by
    have same:=fun r : ℝ=>fieldNativeConnection_affine a theta u force r nu
    simp only [same,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    convert! ((hasDerivAt_id (0:ℝ)).mul_const _).const_add _ using 1
    simp
  have each (j : Fin 4) :=
    (((native (pairFirst p) (pairFirst i) j).mul (connection (pairSecond p) j (pairSecond i))).add
      ((connection (pairFirst p) (pairFirst i) j).mul (native (pairSecond p) j (pairSecond i)))).sub
        (((native (pairSecond p) (pairFirst i) j).mul (connection (pairFirst p) j (pairSecond i))).add
          ((connection (pairSecond p) (pairFirst i) j).mul (native (pairFirst p) j (pairSecond i))))
  have generated:=(HasDerivAt.fun_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 4)))=>each j)).const_mul (minkowskiInternalSign (pairFirst i))
  convert! generated using 1
  · funext r
    simp only [Pi.sub_apply,Pi.add_apply,Pi.mul_apply,zero_sub,sub_zero,zero_add]
    congr 2
    funext j
    ring
  · simp only [originalBFContact,lorentzConnectionQuadraticCurvatureVariation,lorentzConnectionLinearCurvatureVariation,
      constantVariationDerivative,Pi.add_apply,Pi.sub_apply,nativeField_connectionDerivative,nativeConnection_lift,
      lorentzSkewConnectionOfBivectorOneForm_add,fieldGravityCurve,configurationRay,gravityConfigurationForce,
      zero_smul,add_zero,zero_sub,sub_zero,zero_add,Fin.sum_univ_four,sourceData,nativePrimitiveFamily,Fin.addCases_right,lorentzPrimitiveDirection]
    ring

private theorem fieldGravityCurve_curvatureJet (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>holonomicGravityCurvature (fieldGravityCurve u force r) 0)
      (originalBFForce u force).2.2 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro p
  simp only [holonomicGravityCurvature,fieldGravityConnectionDerivative]
  have connection (nu k l : Fin 4) : HasDerivAt (fun r : ℝ=>(fieldGravityCurve u force r).gravityConnection 0 nu k l)
      ((gravityConfigurationForce force).gravityConnection 0 nu k l) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const ((gravityConfigurationForce force).gravityConnection 0 nu k l)).const_add
      ((primitiveFamily u).gravityConnection 0 nu k l) using 1
    simp only [fieldGravityCurve,configurationRay,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_one,one_mul]
  have each (j : Fin 4) :=((connection (pairFirst p) (pairFirst i) j).mul (connection (pairSecond p) j (pairSecond i))).sub
    ((connection (pairSecond p) (pairFirst i) j).mul (connection (pairFirst p) j (pairSecond i)))
  have generated:=(HasDerivAt.fun_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 4)))=>each j)).const_mul (minkowskiInternalSign (pairFirst i))
  convert! generated using 1
  · funext r
    simp only [Pi.sub_apply,Pi.mul_apply,zero_sub,sub_zero,zero_add]
  · simp only [originalBFForce,lorentzConnectionLinearCurvatureVariation,constantVariationDerivative,
      fieldGravityCurve,configurationRay,gravityConfigurationForce,zero_smul,add_zero,zero_sub,sub_zero,Fin.sum_univ_four]
    ring

theorem fieldNativeBFCurve_first (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (fieldNativeBFCurve a theta u force) (originalBFForce u force,originalBFContact a theta u force) 0 :=by
  have line (s d : PhysicalBivector) : HasDerivAt (fun r : ℝ=>s+r • d) d 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add s using 1
    simp
  have e : HasDerivAt (fun r : ℝ=>(fieldGravityCurve u force r).coframe 0) (fieldCoframe force) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const (fieldCoframe force)).const_add ((primitiveFamily u).coframe 0) using 1
    simp
  have B:=line ((primitiveFamily u).gravityAuxiliary 0) (fieldGravityB force)
  have nativeE:=((hasDerivAt_id (0:ℝ)).smul_const ((theta • frameGenerator a)*fieldCoframe force)).const_add
    ((theta • frameGenerator a)*((primitiveFamily u).coframe 0))
  have nativeB:=line (bivectorDirection a theta ((primitiveFamily u).gravityAuxiliary 0)) (bivectorDirection a theta (fieldGravityB force))
  have primitiveB:∀ r : ℝ,bivectorDirection a theta ((primitiveFamily u).gravityAuxiliary 0+r • fieldGravityB force)=
      bivectorDirection a theta ((primitiveFamily u).gravityAuxiliary 0)+r • bivectorDirection a theta (fieldGravityB force):=by
    intro r
    have same:=nativeGravityDirection_affine a theta (originalGravityState u) (originalGravityForce force) r
    exact congrArg (fun s : GravityState=>s.2.1) same
  have nativeE' : HasDerivAt (fun r : ℝ=>(fieldNativeGravityDirection a theta u force r).coframe 0)
      ((theta • frameGenerator a)*fieldCoframe force) 0:=by
    convert! nativeE using 1
    · funext r
      simp only [fieldNativeGravityDirection,lorentzPrimitiveDirection,fieldGravityCurve,configurationRay,
        primitiveFamily,configurationFromFields,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
        sourceData,mul_add,mul_smul_comm,id_eq]
    · simp
  have nativeB' : HasDerivAt (fun r : ℝ=>(fieldNativeGravityDirection a theta u force r).gravityAuxiliary 0)
      (bivectorDirection a theta (fieldGravityB force)) 0:=by
    simpa only [fieldNativeGravityDirection,lorentzPrimitiveDirection,fieldGravityCurve,configurationRay,gravityConfigurationForce,primitiveB] using nativeB
  convert! (e.prodMk (B.prodMk (fieldGravityCurve_curvatureJet u force))).prodMk
    (nativeE'.prodMk (nativeB'.prodMk (fieldNativeCurve_curvatureJet a theta u force))) using 1

private theorem fieldNativeBFCurve_initial (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    fieldNativeBFCurve a theta u force 0=(originalBFState u,nativeBFDirection a theta u) :=by
  simp only [fieldNativeBFCurve,fieldGravityCurve,configurationRay,zero_smul,add_zero,fieldNativeGravityDirection,
    lorentzPrimitiveDirection,originalBFState,nativeBFDirection,nativePrimitiveFamily,Fin.addCases_right]
  rw [show (fun _=>connectionBivectorDirection a theta 0 (ambientPrimitiveData u).2.2.2)=
    nativeLorentzFamilyDirection a (fun _=>theta) u from by
      funext x mu
      simp [nativeLorentzFamilyDirection,connectionBivectorDirection,fieldDirectionalDerivative]]
  rfl

def nativeBFFieldMixed (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) : ℝ:=
  bfMixed (originalBFState u) (nativeBFDirection a theta u) (originalBFForce u force) (originalBFContact a theta u force)

theorem nativeBFFieldMixed_actualCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>bfFirst (fieldNativeBFCurve a theta u force r).1 (fieldNativeBFCurve a theta u force r).2)
      (nativeBFFieldMixed a theta u force) 0 :=by
  have initial:=fieldNativeBFCurve_initial a theta u force
  have generated:=((bfFirst_joint_smooth.differentiable (by simp)).differentiableAt (x:=(originalBFState u,nativeBFDirection a theta u))).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (fieldNativeBFCurve_first a theta u force) initial.symm
  rw [bfFirst_joint_fderiv] at generated
  exact generated

def actualSimplicityStateCurve (u : JointParameter) (force : Field289) (r : ℝ) : GravityState:=
  ((fieldGravityCurve u force r).coframe 0,(fieldGravityCurve u force r).gravityAuxiliary 0,
    (fieldGravityCurve u force r).gravitySimplicityMultiplier 0)

def actualNativeSimplicityDirection (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) (r : ℝ) : GravityState:=
  ((fieldNativeGravityDirection a theta u force r).coframe 0,
    (fieldNativeGravityDirection a theta u force r).gravityAuxiliary 0,
      (fieldNativeGravityDirection a theta u force r).gravitySimplicityMultiplier 0)

theorem actualSimplicityStateCurve_source (u : JointParameter) (force : Field289) (r : ℝ) :
    actualSimplicityStateCurve u force r=originalGravityState u+r • originalGravityForce force :=rfl

theorem actualNativeSimplicityDirection_source (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) (r : ℝ) :
    actualNativeSimplicityDirection a theta u force r=
      nativeGravityDirection a theta (actualSimplicityStateCurve u force r) :=by
  apply Prod.ext
  · simp only [actualNativeSimplicityDirection,fieldNativeGravityDirection,lorentzPrimitiveDirection,nativeGravityDirection,
      actualSimplicityStateCurve,fieldGravityCurve,configurationRay,primitiveFamily,configurationFromFields,
      Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,sourceData,gravityConfigurationForce]
  apply Prod.ext <;> rfl

theorem nativeSimplicityFieldMixed_actualCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>simplicityFirst (actualSimplicityStateCurve u force r)
      (actualNativeSimplicityDirection a theta u force r)) (nativeSimplicityMixed a theta u force) 0 :=by
  simp only [actualNativeSimplicityDirection_source,actualSimplicityStateCurve_source]
  exact nativeSimplicityMixed_generated a theta u force

def nativeGravityActionFirst (a : Fin 6) (theta : ℝ) (u : JointParameter) : ℝ:=
  nativeBFTorque a theta u+nativeSimplicityTorque a theta u

theorem nativeGravityActionFirst_actualCurve (a : Fin 6) (theta : ℝ) (u : JointParameter)
    (nondegenerate : ((primitiveFamily u).coframe 0).det≠0) :
    HasDerivAt (fun r : ℝ=>generatedGravityBFDensity (toContinuumPointField (nativeGravityCurve a theta u r) 0)+
      generatedGravitySimplicityDensity (toContinuumPointField (nativeGravityCurve a theta u r) 0))
      (nativeGravityActionFirst a theta u) 0 :=
  (nativeBF_originalCurve a theta u nondegenerate).add (nativeSimplicity_originalCurve a theta u)

def nativeGravityActionMixed (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) : ℝ:=
  nativeBFFieldMixed a theta u force+nativeSimplicityMixed a theta u force

theorem nativeGravityActionMixed_actualCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>bfFirst (fieldNativeBFCurve a theta u force r).1 (fieldNativeBFCurve a theta u force r).2+
      simplicityFirst (actualSimplicityStateCurve u force r) (actualNativeSimplicityDirection a theta u force r))
      (nativeGravityActionMixed a theta u force) 0 :=
  (nativeBFFieldMixed_actualCurve a theta u force).add (nativeSimplicityFieldMixed_actualCurve a theta u force)

end LowEnergy.PreparationVacuumNativeFullGravityReturn
