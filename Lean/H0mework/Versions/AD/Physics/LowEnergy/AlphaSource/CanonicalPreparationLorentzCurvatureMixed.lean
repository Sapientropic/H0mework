import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationPreparedNativeCarrier

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeSourceRestriction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField PointwiseDiracSpinConnectionLift
open StageNineLorentzConnectionVariation StageNineCompactSupportIntegrationByParts
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection PreparationVacuumLorentzFieldInjection
open PreparationVacuumSourceFieldFamily PreparationVacuumGaugeSourceInjection PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open scoped BigOperators Topology ContDiff Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

private def bracket (A B : LorentzianCoframe) : LorentzianCoframe:=A*B-B*A

def forceMatrix (f : BasePoint→LorentzBivectorOneForm) (x : BasePoint) (mu : Fin 4) : LorentzianCoframe:=
  lorentzSkewConnectionOfBivectorOneForm (f x) mu

def forceDerivativeMatrix (f : BasePoint→LorentzBivectorOneForm) (x : BasePoint) (mu nu : Fin 4) : LorentzianCoframe:=
  fun i j=>lorentzConnectionVariationDerivative f x mu nu i j

private def gravityDerivativeMatrix (c : StageNineHolonomicConfiguration) (x : BasePoint) (mu nu : Fin 4) : LorentzianCoframe:=
  fun i j=>gravityConnectionDerivative c x mu nu i j

def curvatureMatrix (c : StageNineHolonomicConfiguration) (x : BasePoint) (p : Fin 6) : LorentzianCoframe:=
  gravityDerivativeMatrix c x (pairFirst p) (pairSecond p)-gravityDerivativeMatrix c x (pairSecond p) (pairFirst p)+
      bracket (c.gravityConnection x (pairFirst p)) (c.gravityConnection x (pairSecond p))

theorem curvatureMatrix_original (c : StageNineHolonomicConfiguration) (x : BasePoint) (i p : Fin 6) :
    minkowskiInternalSign (pairFirst i)*curvatureMatrix c x p (pairFirst i) (pairSecond i)=
      holonomicGravityCurvature c x i p :=by
  simp only [curvatureMatrix,gravityDerivativeMatrix,bracket,holonomicGravityCurvature,Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,
    Finset.sum_sub_distrib]

def curvatureFirstMatrix (c : StageNineHolonomicConfiguration) (f : BasePoint→LorentzBivectorOneForm)
    (x : BasePoint) (p : Fin 6) : LorentzianCoframe:=
  forceDerivativeMatrix f x (pairFirst p) (pairSecond p)-forceDerivativeMatrix f x (pairSecond p) (pairFirst p)+
    bracket (forceMatrix f x (pairFirst p)) (c.gravityConnection x (pairSecond p))+
      bracket (c.gravityConnection x (pairFirst p)) (forceMatrix f x (pairSecond p))

def curvatureSecondMatrix (f h : Fin 4→LorentzianCoframe) (p : Fin 6) : LorentzianCoframe:=
  bracket (f (pairFirst p)) (h (pairSecond p))+bracket (h (pairFirst p)) (f (pairSecond p))

def nativeConnectionMatrix (epsilon : LorentzianCoframe) (gradient A : Fin 4→LorentzianCoframe) : Fin 4→LorentzianCoframe:=
  fun mu=>bracket epsilon (A mu)-gradient mu

private def firstMatrix (A f : Fin 4→LorentzianCoframe) (df : Fin 4→Fin 4→LorentzianCoframe)
    (p : Fin 6) : LorentzianCoframe:=
  df (pairFirst p) (pairSecond p)-df (pairSecond p) (pairFirst p)+
    bracket (f (pairFirst p)) (A (pairSecond p))+bracket (A (pairFirst p)) (f (pairSecond p))

private theorem twoMatrixLegs (epsilon : LorentzianCoframe) (gradient A f : Fin 4→LorentzianCoframe)
    (df : Fin 4→Fin 4→LorentzianCoframe) (p : Fin 6) :
    curvatureSecondMatrix f (nativeConnectionMatrix epsilon gradient A) p+
      firstMatrix A (fun mu=>bracket epsilon (f mu))
        (fun mu nu=>bracket (gradient mu) (f nu)+bracket epsilon (df mu nu)) p=
      bracket epsilon (firstMatrix A f df p) :=by
  unfold curvatureSecondMatrix nativeConnectionMatrix firstMatrix bracket
  noncomm_ring

def nativeLorentzContact (a : Fin 6) (theta : BasePoint→ℝ) (f : BasePoint→LorentzBivectorOneForm) :
    BasePoint→LorentzBivectorOneForm:=fun x mu=>theta x • lorentzBracketCoordinates (Pi.single a 1) (f x mu)

theorem nativeLorentzContact_matrix (a : Fin 6) (theta : BasePoint→ℝ)
    (f : BasePoint→LorentzBivectorOneForm) (x : BasePoint) (mu : Fin 4) :
    forceMatrix (nativeLorentzContact a theta f) x mu=
      bracket (theta x • frameGenerator a) (forceMatrix f x mu) :=by
  change lorentzMatrix (theta x • lorentzBracketCoordinates (Pi.single a 1) (f x mu))=_
  have scale : lorentzMatrix (theta x • lorentzBracketCoordinates (Pi.single a 1) (f x mu))=
      theta x • lorentzMatrix (lorentzBracketCoordinates (Pi.single a 1) (f x mu)):=by
    unfold lorentzMatrix
    rw [Pi.single_smul]
    exact congrArg (fun K : PointwiseLorentzSpinConnection=>K 0)
      (lorentzSkewConnectionOfBivectorOneForm_smul (theta x) (Pi.single 0 (lorentzBracketCoordinates (Pi.single a 1) (f x mu))))
  rw [scale,lorentzMatrix_lie]
  change theta x • (frameGenerator a*forceMatrix f x mu-forceMatrix f x mu*frameGenerator a)=_
  simp only [bracket,smul_sub,smul_mul_assoc,mul_smul_comm]

private def liftMatrix (mu : Fin 4) : LorentzBivectorOneForm→ₗ[ℝ] LorentzianCoframe where
  toFun f:=lorentzSkewConnectionOfBivectorOneForm f mu
  map_add' f h:=congrArg (fun K=>K mu) (lorentzSkewConnectionOfBivectorOneForm_add f h)
  map_smul' t f:=congrArg (fun K=>K mu) (lorentzSkewConnectionOfBivectorOneForm_smul t f)

private theorem forceMatrix_smooth (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm) (mu : Fin 4) :
    ContDiff ℝ ∞ (fun x=>forceMatrix f x mu) :=
  (liftMatrix mu).toContinuousLinearMap.contDiff.comp f.smooth

private theorem forceDerivativeMatrix_original (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (x : BasePoint) (mu nu : Fin 4) :
    fieldDirectionalDerivative (fun y=>forceMatrix f y nu) x mu=forceDerivativeMatrix f x mu nu :=by
  have smooth:=(forceMatrix_smooth f nu).differentiable (by simp) |>.differentiableAt (x:=x)
  ext i j
  simp only [fieldDirectionalDerivative,forceDerivativeMatrix,lorentzConnectionVariationDerivative]
  change (fderiv ℝ (fun y=>forceMatrix f y nu) x (coordinateDirection mu)) i j=
    fderiv ℝ (fun y=>forceMatrix f y nu i j) x (coordinateDirection mu)
  rw [fderiv_apply (differentiableAt_pi.mp smooth i) j,fderiv_apply smooth i]
  rfl

private def matrixAd (L : LorentzianCoframe) : LorentzianCoframe→ₗ[ℝ] LorentzianCoframe where
  toFun:=bracket L
  map_add' A B:=by simp only [bracket,mul_add,add_mul];abel
  map_smul' t A:=by simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

theorem nativeLorentzContact_firstjet (a : Fin 6) (theta : BasePoint→ℝ) (smoothTheta : ContDiff ℝ ∞ theta)
    (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm) (x : BasePoint) (mu nu : Fin 4) :
    forceDerivativeMatrix (nativeLorentzContact a theta f) x mu nu=
      bracket (fieldDirectionalDerivative theta x mu • frameGenerator a) (forceMatrix f x nu)+
        bracket (theta x • frameGenerator a) (forceDerivativeMatrix f x mu nu) :=by
  let L:=(matrixAd (frameGenerator a)).toContinuousLinearMap
  have dTheta:=(smoothTheta.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=x)
  have dForce:=(forceMatrix_smooth f nu).differentiable (by simp) |>.differentiableAt (x:=x) |>.hasFDerivAt
  have generated:=dTheta.smul (L.hasFDerivAt.comp x dForce)
  have same : (fun y=>forceMatrix (nativeLorentzContact a theta f) y nu)=
      fun y=>theta y • L (forceMatrix f y nu) :=by
    funext y
    rw [nativeLorentzContact_matrix]
    change bracket (theta y • frameGenerator a) (forceMatrix f y nu)=theta y • bracket (frameGenerator a) (forceMatrix f y nu)
    simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
  have generated' : HasFDerivAt (fun y=>theta y • L (forceMatrix f y nu))
      (theta x • L.comp (fderiv ℝ (fun y=>forceMatrix f y nu) x)+
        (fderiv ℝ theta x).smulRight (L (forceMatrix f x nu))) x:=by
    convert! generated using 1
  have derivative :=generated'.fderiv
  ext i j
  change (fderiv ℝ (fun y=>forceMatrix (nativeLorentzContact a theta f) y nu i j) x (coordinateDirection mu))=_
  have whole : fderiv ℝ (fun y=>forceMatrix (nativeLorentzContact a theta f) y nu) x=
      (fderiv ℝ theta x).smulRight (L (forceMatrix f x nu))+
        theta x • L.comp (fderiv ℝ (fun y=>forceMatrix f y nu) x) :=by
    rw [same]
    simpa only [Function.comp_apply,Pi.smul_apply,add_comm] using derivative
  have differentiable : DifferentiableAt ℝ (fun y=>forceMatrix (nativeLorentzContact a theta f) y nu) x:=by
    rw [same]
    exact generated'.differentiableAt
  rw [fderiv_apply (differentiableAt_pi.mp differentiable i) j,fderiv_apply differentiable i,whole]
  change ((fderiv ℝ theta x (coordinateDirection mu)) • bracket (frameGenerator a) (forceMatrix f x nu)+
    theta x • bracket (frameGenerator a) (fieldDirectionalDerivative (fun y=>forceMatrix f y nu) x mu)) i j=_
  rw [forceDerivativeMatrix_original]
  simp only [fieldDirectionalDerivative,bracket,smul_mul_assoc,mul_smul_comm,smul_sub]

theorem curvatureFirstMatrix_original (c : StageNineHolonomicConfiguration) (f : BasePoint→LorentzBivectorOneForm)
    (x : BasePoint) (internalPair p : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair)*
      curvatureFirstMatrix c f x p (pairFirst internalPair) (pairSecond internalPair)=
        lorentzConnectionLinearCurvatureVariation c f x internalPair p :=by
  simp only [curvatureFirstMatrix,bracket,forceMatrix,forceDerivativeMatrix,lorentzConnectionLinearCurvatureVariation,
    Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

theorem actualLorentzTwoCurvatureLegs (c : StageNineHolonomicConfiguration) (a : Fin 6)
    (theta : BasePoint→ℝ) (smoothTheta : ContDiff ℝ ∞ theta)
    (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm) (x : BasePoint) (p : Fin 6) :
    curvatureSecondMatrix (forceMatrix f x)
        (nativeConnectionMatrix (theta x • frameGenerator a)
          (fun mu=>fieldDirectionalDerivative theta x mu • frameGenerator a) (c.gravityConnection x)) p+
      curvatureFirstMatrix c (nativeLorentzContact a theta f) x p=
        bracket (theta x • frameGenerator a) (curvatureFirstMatrix c f x p) :=by
  simp only [curvatureFirstMatrix,nativeLorentzContact_firstjet a theta smoothTheta f x,
    nativeLorentzContact_matrix]
  exact twoMatrixLegs (theta x • frameGenerator a)
    (fun mu=>fieldDirectionalDerivative theta x mu • frameGenerator a)
    (c.gravityConnection x) (forceMatrix f x) (forceDerivativeMatrix f x) p

private def coefficientMatrixLinear : (Fin 6→ℝ)→ₗ[ℝ] LorentzianCoframe where
  toFun:=lorentzMatrix
  map_add' v w:=by
    unfold lorentzMatrix
    rw [Pi.single_add]
    exact congrArg (fun K : PointwiseLorentzSpinConnection=>K 0) (lorentzSkewConnectionOfBivectorOneForm_add _ _)
  map_smul' t v:=by
    unfold lorentzMatrix
    rw [Pi.single_smul]
    exact congrArg (fun K : PointwiseLorentzSpinConnection=>K 0) (lorentzSkewConnectionOfBivectorOneForm_smul t _)

def nativeLorentzFamilyDirection (a : Fin 6) (theta : BasePoint→ℝ) (u : JointParameter) :
    BasePoint→LorentzBivectorOneForm:=fun x=>connectionBivectorDirection a (theta x)
      (fieldDirectionalDerivative theta x) (ambientPrimitiveData u).2.2.2

theorem nativeLorentzFamilyDirection_primitive (a : Fin 6) (theta : BasePoint→ℝ) (u : JointParameter) :
    forceMatrix (nativeLorentzFamilyDirection a theta u) 0=
      (nativePrimitiveFamily (Fin.natAdd 3 a) (theta 0) (fieldDirectionalDerivative theta 0) u).gravityConnection 0 :=by
  funext mu
  simp only [nativePrimitiveFamily,Fin.addCases_right,lorentzPrimitiveDirection,forceMatrix,nativeLorentzFamilyDirection]

theorem nativeLorentzFamilyDirection_original (a : Fin 6) (theta : BasePoint→ℝ)
    (u : JointParameter) (x : BasePoint) :
    forceMatrix (nativeLorentzFamilyDirection a theta u) x=
      nativeConnectionMatrix (theta x • frameGenerator a)
        (fun mu=>fieldDirectionalDerivative theta x mu • frameGenerator a) ((primitiveFamily u).gravityConnection x) :=by
  funext mu
  change coefficientMatrixLinear (theta x • lorentzBracketCoordinates (Pi.single a 1)
    ((ambientPrimitiveData u).2.2.2 mu)-fieldDirectionalDerivative theta x mu • Pi.single a 1)=_
  rw [map_sub,map_smul,map_smul]
  change theta x • lorentzMatrix (lorentzBracketCoordinates (Pi.single a 1) ((ambientPrimitiveData u).2.2.2 mu))-
    fieldDirectionalDerivative theta x mu • lorentzMatrix (Pi.single a 1)=_
  rw [lorentzMatrix_lie]
  change theta x • bracket (frameGenerator a) ((primitiveFamily u).gravityConnection x mu)-
    fieldDirectionalDerivative theta x mu • frameGenerator a=_
  simp only [nativeConnectionMatrix,bracket,smul_mul_assoc,mul_smul_comm,smul_sub]

theorem curvatureSecondMatrix_original (f h : BasePoint→LorentzBivectorOneForm) (x : BasePoint)
    (internalPair p : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair)*
      curvatureSecondMatrix (forceMatrix f x) (forceMatrix h x) p (pairFirst internalPair) (pairSecond internalPair)=
        lorentzConnectionQuadraticCurvatureVariation (f+h) x internalPair p-
          lorentzConnectionQuadraticCurvatureVariation f x internalPair p-
            lorentzConnectionQuadraticCurvatureVariation h x internalPair p :=by
  simp only [curvatureSecondMatrix,bracket,forceMatrix,lorentzConnectionQuadraticCurvatureVariation,Pi.add_apply,
    lorentzSkewConnectionOfBivectorOneForm_add,Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,
    add_mul,mul_add,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

theorem nativeLorentzFamily_twoOriginalLegs (a : Fin 6) (theta : BasePoint→ℝ) (smoothTheta : ContDiff ℝ ∞ theta)
    (u : JointParameter) (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (x : BasePoint) (internalPair p : Fin 6) :
    (lorentzConnectionQuadraticCurvatureVariation (f+nativeLorentzFamilyDirection a theta u) x internalPair p-
      lorentzConnectionQuadraticCurvatureVariation f x internalPair p-
        lorentzConnectionQuadraticCurvatureVariation (nativeLorentzFamilyDirection a theta u) x internalPair p)+
      lorentzConnectionLinearCurvatureVariation (primitiveFamily u) (nativeLorentzContact a theta f) x internalPair p=
    minkowskiInternalSign (pairFirst internalPair)*
      bracket (theta x • frameGenerator a) (curvatureFirstMatrix (primitiveFamily u) f x p)
        (pairFirst internalPair) (pairSecond internalPair) :=by
  rw [←curvatureSecondMatrix_original,←curvatureFirstMatrix_original,nativeLorentzFamilyDirection_original]
  rw [←mul_add]
  exact congrArg (fun M : LorentzianCoframe=>minkowskiInternalSign (pairFirst internalPair)*M (pairFirst internalPair) (pairSecond internalPair))
    (actualLorentzTwoCurvatureLegs (primitiveFamily u) a theta smoothTheta f x p)

def forceCoordinateDerivative (f : BasePoint→LorentzBivectorOneForm) (x : BasePoint) (mu nu : Fin 4) : Fin 6→ℝ:=
  fun i=>fieldDirectionalDerivative (fun y=>f y nu i) x mu

private theorem forceDerivativeMatrix_coefficients (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (x : BasePoint) (mu nu : Fin 4) :
    forceDerivativeMatrix f x mu nu=lorentzMatrix (forceCoordinateDerivative f x mu nu) :=by
  have differentiable : DifferentiableAt ℝ (fun y=>f y nu) x:=
    ((contDiff_pi.mp f.smooth) nu).differentiable (by simp) |>.differentiableAt
  let L:=coefficientMatrixLinear.toContinuousLinearMap
  have source : fderiv ℝ (fun y=>forceMatrix f y nu) x=L.comp (fderiv ℝ (fun y=>f y nu) x):=
    (L.hasFDerivAt.comp x differentiable.hasFDerivAt).fderiv
  rw [←forceDerivativeMatrix_original,fieldDirectionalDerivative,source]
  change coefficientMatrixLinear (fderiv ℝ (fun y=>f y nu) x (coordinateDirection mu))=
    coefficientMatrixLinear (forceCoordinateDerivative f x mu nu)
  apply congrArg coefficientMatrixLinear
  funext i
  rw [forceCoordinateDerivative,fieldDirectionalDerivative,fderiv_apply differentiable i]
  rfl

def sourceCurvatureFirstCoefficients (u : JointParameter) (f : BasePoint→LorentzBivectorOneForm)
    (x : BasePoint) (p : Fin 6) : Fin 6→ℝ:=
  forceCoordinateDerivative f x (pairFirst p) (pairSecond p)-forceCoordinateDerivative f x (pairSecond p) (pairFirst p)+
    lorentzBracketCoordinates (f x (pairFirst p)) ((ambientPrimitiveData u).2.2.2 (pairSecond p))+
      lorentzBracketCoordinates ((ambientPrimitiveData u).2.2.2 (pairFirst p)) (f x (pairSecond p))

theorem sourceCurvatureFirst_matrix (u : JointParameter) (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (x : BasePoint) (p : Fin 6) :
    curvatureFirstMatrix (primitiveFamily u) f x p=lorentzMatrix (sourceCurvatureFirstCoefficients u f x p) :=by
  rw [curvatureFirstMatrix,forceDerivativeMatrix_coefficients,forceDerivativeMatrix_coefficients]
  change lorentzMatrix (forceCoordinateDerivative f x (pairFirst p) (pairSecond p))-
    lorentzMatrix (forceCoordinateDerivative f x (pairSecond p) (pairFirst p))+
      bracket (lorentzMatrix (f x (pairFirst p))) (lorentzMatrix ((ambientPrimitiveData u).2.2.2 (pairSecond p)))+
        bracket (lorentzMatrix ((ambientPrimitiveData u).2.2.2 (pairFirst p))) (lorentzMatrix (f x (pairSecond p)))=_
  unfold bracket
  rw [←lorentzMatrix_lie,←lorentzMatrix_lie]
  change coefficientMatrixLinear _-coefficientMatrixLinear _+coefficientMatrixLinear _+coefficientMatrixLinear _=
    coefficientMatrixLinear (sourceCurvatureFirstCoefficients u f x p)
  rw [←map_sub,←map_add,←map_add]
  rfl

theorem sourceCurvatureFirst_original (u : JointParameter) (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (x : BasePoint) (i p : Fin 6) :
    lorentzConnectionLinearCurvatureVariation (primitiveFamily u) f x i p=sourceCurvatureFirstCoefficients u f x p i :=by
  rw [←curvatureFirstMatrix_original,sourceCurvatureFirst_matrix]
  change loweredLorentzConnectionCoefficient (lorentzSkewConnectionOfBivectorOneForm
    (Pi.single 0 (sourceCurvatureFirstCoefficients u f x p))) 0 i=_
  rw [loweredLorentzConnectionCoefficient_ofBivectorOneForm,Pi.single_eq_same]

private theorem sixBracketCoordinates_basis (v w : Fin 6→ℝ) (i : Fin 6) :
    lorentzBracketCoordinates v w i=∑j : Fin 6,lorentzBracketCoordinates v (Pi.single j 1) i*w j :=by
  have sourceBasis : w=∑j : Fin 6,w j • Pi.single j 1:=by
    funext j
    simp [Pi.single_apply]
  have sourceMatrix : lorentzMatrix w=∑j : Fin 6,w j • lorentzMatrix (Pi.single j 1):=by
    change coefficientMatrixLinear w=_
    conv_lhs=>rw [sourceBasis,map_sum]
    simp only [map_smul]
    rfl
  rw [lorentzBracketCoordinates,sourceMatrix]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,←Finset.sum_sub_distrib,
    Finset.sum_apply,Matrix.sum_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,lorentzBracketCoordinates,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem nativeLorentzFamily_BF_twoLegs (a : Fin 6) (theta : BasePoint→ℝ) (smoothTheta : ContDiff ℝ ∞ theta)
    (u : JointParameter) (f : CompactlySupportedSmoothVariation LorentzBivectorOneForm) (auxPair p : Fin 6) :
    (∑i : Fin 6,(nativePrimitiveFamily (Fin.natAdd 3 a) (theta 0) (fieldDirectionalDerivative theta 0) u).gravityAuxiliary 0 i auxPair*
      lorentzConnectionLinearCurvatureVariation (primitiveFamily u) f 0 i p)+
      (∑i : Fin 6,(primitiveFamily u).gravityAuxiliary 0 i auxPair*
        ((lorentzConnectionQuadraticCurvatureVariation (f+nativeLorentzFamilyDirection a theta u) 0 i p-
          lorentzConnectionQuadraticCurvatureVariation f 0 i p-
            lorentzConnectionQuadraticCurvatureVariation (nativeLorentzFamilyDirection a theta u) 0 i p)+
          lorentzConnectionLinearCurvatureVariation (primitiveFamily u) (nativeLorentzContact a theta f) 0 i p))=0 :=by
  simp only [nativeLorentzFamily_twoOriginalLegs a theta smoothTheta u f 0,
    sourceCurvatureFirst_original,sourceCurvatureFirst_matrix]
  have coefficient (i : Fin 6) : minkowskiInternalSign (pairFirst i)*
      bracket (theta 0 • frameGenerator a) (lorentzMatrix (sourceCurvatureFirstCoefficients u f 0 p))
        (pairFirst i) (pairSecond i)=
        theta 0*lorentzBracketCoordinates (Pi.single a 1) (sourceCurvatureFirstCoefficients u f 0 p) i :=by
    simp only [bracket,smul_mul_assoc,mul_smul_comm,←smul_sub,Matrix.smul_apply,smul_eq_mul]
    change _=theta 0*(minkowskiInternalSign (pairFirst i)*
      (frameGenerator a*lorentzMatrix (sourceCurvatureFirstCoefficients u f 0 p)-
        lorentzMatrix (sourceCurvatureFirstCoefficients u f 0 p)*frameGenerator a) (pairFirst i) (pairSecond i))
    ring
  simp only [coefficient,nativePrimitiveFamily,Fin.addCases_right,lorentzPrimitiveDirection]
  simp_rw [sixBracketCoordinates_basis (Pi.single a 1) (sourceCurvatureFirstCoefficients u f 0 p)]
  exact bivectorDirection_originalBF a (theta 0) ((primitiveFamily u).gravityAuxiliary 0)
    (sourceCurvatureFirstCoefficients u f 0 p) auxPair

end LowEnergy.PreparationVacuumNativeSourceRestriction
