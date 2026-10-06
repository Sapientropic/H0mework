import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalLorentzInverse
import H0mework.Physics.DualVariation.LorentzConnectionVariation
import H0mework.Physics.Dirac.MatterSpinThreeForm

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumGravityLegendreSource
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource StageNineTopologicalFourFormPairing StageNineTopologicalGravityCurvatureVariancePairing
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeLorentzConnectionVariation
open StageNineFormNativeLorentzConnectionLocalVariation StageNineFormNativeMatterSpinThreeForm
open PreparationVacuumNativeFullGravityReturn PreparationVacuumNativeSourceRestriction
open PreparationVacuumJointFieldResponse PreparationVacuumLorentzFieldInjection PreparationVacuumNativeFieldInjection
open PreparationVacuumRepairedGravityActionReturn PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open StageNineCompactSupportIntegrationByParts StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open StageNineLorentzConnectionActualVariationCore
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def sourceLorentzSpinLoad (u : JointParameter) (e : LorentzianCoframe) : LorentzIndex→ℝ:=fun i=>
  formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 0
    (toContinuumPointField (sourceConnectionConfiguration u e 0) 0) (sourceConnectionBasis i)

theorem sourceLorentzSpinLoad_fullBasis (u : JointParameter) (e : LorentzianCoframe) (omega : LorentzBivectorOneForm) :
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0 0
      (toContinuumPointField (sourceConnectionConfiguration u e 0) 0) omega=
        ∑i : LorentzIndex,sourceLorentzSpinLoad u e i*omega i.1 i.2 :=by
  let source:=formNativeLorentzMatterFirstLinearMap positiveSmoothUnifiedSource 0 0
    (toContinuumPointField (sourceConnectionConfiguration u e 0) 0)
  change source omega=_
  calc
    source omega=source (∑i : LorentzIndex,omega i.1 i.2 • sourceConnectionBasis i):=
      congrArg source (sourceConnection_fullBasis omega)
    _= _:=by
      simp only [map_sum,map_smul,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      change omega i.1 i.2*sourceLorentzSpinLoad u e i=sourceLorentzSpinLoad u e i*omega i.1 i.2
      ring

theorem sourceLorentzSpinLoad_originalAffine (u : JointParameter) (e : LorentzianCoframe)
    (omega : LorentzBivectorOneForm) (r : ℝ) :
    generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 0
      (withLorentzConnectionJets (toContinuumPointField (sourceConnectionConfiguration u e 0) 0)
        (sourceCurvatureQuadratic (r • omega))
        ((toContinuumPointField (sourceConnectionConfiguration u e 0) 0).matterCovariantDerivative+
          r • pointwiseMatterLorentzConnectionVariation
            (toContinuumPointField (sourceConnectionConfiguration u e 0) 0) omega))=
      generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 0
        (toContinuumPointField (sourceConnectionConfiguration u e 0) 0)+
          r*(∑i : LorentzIndex,sourceLorentzSpinLoad u e i*omega i.1 i.2) :=by
  rw [generatedDiracDualFormNativeMatterDensity_withLorentzConnectionJets_affine]
  rw [←sourceLorentzSpinLoad_fullBasis]
  rfl

def sourceBFBoundary (e : LorentzianCoframe) (omega : LorentzBivectorOneForm) (mu : Fin 4) : ℝ:=
  ∑a : Fin 6,∑p : Fin 6,physicalIIPlusBivector e a (twoFormComplement p)*
    ((if mu=pairFirst p then omega (pairSecond p) a else 0)-
      (if mu=pairSecond p then omega (pairFirst p) a else 0))

def sourceBFBoundaryFirst (e de : LorentzianCoframe) (omega domega : LorentzBivectorOneForm) (mu : Fin 4) : ℝ:=
  sourceBFBoundary e domega mu+
    ∑a : Fin 6,∑p : Fin 6,gravityInternalDualEquiv (wedgeFirst e de) a (twoFormComplement p)*
      ((if mu=pairFirst p then omega (pairSecond p) a else 0)-
        (if mu=pairSecond p then omega (pairFirst p) a else 0))

theorem sourceBFBoundaryFirst_generated (e de : LorentzianCoframe) (omega domega : LorentzBivectorOneForm) (mu : Fin 4) :
    HasDerivAt (fun r : ℝ=>sourceBFBoundary (e+r • de) (omega+r • domega) mu)
      (sourceBFBoundaryFirst e de omega domega mu) 0 :=by
  have wedge : HasDerivAt (fun r : ℝ=>coframeWedge (e+r • de)) (wedgeFirst e de) 0:=
    hasDerivAt_pi.mpr (fun a=>hasDerivAt_pi.mpr (fun p=>wedgeFirst_generated _ _ a p))
  have B : HasDerivAt (fun r : ℝ=>physicalIIPlusBivector (e+r • de)) (gravityInternalDualEquiv (wedgeFirst e de)) 0:=
    gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 wedge
  have entry (nu : Fin 4) (a : Fin 6) : HasDerivAt (fun r : ℝ=>(omega+r • domega) nu a) (domega nu a) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const (domega nu a)).const_add (omega nu a) using 1
    simp
  have each (a p : Fin 6) := by
    have forward : HasDerivAt (fun r : ℝ=>if mu=pairFirst p then (omega+r • domega) (pairSecond p) a else 0)
        (if mu=pairFirst p then domega (pairSecond p) a else 0) 0:=by
      split_ifs <;> first | exact entry _ _ | exact hasDerivAt_const 0 0
    have reverse : HasDerivAt (fun r : ℝ=>if mu=pairSecond p then (omega+r • domega) (pairFirst p) a else 0)
        (if mu=pairSecond p then domega (pairFirst p) a else 0) 0:=by
      split_ifs <;> first | exact entry _ _ | exact hasDerivAt_const 0 0
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp B a) (twoFormComplement p)).mul (forward.sub reverse)
  have generated:=HasDerivAt.fun_sum (fun a (_ : a∈(Finset.univ : Finset (Fin 6)))=>
    HasDerivAt.fun_sum (fun p (_ : p∈(Finset.univ : Finset (Fin 6)))=>each a p))
  convert! generated using 1
  simp only [sourceBFBoundaryFirst,sourceBFBoundary,zero_smul,add_zero,Pi.sub_apply,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  ring

def sourceLorentzGeometryLoad (e : LorentzianCoframe) (de : Fin 4→LorentzianCoframe) : LorentzIndex→ℝ:=fun i=>
  -(∑mu : Fin 4,sourceBFBoundaryFirst e (de mu) (sourceConnectionBasis i) 0 mu)

private def sourceCoframeBoundaryLinear (e de : LorentzianCoframe) (mu : Fin 4) : LorentzBivectorOneForm→ₗ[ℝ] ℝ where
  toFun omega:=sourceBFBoundaryFirst e de omega 0 mu
  map_add' omega eta:=by
    simp only [sourceBFBoundaryFirst,sourceBFBoundary,Pi.zero_apply,ite_self,sub_self,mul_zero,
      Finset.sum_const_zero,zero_add,Pi.add_apply]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  map_smul' r omega:=by
    simp only [sourceBFBoundaryFirst,sourceBFBoundary,Pi.zero_apply,ite_self,sub_self,mul_zero,
      Finset.sum_const_zero,zero_add,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring

theorem sourceLorentzGeometryLoad_fullBasis (e : LorentzianCoframe) (de : Fin 4→LorentzianCoframe)
    (omega : LorentzBivectorOneForm) :
    -(∑mu : Fin 4,sourceBFBoundaryFirst e (de mu) omega 0 mu)=
      ∑i : LorentzIndex,sourceLorentzGeometryLoad e de i*omega i.1 i.2 :=by
  have source (mu : Fin 4) : sourceBFBoundaryFirst e (de mu) omega 0 mu=
      ∑i : LorentzIndex,omega i.1 i.2*sourceBFBoundaryFirst e (de mu) (sourceConnectionBasis i) 0 mu:=by
    let L:=sourceCoframeBoundaryLinear e (de mu) mu
    change L omega=_
    calc
      L omega=L (∑i : LorentzIndex,omega i.1 i.2 • sourceConnectionBasis i):=
        congrArg L (sourceConnection_fullBasis omega)
      _= _:=by simp only [map_sum,map_smul,smul_eq_mul];rfl
  simp_rw [source]
  rw [Finset.sum_comm,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sourceLorentzGeometryLoad]
  rw [←Finset.mul_sum]
  ring

def sourceCurvatureDerivative (domega : Fin 4→LorentzBivectorOneForm) : PhysicalBivector:=fun a p=>
  domega (pairFirst p) (pairSecond p) a-domega (pairSecond p) (pairFirst p) a

theorem sourceBFCurl_originalBoundary (e : LorentzianCoframe) (domega : Fin 4→LorentzBivectorOneForm) :
    gravityTopologicalBFCoefficient (physicalIIPlusBivector e) (sourceCurvatureDerivative domega)=
      ∑mu : Fin 4,sourceBFBoundary e (domega mu) mu :=by
  rw [gravityTopologicalBFCoefficient_eq_mixed]
  simp only [gravityTopologicalMixedWedgeCoefficient,orientedTwoFormWedgeCoefficient,
    generatedTwoFormWedgeCoefficient,sourceCurvatureDerivative,sourceBFBoundary]
  conv_rhs=>rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [Fin.sum_univ_four,Fin.sum_univ_six,twoFormComplement,pairFirst,pairSecond]
  ring

theorem sourceBFOriginalGreenIdentity (e : LorentzianCoframe) (de : Fin 4→LorentzianCoframe)
    (omega : LorentzBivectorOneForm) (domega : Fin 4→LorentzBivectorOneForm) :
    gravityTopologicalBFCoefficient (physicalIIPlusBivector e) (sourceCurvatureDerivative domega)=
      (∑mu : Fin 4,sourceBFBoundaryFirst e (de mu) omega (domega mu) mu)+
        ∑i : LorentzIndex,sourceLorentzGeometryLoad e de i*omega i.1 i.2 :=by
  rw [sourceBFCurl_originalBoundary,←sourceLorentzGeometryLoad_fullBasis]
  simp only [sourceBFBoundaryFirst,Finset.sum_add_distrib]
  simp [sourceBFBoundary]

def sourceLorentzOriginalLoad (u : JointParameter) (e : LorentzianCoframe) (de : Fin 4→LorentzianCoframe) : LorentzIndex→ℝ:=
  sourceLorentzGeometryLoad e de+sourceLorentzSpinLoad u e

def sourceLorentzEulerResidual (u : JointParameter) (e : LorentzianCoframe) (de : Fin 4→LorentzianCoframe)
    (omega : LorentzBivectorOneForm) : LorentzIndex→ℝ:=
  (sourceLorentzHessian e).mulVec (fun i=>omega i.1 i.2)+sourceLorentzOriginalLoad u e de

def sourceLorentzLoadedAction (u : JointParameter) (e : LorentzianCoframe) (de : Fin 4→LorentzianCoframe)
    (omega : LorentzBivectorOneForm) : ℝ:=
  sourceLorentzQuadratic e omega+(∑i : LorentzIndex,sourceLorentzOriginalLoad u e de i*omega i.1 i.2)-3*e.det

theorem sourceLorentzLoadedAction_original (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (omega : LorentzBivectorOneForm)
    (domega : Fin 4→LorentzBivectorOneForm) :
    reducedGravityDensity ((e,(primitiveFamily u).gravityAuxiliary 0,(primitiveFamily u).gravitySimplicityMultiplier 0),
      sourceCurvatureDerivative domega+sourceCurvatureQuadratic omega)+
      generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 0
        (withLorentzConnectionJets (toContinuumPointField (sourceConnectionConfiguration u e 0) 0)
          (sourceCurvatureDerivative domega+sourceCurvatureQuadratic omega)
          ((toContinuumPointField (sourceConnectionConfiguration u e 0) 0).matterCovariantDerivative+
            pointwiseMatterLorentzConnectionVariation
              (toContinuumPointField (sourceConnectionConfiguration u e 0) 0) omega))=
      (∑mu : Fin 4,sourceBFBoundaryFirst e (de mu) omega (domega mu) mu)+
        sourceLorentzLoadedAction u e de omega+
        generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 0
          (toContinuumPointField (sourceConnectionConfiguration u e 0) 0) :=by
  have matter : generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 0
      (withLorentzConnectionJets (toContinuumPointField (sourceConnectionConfiguration u e 0) 0)
        (sourceCurvatureDerivative domega+sourceCurvatureQuadratic omega)
        ((toContinuumPointField (sourceConnectionConfiguration u e 0) 0).matterCovariantDerivative+
          pointwiseMatterLorentzConnectionVariation
            (toContinuumPointField (sourceConnectionConfiguration u e 0) 0) omega))=
      generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 0
        (toContinuumPointField (sourceConnectionConfiguration u e 0) 0)+
          ∑i : LorentzIndex,sourceLorentzSpinLoad u e i*omega i.1 i.2:=by
    rw [←sourceLorentzSpinLoad_fullBasis]
    simpa only [one_smul,one_mul,formNativeLorentzMatterFirstCoefficient] using
      generatedDiracDualFormNativeMatterDensity_withLorentzConnectionJets_affine positiveSmoothUnifiedSource 0 0
        (toContinuumPointField (sourceConnectionConfiguration u e 0) 0)
        (sourceCurvatureDerivative domega+sourceCurvatureQuadratic omega)
        (pointwiseMatterLorentzConnectionVariation
          (toContinuumPointField (sourceConnectionConfiguration u e 0) 0) omega) (1:ℝ)
  rw [reducedGravityDensity_volume,gravityTopologicalBFCoefficient_add_right,sourceBFOriginalGreenIdentity,matter]
  simp only [sourceLorentzLoadedAction,sourceLorentzOriginalLoad,Pi.add_apply,add_mul,Finset.sum_add_distrib,
    sourceLorentzQuadratic]
  ring

private theorem sourceLorentzBilinear_fullMatrix (e : LorentzianCoframe) (omega eta : LorentzBivectorOneForm) :
    sourceLorentzBilinear e omega eta=∑i : LorentzIndex,∑j : LorentzIndex,
      omega i.1 i.2*sourceLorentzHessian e i j*eta j.1 j.2:=by
  have expansion : sourceLorentzBilinear e omega eta=
      ∑i : LorentzIndex,omega i.1 i.2*sourceLorentzBilinear e (sourceConnectionBasis i) eta:=by
    change sourceLorentzLinear e eta omega=_
    calc
      sourceLorentzLinear e eta omega=sourceLorentzLinear e eta
          (∑i : LorentzIndex,omega i.1 i.2 • sourceConnectionBasis i):=
        congrArg (sourceLorentzLinear e eta) (sourceConnection_fullBasis omega)
      _= _:=by simp only [map_sum,map_smul,smul_eq_mul];rfl
  have each (i : LorentzIndex) : sourceLorentzBilinear e (sourceConnectionBasis i) eta=
      ∑j : LorentzIndex,eta j.1 j.2*sourceLorentzHessian e i j:=by
    rw [sourceLorentzBilinear_symmetric]
    change sourceLorentzLinear e (sourceConnectionBasis i) eta=_
    calc
      sourceLorentzLinear e (sourceConnectionBasis i) eta=
          sourceLorentzLinear e (sourceConnectionBasis i)
            (∑j : LorentzIndex,eta j.1 j.2 • sourceConnectionBasis j):=
        congrArg (sourceLorentzLinear e (sourceConnectionBasis i)) (sourceConnection_fullBasis eta)
      _= _:=by
        simp only [map_sum,map_smul,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        change eta j.1 j.2*sourceLorentzHessian e j i=eta j.1 j.2*sourceLorentzHessian e i j
        rw [sourceLorentzHessian_symmetric]
  rw [expansion]
  simp_rw [each,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceLorentzLoadedAction_first (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (omega eta : LorentzBivectorOneForm) :
    HasDerivAt (fun r : ℝ=>sourceLorentzLoadedAction u e de (omega+r • eta))
      (∑i : LorentzIndex,sourceLorentzEulerResidual u e de omega i*eta i.1 i.2) 0:=by
  have each (i : LorentzIndex) : HasDerivAt
      (fun r : ℝ=>sourceLorentzOriginalLoad u e de i*(omega+r • eta) i.1 i.2)
      (sourceLorentzOriginalLoad u e de i*eta i.1 i.2) 0:=by
    convert! (((hasDerivAt_id (0:ℝ)).mul_const (eta i.1 i.2)).const_add (omega i.1 i.2)).const_mul
      (sourceLorentzOriginalLoad u e de i) using 1
    simp
  have linear:=HasDerivAt.fun_sum (fun i (_ : i∈(Finset.univ : Finset LorentzIndex))=>each i)
  have actual:=((sourceLorentzQuadratic_first e omega eta).add linear).sub_const (3*e.det)
  convert! actual using 1
  rw [sourceLorentzBilinear_fullMatrix]
  simp only [sourceLorentzEulerResidual,Pi.add_apply,Matrix.mulVec,dotProduct,
    add_mul,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceLorentzHessian_symmetric]
  ring


def sourceResolvedLorentzConnection (u : JointParameter) (e : LorentzianCoframe) (de : Fin 4→LorentzianCoframe) : LorentzBivectorOneForm:=
  fun mu a=>-(sourceLorentzInverse e).mulVec (sourceLorentzOriginalLoad u e de) (mu,a)

theorem sourceResolvedLorentzConnection_euler (u : JointParameter) (e : LorentzianCoframe)
    (nondegenerate : e.det≠0) (de : Fin 4→LorentzianCoframe) :
    sourceLorentzEulerResidual u e de (sourceResolvedLorentzConnection u e de)=0 :=by
  have actual:=congrArg (fun A : Matrix LorentzIndex LorentzIndex ℝ=>A.mulVec (sourceLorentzOriginalLoad u e de))
    (sourceLorentzInverse_right e nondegenerate)
  rw [←Matrix.mulVec_mulVec,Matrix.one_mulVec] at actual
  unfold sourceLorentzEulerResidual sourceResolvedLorentzConnection
  change (sourceLorentzHessian e).mulVec (-(sourceLorentzInverse e).mulVec (sourceLorentzOriginalLoad u e de))+
    sourceLorentzOriginalLoad u e de=0
  rw [Matrix.mulVec_neg,actual]
  simp

theorem sourceResolvedLorentzConnection_unique (u : JointParameter) (e : LorentzianCoframe)
    (nondegenerate : e.det≠0) (de : Fin 4→LorentzianCoframe) (omega : LorentzBivectorOneForm)
    (equation : sourceLorentzEulerResidual u e de omega=0) :
    omega=sourceResolvedLorentzConnection u e de :=by
  have solve:=congrArg ((sourceLorentzInverse e).mulVec) equation
  simp only [sourceLorentzEulerResidual,Matrix.mulVec_add,Matrix.mulVec_zero] at solve
  rw [Matrix.mulVec_mulVec,sourceLorentzInverse_left e nondegenerate,Matrix.one_mulVec] at solve
  funext mu a
  have component:=congrFun solve (mu,a)
  change omega mu a=-(sourceLorentzInverse e).mulVec (sourceLorentzOriginalLoad u e de) (mu,a)
  simp only [Pi.add_apply,Pi.zero_apply] at component
  linarith

theorem sourceResolvedLorentzConnection_stationary (u : JointParameter) (e : LorentzianCoframe)
    (nondegenerate : e.det≠0) (de : Fin 4→LorentzianCoframe) (eta : LorentzBivectorOneForm) :
    HasDerivAt (fun r : ℝ=>sourceLorentzLoadedAction u e de (sourceResolvedLorentzConnection u e de+r • eta)) 0 0:=by
  simpa only [sourceResolvedLorentzConnection_euler u e nondegenerate de,Pi.zero_apply,zero_mul,Finset.sum_const_zero]
    using sourceLorentzLoadedAction_first u e de (sourceResolvedLorentzConnection u e de) eta

theorem sourceLorentzEliminatedAction_original (u : JointParameter) (e : LorentzianCoframe)
    (nondegenerate : e.det≠0) (de : Fin 4→LorentzianCoframe) :
    sourceLorentzLoadedAction u e de (sourceResolvedLorentzConnection u e de)=
      -(1/2:ℝ)*(∑i : LorentzIndex,sourceLorentzOriginalLoad u e de i*
        (sourceLorentzInverse e).mulVec (sourceLorentzOriginalLoad u e de) i)-3*e.det :=by
  have euler:=sourceResolvedLorentzConnection_euler u e nondegenerate de
  have read : (sourceLorentzHessian e).mulVec
      (fun i=>sourceResolvedLorentzConnection u e de i.1 i.2)=-sourceLorentzOriginalLoad u e de:=by
    funext i
    have component:=congrFun euler i
    simp only [sourceLorentzEulerResidual,Pi.add_apply,Pi.zero_apply] at component
    change (sourceLorentzHessian e).mulVec
      (fun i=>sourceResolvedLorentzConnection u e de i.1 i.2) i = -sourceLorentzOriginalLoad u e de i
    linarith
  rw [sourceLorentzLoadedAction,sourceLorentzQuadratic_fullMatrix]
  have quadratic : (∑i : LorentzIndex,∑j : LorentzIndex,
      sourceResolvedLorentzConnection u e de i.1 i.2*sourceLorentzHessian e i j*
        sourceResolvedLorentzConnection u e de j.1 j.2)=
      -(∑i : LorentzIndex,sourceLorentzOriginalLoad u e de i*sourceResolvedLorentzConnection u e de i.1 i.2):=by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have row:=congrFun read i
    rw [Matrix.mulVec,dotProduct] at row
    have factor : (∑j : LorentzIndex,sourceResolvedLorentzConnection u e de i.1 i.2*sourceLorentzHessian e i j*
        sourceResolvedLorentzConnection u e de j.1 j.2)=
      sourceResolvedLorentzConnection u e de i.1 i.2*
        (∑j : LorentzIndex,sourceLorentzHessian e i j*sourceResolvedLorentzConnection u e de j.1 j.2):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [factor,row]
    simp only [Pi.neg_apply]
    ring
  rw [quadratic]
  simp only [sourceResolvedLorentzConnection,neg_mul,mul_neg,Finset.sum_neg_distrib]
  ring

end LowEnergy.PreparationVacuumGravityLegendreSource
