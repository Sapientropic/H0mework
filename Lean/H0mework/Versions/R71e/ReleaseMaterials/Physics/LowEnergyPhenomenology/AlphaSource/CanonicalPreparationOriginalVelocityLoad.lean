import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalLorentzLoad

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeLegendreSource
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineBlockwiseConstitutive
open PreparationVacuumGravityLegendreSource PreparationVacuumNativeFullGravityReturn
open PreparationVacuumJointFieldResponse
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

abbrev CoframeIndex:=Fin 4×Fin 4

def sourceTemporalJet (v : LorentzianCoframe) : Fin 4→LorentzianCoframe:=fun mu=>if mu=0 then v else 0

def sourceCoframeVelocityLoad (e v : LorentzianCoframe) : LorentzIndex→ℝ:=fun i=>
  -sourceBFBoundaryFirst e v (sourceConnectionBasis i) 0 0

theorem sourceCoframeVelocityLoad_original (e v : LorentzianCoframe) :
    sourceCoframeVelocityLoad e v=sourceLorentzGeometryLoad e (sourceTemporalJet v):=by
  have zeroJet : wedgeFirst e (0:LorentzianCoframe)=0:=by
    funext a p
    simp [wedgeFirst]
  funext i
  simp only [sourceCoframeVelocityLoad,sourceLorentzGeometryLoad,sourceTemporalJet,Fin.sum_univ_four]
  simp [sourceBFBoundaryFirst,sourceBFBoundary,zeroJet,map_zero]

private theorem sourceWedgeJet_add (e v w : LorentzianCoframe) :
    wedgeFirst e (v+w)=wedgeFirst e v+wedgeFirst e w:=by
  funext i p
  simp only [wedgeFirst,Matrix.add_apply,Pi.add_apply]
  ring

private theorem sourceWedgeJet_smul (e v : LorentzianCoframe) (r : ℝ) :
    wedgeFirst e (r • v)=r • wedgeFirst e v:=by
  funext i p
  simp only [wedgeFirst,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  ring

def sourceCoframeVelocityLinear (e : LorentzianCoframe) : LorentzianCoframe→ₗ[ℝ] (LorentzIndex→ℝ) where
  toFun:=sourceCoframeVelocityLoad e
  map_add' v w:=by
    funext i
    simp only [sourceCoframeVelocityLoad,sourceBFBoundaryFirst,sourceBFBoundary,Pi.zero_apply,
      ite_self,sub_self,mul_zero,Finset.sum_const_zero,zero_add,sourceWedgeJet_add,map_add,
      Pi.add_apply,add_mul,Finset.sum_add_distrib]
    ring
  map_smul' r v:=by
    funext i
    simp only [sourceCoframeVelocityLoad,sourceBFBoundaryFirst,sourceBFBoundary,Pi.zero_apply,
      ite_self,sub_self,mul_zero,Finset.sum_const_zero,zero_add,sourceWedgeJet_smul,map_smul,
      Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc,←Finset.mul_sum]
    ring

def sourceVelocityBasis (i : CoframeIndex) : LorentzianCoframe:=fun a mu=>if (a,mu)=i then 1 else 0

theorem sourceVelocity_fullBasis (v : LorentzianCoframe) :
    v=∑i : CoframeIndex,v i.1 i.2 • sourceVelocityBasis i:=by
  funext a mu
  simp [sourceVelocityBasis,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]

def sourceVelocityMatrix (e : LorentzianCoframe) : Matrix LorentzIndex CoframeIndex ℝ:=fun i j=>
  sourceCoframeVelocityLoad e (sourceVelocityBasis j) i

theorem sourceVelocityMatrix_generated (e v : LorentzianCoframe) :
    sourceCoframeVelocityLoad e v=(sourceVelocityMatrix e).mulVec (fun i=>v i.1 i.2):=by
  have actual:=congrArg (sourceCoframeVelocityLinear e) (sourceVelocity_fullBasis v)
  simp only [map_sum,map_smul,smul_eq_mul] at actual
  funext i
  have component:=congrFun actual i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at component
  change sourceCoframeVelocityLoad e v i=
    ∑j : CoframeIndex,v j.1 j.2*sourceCoframeVelocityLoad e (sourceVelocityBasis j) i at component
  change sourceCoframeVelocityLoad e v i=
    ∑j : CoframeIndex,sourceCoframeVelocityLoad e (sourceVelocityBasis j) i*v j.1 j.2
  rw [component]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceLorentzInverse_symmetric (e : LorentzianCoframe) (nondegenerate : e.det≠0) :
    (sourceLorentzInverse e).transpose=sourceLorentzInverse e:=by
  have HS : (sourceLorentzHessian e).transpose=sourceLorentzHessian e:=by
    ext i j
    exact sourceLorentzHessian_symmetric e j i
  have transposed : (sourceLorentzInverse e).transpose*sourceLorentzHessian e=1:=by
    have original:=congrArg Matrix.transpose (sourceLorentzInverse_right e nondegenerate)
    simpa only [Matrix.transpose_mul,HS,Matrix.transpose_one] using original
  calc
    (sourceLorentzInverse e).transpose=(sourceLorentzInverse e).transpose*
        (sourceLorentzHessian e*sourceLorentzInverse e):=by
      rw [sourceLorentzInverse_right e nondegenerate,mul_one]
    _=((sourceLorentzInverse e).transpose*sourceLorentzHessian e)*sourceLorentzInverse e:=by rw [mul_assoc]
    _=sourceLorentzInverse e:=by rw [transposed,one_mul]

def sourceVelocityHessian (e : LorentzianCoframe) : Matrix CoframeIndex CoframeIndex ℝ:=
  -(sourceVelocityMatrix e).transpose*sourceLorentzInverse e*sourceVelocityMatrix e

private def sourceGeometryJetLinear (e : LorentzianCoframe) :
    (Fin 4→LorentzianCoframe)→ₗ[ℝ] (LorentzIndex→ℝ) where
  toFun:=sourceLorentzGeometryLoad e
  map_add' de df:=by
    funext i
    simp only [sourceLorentzGeometryLoad,Pi.add_apply,sourceBFBoundaryFirst,sourceBFBoundary,
      Pi.zero_apply,ite_self,sub_self,mul_zero,Finset.sum_const_zero,zero_add,sourceWedgeJet_add,
      map_add,Pi.add_apply,add_mul,Finset.sum_add_distrib]
    ring
  map_smul' r de:=by
    funext i
    simp only [sourceLorentzGeometryLoad,Pi.smul_apply,sourceBFBoundaryFirst,sourceBFBoundary,
      Pi.zero_apply,ite_self,sub_self,mul_zero,Finset.sum_const_zero,zero_add,sourceWedgeJet_smul,
      map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc,←Finset.mul_sum]
    ring

theorem sourceTemporalLoad_add (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (v : LorentzianCoframe) :
    sourceLorentzOriginalLoad u e (de+sourceTemporalJet v)=
      sourceLorentzOriginalLoad u e de+sourceCoframeVelocityLoad e v:=by
  rw [sourceCoframeVelocityLoad_original]
  have actual:=(sourceGeometryJetLinear e).map_add de (sourceTemporalJet v)
  change sourceLorentzGeometryLoad e (de+sourceTemporalJet v)=
    sourceLorentzGeometryLoad e de+sourceLorentzGeometryLoad e (sourceTemporalJet v) at actual
  simp only [sourceLorentzOriginalLoad,actual]
  abel

def sourceCoframeVelocityAction (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (v : LorentzianCoframe) : ℝ:=
  sourceLorentzLoadedAction u e (de+sourceTemporalJet v)
    (sourceResolvedLorentzConnection u e (de+sourceTemporalJet v))

def sourceCoframeVelocityMomentum (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (v : LorentzianCoframe) : CoframeIndex→ℝ:=
  (sourceVelocityMatrix e).transpose.mulVec
    (fun i=>sourceResolvedLorentzConnection u e (de+sourceTemporalJet v) i.1 i.2)

theorem sourceTemporalLoad_first (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (v dv : LorentzianCoframe) :
    HasDerivAt (fun r : ℝ=>sourceLorentzOriginalLoad u e (de+sourceTemporalJet (v+r • dv)))
      (sourceCoframeVelocityLoad e dv) 0:=by
  have line : HasDerivAt (fun r : ℝ=>v+r • dv) dv 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const dv).const_add v using 1
    simp
  have linear:=(sourceCoframeVelocityLinear e).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 line
  have current : HasDerivAt
      (fun r : ℝ=>sourceLorentzOriginalLoad u e (de+sourceTemporalJet (v+r • dv)))
      (sourceCoframeVelocityLoad e dv) 0:=by
    convert! linear.const_add (sourceLorentzOriginalLoad u e de) using 1
    funext r
    exact sourceTemporalLoad_add u e de (v+r • dv)
  exact current

private theorem sourceInverseSquare_first (e : LorentzianCoframe) (nondegenerate : e.det≠0)
    (J : ℝ→(LorentzIndex→ℝ)) (dJ : LorentzIndex→ℝ) (generated : HasDerivAt J dJ 0) :
    HasDerivAt (fun r=>∑i : LorentzIndex,∑j : LorentzIndex,J r i*sourceLorentzInverse e i j*J r j)
      (2*(∑i : LorentzIndex,dJ i*(sourceLorentzInverse e).mulVec (J 0) i)) 0:=by
  have each (i j : LorentzIndex):=
    ((hasDerivAt_pi.mp generated i).mul_const (sourceLorentzInverse e i j)).mul
      (hasDerivAt_pi.mp generated j)
  have actual:=HasDerivAt.fun_sum (fun i (_ : i∈(Finset.univ : Finset LorentzIndex))=>
    HasDerivAt.fun_sum (fun j (_ : j∈(Finset.univ : Finset LorentzIndex))=>each i j))
  convert! actual using 1
  have symmetry (i j : LorentzIndex) : sourceLorentzInverse e i j=sourceLorentzInverse e j i:=by
    have actual:=congrFun (congrFun (sourceLorentzInverse_symmetric e nondegenerate) j) i
    exact actual
  have reverse : (∑i : LorentzIndex,∑j : LorentzIndex,J 0 i*sourceLorentzInverse e i j*dJ j)=
      ∑i : LorentzIndex,∑j : LorentzIndex,dJ i*sourceLorentzInverse e i j*J 0 j:=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [symmetry j i]
    ring
  simp only [Finset.sum_add_distrib]
  rw [reverse]
  have forward : (∑i : LorentzIndex,dJ i*(sourceLorentzInverse e).mulVec (J 0) i)=
      ∑i : LorentzIndex,∑j : LorentzIndex,dJ i*sourceLorentzInverse e i j*J 0 j:=by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
  rw [forward]
  ring

theorem sourceCoframeVelocityAction_first (u : JointParameter) (e : LorentzianCoframe)
    (nondegenerate : e.det≠0) (de : Fin 4→LorentzianCoframe) (v dv : LorentzianCoframe) :
    HasDerivAt (fun r : ℝ=>sourceCoframeVelocityAction u e de (v+r • dv))
      (∑i : CoframeIndex,sourceCoframeVelocityMomentum u e de v i*dv i.1 i.2) 0:=by
  have current:=sourceTemporalLoad_first u e de v dv
  have square:=sourceInverseSquare_first e nondegenerate _ _ current
  have actual:=(square.const_mul (-(1/2:ℝ))).sub_const (3*e.det)
  convert! actual using 1
  · funext r
    rw [sourceCoframeVelocityAction,sourceLorentzEliminatedAction_original u e nondegenerate]
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
  · simp only [sourceCoframeVelocityMomentum,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
      sourceResolvedLorentzConnection,zero_smul,add_zero,Finset.sum_neg_distrib,mul_neg,neg_mul]
    rw [sourceVelocityMatrix_generated]
    let w:=(sourceLorentzInverse e).mulVec (sourceLorentzOriginalLoad u e (de+sourceTemporalJet v))
    change -(∑j : CoframeIndex,(∑i : LorentzIndex,sourceVelocityMatrix e i j*w i)*dv j.1 j.2)=
      -((1/2:ℝ)*(2*(∑i : LorentzIndex,(∑j : CoframeIndex,sourceVelocityMatrix e i j*dv j.1 j.2)*w i)))
    have shuffle : (∑j : CoframeIndex,(∑i : LorentzIndex,sourceVelocityMatrix e i j*w i)*dv j.1 j.2)=
        ∑i : LorentzIndex,(∑j : CoframeIndex,sourceVelocityMatrix e i j*dv j.1 j.2)*w i:=by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [shuffle]
    ring

theorem sourceCoframeVelocityMomentum_first (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (v dv : LorentzianCoframe) :
    HasDerivAt (fun r : ℝ=>sourceCoframeVelocityMomentum u e de (v+r • dv))
      ((sourceVelocityHessian e).mulVec (fun i=>dv i.1 i.2)) 0:=by
  let M : Matrix CoframeIndex LorentzIndex ℝ:=-(sourceVelocityMatrix e).transpose*sourceLorentzInverse e
  let L:=M.mulVecLin.toContinuousLinearMap
  have actual:=L.hasFDerivAt.comp_hasDerivAt 0 (sourceTemporalLoad_first u e de v dv)
  convert! actual using 1
  · funext r
    change (sourceVelocityMatrix e).transpose.mulVec
        (-(sourceLorentzInverse e).mulVec (sourceLorentzOriginalLoad u e (de+sourceTemporalJet (v+r • dv))))=
      M.mulVec (sourceLorentzOriginalLoad u e (de+sourceTemporalJet (v+r • dv)))
    rw [Matrix.mulVec_neg,←Matrix.mulVec_mulVec]
    simp only [M,Matrix.neg_mul,Matrix.neg_mulVec]
  · rw [sourceVelocityHessian,←Matrix.mulVec_mulVec,←sourceVelocityMatrix_generated e dv]
    rfl

end LowEnergy.PreparationVacuumCoframeLegendreSource
