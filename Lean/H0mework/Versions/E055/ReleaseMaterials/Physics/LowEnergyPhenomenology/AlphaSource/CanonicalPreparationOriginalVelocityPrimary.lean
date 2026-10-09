import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalVelocityLoad

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeLegendreSource
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineBlockwiseConstitutive
open StageNineLorentzConnectionVariation StageNineTopologicalFourFormPairing StageNineGlobalIntegratedAction
open PreparationVacuumGravityLegendreSource PreparationVacuumNativeFullGravityReturn
open PreparationVacuumLorentzFieldInjection PreparationVacuumNativeLocalWard
open PreparationVacuumJointFieldResponse
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

theorem sourceVelocityMatrix_timeRow (e : LorentzianCoframe) (a : Fin 6) (i : CoframeIndex) :
    sourceVelocityMatrix e (0,a) i=0:=by
  simp [sourceVelocityMatrix,sourceCoframeVelocityLoad,sourceBFBoundaryFirst,sourceBFBoundary,
    sourceConnectionBasis,Fin.sum_univ_six,pairFirst,pairSecond]

theorem sourceVelocityMatrix_timeColumn (e : LorentzianCoframe) (i : LorentzIndex) (a : Fin 4) :
    sourceVelocityMatrix e i (a,0)=0:=by
  rcases i with ⟨mu,b⟩
  fin_cases mu <;> fin_cases b <;> fin_cases a <;>
    simp [sourceVelocityMatrix,sourceCoframeVelocityLoad,sourceBFBoundaryFirst,sourceBFBoundary,
      sourceConnectionBasis,sourceVelocityBasis,wedgeFirst,gravityInternalDualEquiv,gravityInternalDualLinear,
      internalBivectorDual,lorentzianCoframeHodge,LinearMap.coe_mk,AddHom.coe_mk,
      Fin.sum_univ_six,pairFirst,pairSecond,twoFormComplement]

theorem sourceCoframeVelocityMomentum_timePrimary (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (v : LorentzianCoframe) (a : Fin 4) :
    sourceCoframeVelocityMomentum u e de v (a,0)=0:=by
  simp only [sourceCoframeVelocityMomentum,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
    sourceVelocityMatrix_timeColumn,zero_mul,Finset.sum_const_zero]

theorem sourceVelocityHessian_timePrimary (e : LorentzianCoframe) (a : Fin 4) :
    (sourceVelocityHessian e).mulVec (fun i=>sourceVelocityBasis (a,0) i.1 i.2)=0:=by
  have actual : (sourceVelocityMatrix e).mulVec (fun i=>sourceVelocityBasis (a,0) i.1 i.2)=0:=by
    funext i
    simp [Matrix.mulVec,dotProduct,sourceVelocityBasis,sourceVelocityMatrix_timeColumn]
  rw [sourceVelocityHessian,←Matrix.mulVec_mulVec,actual,Matrix.mulVec_zero]

def sourceLorentzTemporalVelocity (e : LorentzianCoframe) (a : Fin 6) : LorentzianCoframe:=frameGenerator a*e

theorem sourceLorentzTemporalVelocity_original (e : LorentzianCoframe) (a : Fin 6) :
    sourceLorentzTemporalVelocity e a=nativeFrameGenerator (Fin.natAdd 3 a)*e:=by
  rw [sourceLorentzTemporalVelocity,frameGenerator_original]

theorem sourceLorentzTemporalLoad_native (e : LorentzianCoframe) (a : Fin 6) (i : LorentzIndex) :
    sourceCoframeVelocityLoad e (sourceLorentzTemporalVelocity e a) i=sourceLorentzHessian e i (0,a):=by
  rw [sourceLorentzHessian_coefficients]
  rcases i with ⟨mu,b⟩
  fin_cases mu <;> fin_cases b <;> fin_cases a <;>
    simp [sourceCoframeVelocityLoad,sourceBFBoundaryFirst,sourceBFBoundary,sourceLorentzTemporalVelocity,
      sourceConnectionBasis,wedgeFirst,gravityInternalDualEquiv,gravityInternalDualLinear,
      internalBivectorDual,lorentzianCoframeHodge,physicalIIPlusBivector,coframeWedge,
      sourceLorentzStructure,frameGenerator,lorentzGenerator,lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,orientedLorentzBivectorBasisCoefficient,Pi.single_apply,
      LinearMap.coe_mk,AddHom.coe_mk,Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_six,
      minkowskiInternalSign,lorentzianTwoFormSign,pairFirst,pairSecond,twoFormComplement] <;> ring

theorem sourceLorentzTemporalLoad_matrix (e : LorentzianCoframe) (a : Fin 6) :
    (sourceVelocityMatrix e).mulVec (fun i=>sourceLorentzTemporalVelocity e a i.1 i.2)=
      (sourceLorentzHessian e).mulVec (fun i=>sourceConnectionBasis (0,a) i.1 i.2):=by
  rw [←sourceVelocityMatrix_generated]
  funext i
  rw [sourceLorentzTemporalLoad_native]
  simp [Matrix.mulVec,dotProduct,sourceConnectionBasis]

theorem sourceVelocityHessian_nativePrimary (e : LorentzianCoframe) (nondegenerate : e.det≠0) (a : Fin 6) :
    (sourceVelocityHessian e).mulVec (fun i=>sourceLorentzTemporalVelocity e a i.1 i.2)=0:=by
  rw [sourceVelocityHessian,←Matrix.mulVec_mulVec,sourceLorentzTemporalLoad_matrix,←Matrix.mulVec_mulVec]
  have actual : (sourceLorentzInverse e).mulVec
      ((sourceLorentzHessian e).mulVec (fun i=>sourceConnectionBasis (0,a) i.1 i.2))=
      (fun i=>sourceConnectionBasis (0,a) i.1 i.2):=by
    rw [Matrix.mulVec_mulVec,sourceLorentzInverse_left e nondegenerate,Matrix.one_mulVec]
  rw [actual]
  funext i
  simp [Matrix.mulVec,dotProduct,Matrix.transpose_apply,sourceConnectionBasis,sourceVelocityMatrix_timeRow]

theorem sourceVelocityMomentum_pairing (u : JointParameter) (e : LorentzianCoframe)
    (de : Fin 4→LorentzianCoframe) (v w : LorentzianCoframe) :
    (∑i : CoframeIndex,sourceCoframeVelocityMomentum u e de v i*w i.1 i.2)=
      ∑k : LorentzIndex,sourceCoframeVelocityLoad e w k*
        sourceResolvedLorentzConnection u e (de+sourceTemporalJet v) k.1 k.2:=by
  rw [sourceVelocityMatrix_generated]
  simp only [sourceCoframeVelocityMomentum,Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceLorentzMomentum_nativePrimary (u : JointParameter) (e : LorentzianCoframe)
    (nondegenerate : e.det≠0) (de : Fin 4→LorentzianCoframe) (v : LorentzianCoframe) (a : Fin 6) :
    (∑i : CoframeIndex,sourceCoframeVelocityMomentum u e de v i*sourceLorentzTemporalVelocity e a i.1 i.2)+
      sourceLorentzOriginalLoad u e de (0,a)=0:=by
  rw [sourceVelocityMomentum_pairing]
  simp_rw [sourceLorentzTemporalLoad_native,sourceLorentzHessian_symmetric e _ (0,a)]
  have euler:=congrFun (sourceResolvedLorentzConnection_euler u e nondegenerate (de+sourceTemporalJet v)) (0,a)
  simp only [sourceLorentzEulerResidual,Pi.add_apply,Pi.zero_apply,Matrix.mulVec,dotProduct] at euler
  have temporal : sourceCoframeVelocityLoad e v (0,a)=0:=by
    rw [sourceVelocityMatrix_generated]
    simp only [Matrix.mulVec,dotProduct,sourceVelocityMatrix_timeRow,zero_mul,Finset.sum_const_zero]
  rw [sourceTemporalLoad_add] at euler
  simp only [Pi.add_apply,temporal,add_zero] at euler
  exact euler

end LowEnergy.PreparationVacuumCoframeLegendreSource
