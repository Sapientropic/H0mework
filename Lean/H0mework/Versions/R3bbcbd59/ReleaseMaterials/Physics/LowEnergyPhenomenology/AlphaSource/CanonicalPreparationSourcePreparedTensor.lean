import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingCarrier

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSharedPoleCarrier
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumRestModeCoupling PreparationVacuumPhysicalFeedback
open CanonicalGradedSpatialSource GaussCoreHilbert
open scoped BigOperators Matrix InnerProductSpace
attribute [local irreducible] sourcePolePrepared sourcePoleRead

theorem movingOverlap_left_unitary (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum) :
    (movingOverlap momentum).conjTranspose*movingOverlap momentum=1:=by
  ext left right
  have gram:=sourcePolePrepared_orthonormal epsilon precision momentum left right
  rw [movingOverlap_prepared epsilon precision momentum left,movingOverlap_prepared epsilon precision momentum right] at gram
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,sourcePolePrepared_orthonormal,
    mul_ite,mul_one,mul_zero] at gram
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at gram
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,starRingEnd_apply,mul_comm] using gram

theorem movingOverlap_right_unitary (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum) :
    movingOverlap momentum*(movingOverlap momentum).conjTranspose=1:=
  mul_eq_one_comm.mp (movingOverlap_left_unitary epsilon precision momentum)

def sourceTensor (epsilon : ℝ) (precision : 0<epsilon) (pL pR : PhysicalMomentum) (A : H→L[ℂ] H) :
    Matrix RestStateIndex RestStateIndex ℂ:=fun left right=>sourcePoleRead epsilon precision pL pR left right A

/-- All intermediate quantum dynamics remain inside A; the actual external state carrier is unchanged. -/
theorem sourceTensor_generated (epsilon : ℝ) (precision : 0<epsilon) (pL pR : PhysicalMomentum) (A : H→L[ℂ] H) :
    sourceTensor epsilon precision pL pR A=
      (movingOverlap pL).conjTranspose*sourceTensor epsilon precision 0 0 A*movingOverlap pR:=by
  ext left right
  simp only [sourceTensor,sourcePoleRead_actual]
  rw [movingOverlap_prepared epsilon precision pL left,movingOverlap_prepared epsilon precision pR right]
  simp only [map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,sourceTensor,sourcePoleRead_actual,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceTensor_same_carrier (epsilon : ℝ) (precision : 0<epsilon) (pL pR : PhysicalMomentum) (A : H→L[ℂ] H) :
    movingOverlap pL*sourceTensor epsilon precision pL pR A*(movingOverlap pR).conjTranspose=
      sourceTensor epsilon precision 0 0 A:=by
  rw [sourceTensor_generated]
  calc
    _=(movingOverlap pL*(movingOverlap pL).conjTranspose)*sourceTensor epsilon precision 0 0 A*
        (movingOverlap pR*(movingOverlap pR).conjTranspose):=by noncomm_ring
    _= _:=by rw [movingOverlap_right_unitary epsilon precision pL,movingOverlap_right_unitary epsilon precision pR,one_mul,mul_one]

def actualModeTensor (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    Matrix RestStateIndex RestStateIndex ℂ:=fun left right=>sourceModeCurrent q pL pR left right t

theorem actualModeTensor_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) : actualModeTensor q pL pR t=
      -((movingOverlap pL).conjTranspose*sourceTensor q.epsilon q.precision 0 0 (sourceModeKernel q pL pR t)*movingOverlap pR):=by
  rw [←sourceTensor_generated]
  ext left right
  exact sourceModeCurrent_generated q pL pR left right t nonrealL nonrealR

theorem actualModeTensor_same_carrier (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    movingOverlap pL*actualModeTensor q pL pR t*(movingOverlap pR).conjTranspose=
      -sourceTensor q.epsilon q.precision 0 0 (sourceModeKernel q pL pR t):=by
  rw [actualModeTensor_generated q pL pR t nonrealL nonrealR,←sourceTensor_generated,mul_neg,neg_mul,
    sourceTensor_same_carrier]

end LowEnergy.PreparationVacuumSharedPoleCarrier
