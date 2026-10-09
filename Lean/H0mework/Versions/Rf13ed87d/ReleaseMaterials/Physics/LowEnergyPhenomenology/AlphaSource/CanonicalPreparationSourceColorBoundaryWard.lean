import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceColorPreparedWard

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalColorWard
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

attribute [local irreducible] sourceColorReader sourcePolePrepared sourceHamiltonian

def sourceColorFullKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H :=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*sourceColorReader 0 q.F*
    jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

def sourceColorFullKernelJet (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : SourceJet (H→L[ℂ] H) :=
  jetMul (jetMul (jetMul (jetMul (physicalTimeJet pL q.F 0 (-1) 0 t)
    (jetConst (jointResolvent pL q.F q.z 0))) (jetConst (sourceColorReader 0 q.F)))
      (jetConst (jointResolvent pR q.F q.w 0))) (physicalTimeJet pR q.F 0 1 0 t)

def sourceColorFullJet (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : SourceJet ℂ :=
  negativeJet (pairJet (sourcePolePrepared q.epsilon q.precision pL left)
    (sourcePolePrepared q.epsilon q.precision pR right) (sourceColorFullKernelJet q pL pR t))

theorem sourceColorFullJet_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : HasSourceJets (sourceColorFullJet q pL pR left right) t :=
  negativeJets_generated _ _ (pairJets_generated _ _ _ _
    (productJets _ _ t (productJets _ _ t (productJets _ _ t (productJets _ _ t
      (physicalTimeJet_generated _ _ _ _ _ _) (constantJets _ _)) (constantJets _ _))
      (constantJets _ _)) (physicalTimeJet_generated _ _ _ _ _ _)))

private theorem half_word {B : Type*} [Ring B] [Algebra ℝ B] (L R X Y : B) :
    (1/2 : ℝ) • (L*X*R-L*Y*R)=L*((1/2 : ℝ) • (X-Y))*R := by
  simp only [mul_sub,sub_mul,smul_sub,smul_mul_assoc,mul_smul_comm]

theorem sourceColorFullKernel_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    (1/2 : ℝ) • (fiveKernel (gaugeField 0 6) pR (pL-pR) q.F q.z q.w t 0-
      fiveKernel (gaugeField 0 7) pR (pL-pR) q.F q.z q.w t 0)=sourceColorFullKernel q pL pR t := by
  have momentum : pR+(pL-pR)=pL:=by ext i;simp
  unfold fiveKernel sourceColorFullKernel
  rw [momentum,←sourceColorReader_generated 0 pR q.F]
  simpa only [mul_assoc] using half_word (B:=H→L[ℂ] H)
    (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0)
    (jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0) _ _

private theorem negative_half_read {B : Type*} [AddCommGroup B] [Module ℝ B]
    (L : B→ₗ[ℝ] ℂ) (X Y Z : B) (source : (1/2 : ℝ) • (X-Y)=Z) :
    (-L X-(-L Y))/2= -L Z := by
  rw [←source,map_smul,map_sub,Complex.real_smul]
  norm_num
  ring

theorem sourceColorFullJet_value (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) :
    (sourceColorFullJet q pL pR left right t).value=sourceConstraintCharge q pL pR left right t := by
  have value : (sourceColorFullKernelJet q pL pR t).value=sourceColorFullKernel q pL pR t := by
    simp only [sourceColorFullKernelJet,sourceColorFullKernel,jetMul,jetConst,physicalTimeJet,timeJet,
      neg_one_mul,one_mul,add_zero,physicalTime]
  change -inner ℂ (sourcePolePrepared q.epsilon q.precision pL left)
    ((sourceColorFullKernelJet q pL pR t).value (sourcePolePrepared q.epsilon q.precision pR right))=_
  rw [value,←sourcePoleRead_actual]
  unfold sourceConstraintCharge constraintChargeRead
  dsimp only
  rw [sourcePoleActionEuler_source,sourcePoleActionEuler_source]
  change -sourcePoleRead q.epsilon q.precision pL pR left right (sourceColorFullKernel q pL pR t)=
    (-sourcePoleRead q.epsilon q.precision pL pR left right (fiveKernel (gaugeField 0 6) pR (pL-pR) q.F q.z q.w t 0)-
      (-sourcePoleRead q.epsilon q.precision pL pR left right (fiveKernel (gaugeField 0 7) pR (pL-pR) q.F q.z q.w t 0)))/2
  exact (negative_half_read ((sourcePoleRead q.epsilon q.precision pL pR left right).toLinearMap.restrictScalars ℝ)
    _ _ _ (sourceColorFullKernel_generated q pL pR t)).symm

private theorem bracket_slide {B : Type*} [Ring B] (L R J S T C D : B)
    (RC : R*C=C*R) (SD : S*D=D*S) (TD : T*D=D*T) :
    L*C*R*J*S*T-L*R*J*S*T*D=L*R*(C*J-J*D)*S*T := by
  have left : L*C*R*J*S*T=L*R*C*J*S*T := by
    simpa only [mul_assoc] using congrArg (fun X=>L*X*J*S*T) RC.symm
  have right : L*R*J*S*T*D=L*R*J*D*S*T := by
    calc
      _=L*R*J*S*(T*D):=by simp only [mul_assoc]
      _=L*R*J*S*(D*T):=by rw [TD]
      _=L*R*J*(S*D)*T:=by simp only [mul_assoc]
      _=L*R*J*(D*S)*T:=by rw [SD]
      _=_:=by simp only [mul_assoc]
  rw [left,right]
  simp only [mul_sub,sub_mul,mul_assoc]

private theorem bracket_derivative {B : Type*} [Ring B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] (L R J S T C D : B)
    (RC : R*C=C*R) (SD : S*D=D*S) (TD : T*D=D*T) :
    (Complex.I • (L*C))*R*J*S*T+L*R*J*S*((-Complex.I) • (T*D))=
      Complex.I • (L*R*(C*J-J*D)*S*T) := by
  simp only [smul_mul_assoc,mul_smul_comm]
  rw [neg_smul,←sub_eq_add_neg,←smul_sub]
  simpa only [mul_assoc] using congrArg (fun X=>Complex.I • X) (bracket_slide L R J S T C D RC SD TD)

theorem sourceColorFullKernelJet_first (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (sourceColorFullKernelJet q pL pR t).first=
      Complex.I • (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
        sourceColorInsertion q pL pR*jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0) := by
  have h:=bracket_derivative (physicalTime pL q.F (-t) 0) (jointResolvent pL q.F q.z 0)
    (sourceColorReader 0 q.F) (jointResolvent pR q.F q.w 0) (physicalTime pR q.F t 0)
    (sourceHamiltonian pL q.F) (sourceHamiltonian pR q.F)
    (sourceResolvent_commutes pL q.F q.z nonrealL) (sourceResolvent_commutes pR q.F q.w nonrealR)
    (sourceTime_commutes pR q.F t)
  simpa only [sourceColorFullKernelJet,sourceColorInsertion,jetMul,jetConst,physicalTimeJet,timeJet,
    physicalTime,sourceHamiltonian,neg_one_mul,one_mul,add_zero,mul_zero,zero_mul,zero_add,
    neg_one_smul,mul_smul_comm,neg_smul,one_smul,neg_neg] using h

/-- The actual source row is read after the complete Gauss action torque and all four source defects. -/
def sourceActualColorWardRead (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ :=
  -Complex.I*((sourcePoleDual q.epsilon q.precision pL left).comp
    (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0))
      (sourceColorWardReturn q pL pR (jointResolvent pR q.F q.w 0
        (physicalTime pR q.F t 0 (sourcePolePrepared q.epsilon q.precision pR right))))

theorem sourceConstraintChargeFirst_actualWard (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceConstraintChargeFirst q pL pR left right t=sourceActualColorWardRead q pL pR left right t := by
  have h:=(sourceColorFullJet_generated q pL pR left right t).1
  simp only [sourceColorFullJet_value] at h
  have first:=(sourceConstraintCharge_derivative q pL pR left right t).unique h
  rw [first]
  change -inner ℂ (sourcePolePrepared q.epsilon q.precision pL left)
    ((sourceColorFullKernelJet q pL pR t).first (sourcePolePrepared q.epsilon q.precision pR right))=_
  rw [sourceColorFullKernelJet_first q pL pR t nonrealL nonrealR]
  simp only [smul_apply,inner_smul_right,mul_apply_eq_comp,sourceColorInsertion_generated]
  unfold sourceActualColorWardRead
  rw [sourcePoleDual]
  simp only [ContinuousLinearMap.comp_apply,mul_apply_eq_comp,innerSL_apply_apply,neg_mul]

theorem sourceActualCosource114_actualWardBoundary (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceActualCurrentCosource q pL pR left right spatial lambda T 114=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceActualColorWardRead q pL pR left right t)+
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintCovariant q pL pR left right spatial t)-
        (laplaceWeight lambda T*sourceConstraintCharge q pL pR left right T-
          sourceConstraintCharge q pL pR left right 0) := by
  rw [sourceActualCosource114_chargeBoundary]
  simp_rw [sourceConstraintChargeFirst_actualWard q pL pR left right _ nonrealL nonrealR]

end LowEnergy.PreparationVacuumPhysicalColorWard
