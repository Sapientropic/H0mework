import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeGaugeAction
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceStaticInterval

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumRestModeCoupling
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

open Filter
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

open PreparationVacuumStaticPoleResponse PreparationVacuumFullOriginResponse

def sourceModeSample (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ:=
  pairSample z (a z) (sourceModeFiber z (b z))

def sourceModeForm (a b : QuantumTest) : ℂ:=∫z,sourceModeSample a b z ∂GaussHistoryHilbert.configurationMeasure

private theorem pair_sub (z : SourceCoordinateSlice) (u v w : FockFiber) :
    pairSample z u (v-w)=pairSample z u v-pairSample z u w:=by
  simp only [pairSample,WithLp.ofLp_sub,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

private theorem raw_integrable (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (fun z=>rawSample reader p a b (0,z)) GaussHistoryHilbert.configurationMeasure:=by
  apply parameter_slice_integrable _ (tsupport a) a.hasCompactSupport 0
    (fun z=>rawSample_near_smooth reader p a b 0 z (by simpa only [norm_zero] using ambientRadius_positive a))
    (rawSample_zero reader p a b)

theorem sourceModeSample_generated (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    rawSample (gaugeField 1 0) p a b (0,z)-rawSample (gaugeField 2 1) p a b (0,z)=sourceModeSample a b z:=by
  by_cases inside : z∈tsupport a
  · have h:=sourceModeFiber_generated p ⟨z,a.tsupport_subset inside⟩
    unfold rawSample sourceModeSample
    rw [rawFiber_zero,rawFiber_zero,←h]
    exact (pair_sub z _ _ _).symm
  · rw [rawSample_zero _ _ _ _ _ _ inside,rawSample_zero _ _ _ _ _ _ inside]
    simp only [sub_self,sourceModeSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem sourceModeForm_generated (p : PhysicalMomentum) (a b : QuantumTest) :
    rawForm (gaugeField 1 0) p a b 0-rawForm (gaugeField 2 1) p a b 0=sourceModeForm a b:=by
  unfold rawForm sourceModeForm
  rw [←integral_sub (raw_integrable _ _ _ _) (raw_integrable _ _ _ _)]
  exact integral_congr_ae (Eventually.of_forall (sourceModeSample_generated p a b))

def sourceModeReader (F : GaussUnitaryHistory.Index) : H→L[ℂ] H:=
  finiteRiesz F (fun i j=>sourceModeForm (frameTest F i) (frameTest F j))

attribute [local irreducible] frameVector frameTest rawForm sourceModeForm sourceModeReader
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _

theorem sourceModeReader_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    rawReader (gaugeField 1 0) p F 0-rawReader (gaugeField 2 1) p F 0=sourceModeReader F:=by
  unfold rawReader sourceModeReader finiteRiesz
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact (sub_smul (rawForm (gaugeField 1 0) p (frameTest F i) (frameTest F j) 0)
    (rawForm (gaugeField 2 1) p (frameTest F i) (frameTest F j) 0)
    (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))).symm.trans
      (congrArg (fun e : ℂ=>e • InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
        (sourceModeForm_generated p (frameTest F i) (frameTest F j)))

def sourceModeKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H:=
  SourceFiniteUnitary.time (actualC pL q.F) (-t)*CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*
    sourceModeReader q.F*CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w*
      SourceFiniteUnitary.time (actualC pR q.F) t

theorem sourceModeKernel_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    sourceGaugeZeroHistoryKernel q pL pR 1 0 t-sourceGaugeZeroHistoryKernel q pL pR 2 1 t=sourceModeKernel q pL pR t:=by
  have h:=congrArg (fun A : H→L[ℂ] H=>SourceFiniteUnitary.time (actualC pL q.F) (-t)*
    CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*A*CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w*
      SourceFiniteUnitary.time (actualC pR q.F) t) (sourceModeReader_generated pR q.F)
  simp only [mul_sub,sub_mul] at h
  exact h

def sourceModeCurrent (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ:=
  sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 1 0)-sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 2 1)

theorem sourceModeCurrent_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceModeCurrent q pL pR left right t=
      -sourcePoleRead q.epsilon q.precision pL pR left right (sourceModeKernel q pL pR t):=by
  have h:=congrArg (sourcePoleRead q.epsilon q.precision pL pR left right) (sourceModeKernel_generated q pL pR t)
  rw [map_sub] at h
  unfold sourceModeCurrent
  rw [sourceGaugeCurrent_zeroHistory q pL pR left right 1 0 t nonrealL nonrealR,
    sourceGaugeCurrent_zeroHistory q pL pR left right 2 1 t nonrealL nonrealR]
  linear_combination -h

theorem actualOriginWeight_sourceReader (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    actualOriginWeight q pL pR left right lambda T=
      -(3/10:ℂ)*rootTwo*∫t in (0:ℝ)..T,laplaceWeight lambda t*
        sourcePoleRead q.epsilon q.precision pL pR left right (sourceModeKernel q pL pR t):=by
  have continuous (i : Fin 289) : Continuous (fun t=>laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t i):=by
    have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
    exact weight.mul (sourcePoleActionEuler_continuous q pL pR left right i)
  have difference : (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceModeCurrent q pL pR left right t)=
      actualCurrent q pL pR left right lambda T 21-actualCurrent q pL pR left right lambda T 34:=by
    unfold sourceModeCurrent
    simp only [mul_sub]
    rw [show gaugeSlot 1 0=(21:Fin 289) from rfl,show gaugeSlot 2 1=(34:Fin 289) from rfl]
    rw [intervalIntegral.integral_sub ((continuous 21).intervalIntegrable 0 T) ((continuous 34).intervalIntegrable 0 T)]
    rfl
  rw [actualOriginWeight,←difference]
  simp_rw [sourceModeCurrent_generated q pL pR left right _ nonrealL nonrealR,mul_neg]
  rw [intervalIntegral.integral_neg]
  ring

theorem actualCurrent_staticResidue_modeReader (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    staticResidue (actualCurrent q pL pR left right lambda T)=fullNativeOrigin*ᵥ
      (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*
        (-(3/10:ℂ)*rootTwo*∫t in (0:ℝ)..T,laplaceWeight lambda t*
          sourcePoleRead q.epsilon q.precision pL pR left right (sourceModeKernel q pL pR t)))+
       Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*
        (-(3/10:ℂ)*rootTwo*∫t in (0:ℝ)..T,laplaceWeight lambda t*
          sourcePoleRead q.epsilon q.precision pL pR left right (sourceModeKernel q pL pR t)))):=by
  rw [actualCurrent_staticResidue,actualOriginWeight_sourceReader q pL pR left right lambda T nonrealL nonrealR]

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open Stage9C.Material.SpinPair Stage10 Stage10.CanonicalMatter
open Stage9DEF Stage9DEF.Compatibility Electromagnetic.ExternalState

/-- The homogeneous source rest-current read retains the original clock normalization and the complete charge transition. -/
theorem actualRestState_mode_charge_clock (point : BasePoint) (left right : RestStateIndex) :
    (lapse:ℂ)*((3/10:ℂ)*rootTwo*
      (2*actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
        (currentAction 1 (sourceColorP286Generator 1) (actualRestStatePreparation right (actual.matter point))))-
       2*actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
        (currentAction 2 (sourceColorP286Generator 0) (actualRestStatePreparation right (actual.matter point))))))=
      Complex.I*(sourceRestPoleEnergy (sourceRestStatePole left)-sourceRestPoleEnergy (sourceRestStatePole right))*
        actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
          (currentAction 0 (sourceColorP286Generator 2) (actualRestStatePreparation right (actual.matter point)))):=by
  rw [actualRestState_kernel_current,actualRestState_current_mixing]
  have scales : (lapse:ℂ)*(3/10:ℂ)*rootTwo=(frequency:ℂ)/2:=by
    rw [ChargedPreparation.Dynamics.frequency_gauge]
    unfold rootTwo gaugeScale spinScale
    push_cast
    ring
  calc
    _=((ActionNormalization.phaseMomentum:ℂ)/2)*((frequency:ℂ)*sourceKernelCurrentMixing left right):=by
      calc
        _=((lapse:ℂ)*(3/10:ℂ)*rootTwo)*((ActionNormalization.phaseMomentum:ℂ)*sourceKernelCurrentMixing left right):=by ring
        _= _:=by rw [scales];ring
    _= _:=by rw [sourceKernelCurrent_charge_commutator];ring

open PreparationVacuumPhysicalAbelZeroRead SourceJointResidualEnergy

def sourceModeStaticCoefficient (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (i j : Channel q.F) : ℂ:=
  -(((channelValue q.F i:ℂ)-q.z)⁻¹*((channelValue q.F j:ℂ)-q.w)⁻¹*
    inner ℂ (channel q.F i (sourcePolePrepared q.epsilon q.precision 0 left))
      (sourceModeReader q.F (channel q.F j (sourcePolePrepared q.epsilon q.precision 0 right))))

theorem sourceModeStaticCoefficient_generated (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (i j : Channel q.F) : sourceStaticCoefficient q left right 1 0 i j-sourceStaticCoefficient q left right 2 1 i j=
      sourceModeStaticCoefficient q left right i j:=by
  have h:=congrArg (fun A : H→L[ℂ] H=>inner ℂ (channel q.F i (sourcePolePrepared q.epsilon q.precision 0 left))
    (A (channel q.F j (sourcePolePrepared q.epsilon q.precision 0 right)))) (sourceModeReader_generated 0 q.F)
  simp only [sub_apply,inner_sub_right] at h
  unfold sourceStaticCoefficient sourceModeStaticCoefficient
  rw [←h]
  ring

def sourceModeStaticResidue (q : PhysicalResponsePoint) (left right : RestStateIndex) : ℂ:=
  ∑i : Channel q.F,∑j : Channel q.F,
    if channelValue q.F i=channelValue q.F j then sourceModeStaticCoefficient q left right i j else 0

theorem sourceModeStaticResidue_generated (q : PhysicalResponsePoint) (left right : RestStateIndex) :
    sourceStaticResidue q left right 1 0-sourceStaticResidue q left right 2 1=sourceModeStaticResidue q left right:=by
  unfold sourceStaticResidue sourceModeStaticResidue
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · exact sourceModeStaticCoefficient_generated q left right i j
  · ring

def sourceModeHalfWeight (q : PhysicalResponsePoint) (left right : RestStateIndex) (eta : ℝ) : ℂ:=
  (3/10:ℂ)*rootTwo*(sourcePoleCurrentHalf q 0 0 left right (eta:ℂ) (gaugeSlot 1 0)-
    sourcePoleCurrentHalf q 0 0 left right (eta:ℂ) (gaugeSlot 2 1))

theorem sourceModeHalfWeight_Abel (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*sourceModeHalfWeight q left right eta) (𝓝[>] (0:ℝ))
      (𝓝 ((3/10:ℂ)*rootTwo*sourceModeStaticResidue q left right)):=by
  have h:=((sourceActualStaticHalf_Abel_zero q left right 1 0 nonrealL nonrealR).sub
    (sourceActualStaticHalf_Abel_zero q left right 2 1 nonrealL nonrealR)).const_mul ((3/10:ℂ)*rootTwo)
  rw [sourceModeStaticResidue_generated] at h
  convert h using 1
  ext eta
  unfold sourceModeHalfWeight
  ring

theorem sourceModeHalfWeight_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (eta : ℝ) (positive : 0<eta) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖(eta:ℂ)*sourceModeHalfWeight q left right eta-(3/10:ℂ)*rootTwo*sourceModeStaticResidue q left right‖ ≤
      ‖(3/10:ℂ)*rootTwo‖*eta*(sourceStaticErrorPrice q left right 1 0+sourceStaticErrorPrice q left right 2 1):=by
  have first:=sourceActualStaticHalf_controlled q left right 1 0 eta positive nonrealL nonrealR
  have second:=sourceActualStaticHalf_controlled q left right 2 1 eta positive nonrealL nonrealR
  have factor : (eta:ℂ)*sourceModeHalfWeight q left right eta-(3/10:ℂ)*rootTwo*sourceModeStaticResidue q left right=
      ((3/10:ℂ)*rootTwo)*
      (((eta:ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta:ℂ) (gaugeSlot 1 0)-sourceStaticResidue q left right 1 0)-
       ((eta:ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta:ℂ) (gaugeSlot 2 1)-sourceStaticResidue q left right 2 1)):=by
    rw [←sourceModeStaticResidue_generated]
    unfold sourceModeHalfWeight
    ring
  rw [factor,norm_mul]
  calc
    _ ≤ ‖(3/10:ℂ)*rootTwo‖*(‖(eta:ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta:ℂ) (gaugeSlot 1 0)-sourceStaticResidue q left right 1 0‖+
        ‖(eta:ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta:ℂ) (gaugeSlot 2 1)-sourceStaticResidue q left right 2 1‖):=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖(3/10:ℂ)*rootTwo‖*(eta*sourceStaticErrorPrice q left right 1 0+eta*sourceStaticErrorPrice q left right 2 1):=
      mul_le_mul_of_nonneg_left (add_le_add first second) (norm_nonneg _)
    _= _:=by ring

end LowEnergy.PreparationVacuumRestModeCoupling
