import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargeTimeAbel
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceModeCurrent

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalChargeTimeZero
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
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore




open scoped ContDiff



open PreparationVacuumPhysicalGaussColorTorque



open FullQuantum
open scoped Matrix.Norms.L2Operator

local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace




open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumActionDecomposition
open CanonicalPhysicalSpatial






open PreparationVacuumPhysicalN1MaterialWard

open PreparationVacuumPhysicalNativeColourReturn SourceJointResidualEnergy

private theorem weighted_remainder (w c j k q r d : ℂ) (h : c*(j-k)=q+Complex.I*r-d) :
    c*(w*j-w*k)-w*q=w*(Complex.I*r-d) := by
  calc
    _=w*(c*(j-k)-q) := by ring
    _=w*(Complex.I*r-d) := by rw [h];ring

def sourceGaussRemainderHalf (q : PhysicalResponsePoint) (left right : RestStateIndex) (lambda : ℂ) : ℂ :=
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t*
    (Complex.I*sourceColourContactRemainderRead q 0 0 left right t-sourceDeviationJointRead q 0 0 left right t)

private theorem actual_weighted_remainder (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (gaugeScale/2 : ℝ) •
      (laplaceWeight lambda t*sourcePoleActionEuler q 0 0 left right 0 t (gaugeSlot 1 0)-
        laplaceWeight lambda t*sourcePoleActionEuler q 0 0 left right 0 t (gaugeSlot 2 1))-
      laplaceWeight lambda t*sourceConstraintChargeFirst q 0 0 left right t=
    laplaceWeight lambda t*
      (Complex.I*sourceColourContactRemainderRead q 0 0 left right t-sourceDeviationJointRead q 0 0 left right t) := by
  have h:=sourceActualMode_completeGauss q 0 0 left right t nonrealL nonrealR
  simp only [Complex.real_smul] at h ⊢
  exact weighted_remainder _ _ _ _ _ _ _ h

theorem sourceGaussRemainder_integrable (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    IntegrableOn (fun t=>laplaceWeight lambda t*
      (Complex.I*sourceColourContactRemainderRead q 0 0 left right t-sourceDeviationJointRead q 0 0 left right t)) (Ioi 0) := by
  have current:=((sourcePoleCurrent_integrable q 0 0 left right lambda off (gaugeSlot 1 0)).sub
    (sourcePoleCurrent_integrable q 0 0 left right lambda off (gaugeSlot 2 1))).smul (gaugeScale/2 : ℝ)
  exact (current.sub (sourceChargeTime_integrable q left right lambda off nonrealL nonrealR)).congr
    (Eventually.of_forall (fun t=>actual_weighted_remainder q left right lambda t nonrealL nonrealR))

theorem sourceGaussRemainderHalf_generated (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceGaussRemainderHalf q left right lambda=
      (gaugeScale/2 : ℝ) • (sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 1 0)-
        sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 2 1))-
      sourceChargeTimeHalf q left right lambda := by
  have i1:=sourcePoleCurrent_integrable q 0 0 left right lambda off (gaugeSlot 1 0)
  have i2:=sourcePoleCurrent_integrable q 0 0 left right lambda off (gaugeSlot 2 1)
  have current : IntegrableOn (fun t=>(gaugeScale/2 : ℝ) •
      (laplaceWeight lambda t*sourcePoleActionEuler q 0 0 left right 0 t (gaugeSlot 1 0)-
        laplaceWeight lambda t*sourcePoleActionEuler q 0 0 left right 0 t (gaugeSlot 2 1))) (Ioi 0) := by
    exact ((i1.sub i2).smul (gaugeScale/2 : ℝ)).congr (Eventually.of_forall (fun _=>rfl))
  unfold sourceGaussRemainderHalf
  rw [show (fun t=>laplaceWeight lambda t*(Complex.I*sourceColourContactRemainderRead q 0 0 left right t-
      sourceDeviationJointRead q 0 0 left right t))=
      (fun t=>(gaugeScale/2 : ℝ) • (laplaceWeight lambda t*sourcePoleActionEuler q 0 0 left right 0 t (gaugeSlot 1 0)-
        laplaceWeight lambda t*sourcePoleActionEuler q 0 0 left right 0 t (gaugeSlot 2 1))-
      laplaceWeight lambda t*sourceConstraintChargeFirst q 0 0 left right t) from
        funext (fun t=>(actual_weighted_remainder q left right lambda t nonrealL nonrealR).symm)]
  rw [integral_sub current (sourceChargeTime_integrable q left right lambda off nonrealL nonrealR),
    integral_smul,integral_sub i1 i2]
  rfl

theorem sourceGaussRemainderHalf_Abel (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta : ℂ)*sourceGaussRemainderHalf q left right (eta : ℂ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (((gaugeScale/2 : ℝ) : ℂ)*sourceModeStaticResidue q left right)) := by
  have h:=(((sourceActualStaticHalf_Abel_zero q left right 1 0 nonrealL nonrealR).sub
    (sourceActualStaticHalf_Abel_zero q left right 2 1 nonrealL nonrealR)).const_mul ((gaugeScale/2 : ℝ) : ℂ)).sub
      (sourceActualChargeTimeHalf_Abel_zero q left right nonrealL nonrealR)
  rw [sourceModeStaticResidue_generated,sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with eta positive
  rw [sourceGaussRemainderHalf_generated q left right (eta : ℂ)
    (by simpa only [Complex.ofReal_re] using (show 0<eta from positive)) nonrealL nonrealR]
  simp only [Complex.real_smul]
  ring

def sourceGaussRemainderPrice (q : PhysicalResponsePoint) (left right : RestStateIndex) : ℝ :=
  ‖((gaugeScale/2 : ℝ) : ℂ)‖*(sourceStaticErrorPrice q left right 1 0+sourceStaticErrorPrice q left right 2 1)+
    sourceChargeTimePrice q left right

theorem sourceGaussRemainderHalf_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (eta : ℝ) (positive : 0<eta) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖(eta : ℂ)*sourceGaussRemainderHalf q left right (eta : ℂ)-
      ((gaugeScale/2 : ℝ) : ℂ)*sourceModeStaticResidue q left right‖ ≤
      eta*sourceGaussRemainderPrice q left right := by
  have first:=sourceActualStaticHalf_controlled q left right 1 0 eta positive nonrealL nonrealR
  have second:=sourceActualStaticHalf_controlled q left right 2 1 eta positive nonrealL nonrealR
  have time:=sourceActualChargeTimeHalf_controlled q left right eta positive nonrealL nonrealR
  have factor : (eta : ℂ)*sourceGaussRemainderHalf q left right (eta : ℂ)-
      ((gaugeScale/2 : ℝ) : ℂ)*sourceModeStaticResidue q left right=
      ((gaugeScale/2 : ℝ) : ℂ)*
        (((eta : ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta : ℂ) (gaugeSlot 1 0)-sourceStaticResidue q left right 1 0)-
          ((eta : ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta : ℂ) (gaugeSlot 2 1)-sourceStaticResidue q left right 2 1))-
        (eta : ℂ)*sourceChargeTimeHalf q left right (eta : ℂ) := by
    rw [sourceGaussRemainderHalf_generated q left right (eta : ℂ)
      (by simpa only [Complex.ofReal_re] using positive) nonrealL nonrealR,←sourceModeStaticResidue_generated]
    simp only [Complex.real_smul]
    ring
  rw [factor]
  apply (norm_sub_le _ _).trans
  have price: ‖((eta : ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta : ℂ) (gaugeSlot 1 0)-sourceStaticResidue q left right 1 0)-
      ((eta : ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta : ℂ) (gaugeSlot 2 1)-sourceStaticResidue q left right 2 1)‖ ≤
      eta*sourceStaticErrorPrice q left right 1 0+eta*sourceStaticErrorPrice q left right 2 1 :=
    (norm_sub_le _ _).trans (add_le_add first second)
  rw [norm_mul]
  exact (add_le_add (mul_le_mul_of_nonneg_left price (norm_nonneg _)) time).trans_eq (by
    unfold sourceGaussRemainderPrice
    ring)

private theorem frequency_initial (lambda frequency c : ℂ) (nonzero : lambda-frequency≠0) :
    (lambda-frequency)⁻¹*(frequency*c)=lambda*((lambda-frequency)⁻¹*c)-c := by
  field_simp
  ring

private theorem primitive_half_channels (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    constraintChargeRead (sourcePoleCurrentHalf q 0 0 left right lambda)=
      ∑i : Channel q.F,∑j : Channel q.F,
        (sourceStaticDenominator q.F i j lambda)⁻¹*sourceColorStaticCoefficient q left right 0 i j := by
  change (sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 0 6)-
    sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 0 7))/2=_
  rw [sourceStaticHalf_generated q left right 0 6 lambda off nonrealL nonrealR,
    sourceStaticHalf_generated q left right 0 7 lambda off nonrealL nonrealR]
  unfold sourceStaticAbel
  rw [←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [←sourceColorStaticCoefficient_generated]
  ring

theorem sourceChargeTimeHalf_initial (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceChargeTimeHalf q left right lambda=
      lambda*constraintChargeRead (sourcePoleCurrentHalf q 0 0 left right lambda)-
        sourceConstraintCharge q 0 0 left right 0 := by
  have initial : sourceConstraintCharge q 0 0 left right 0=
      ∑i : Channel q.F,∑j : Channel q.F,sourceColorStaticCoefficient q left right 0 i j := by
    rw [sourceConstraintCharge_color,sourceColorCurrent_channels q left right 0 0 nonrealL nonrealR]
    simp only [sourceStaticPhase_exp,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]
  rw [sourceChargeTimeHalf_generated q left right lambda off nonrealL nonrealR,
    primitive_half_channels q left right lambda off nonrealL nonrealR,initial]
  unfold sourceChargeTimeAbel
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have nonzero : sourceStaticDenominator q.F i j lambda≠0 := by
    intro zero
    have real:=congrArg Complex.re zero
    simp only [sourceStaticDenominator,Complex.sub_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Complex.zero_re] at real
    exact off.ne' real
  exact frequency_initial lambda (Complex.I*(sourceStaticGap q.F i j : ℂ))
    (sourceColorStaticCoefficient q left right 0 i j) nonzero

theorem sourceGaussRemainderHalf_initial (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceGaussRemainderHalf q left right lambda=
      (gaugeScale/2 : ℝ) • (sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 1 0)-
        sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 2 1))-
      lambda*constraintChargeRead (sourcePoleCurrentHalf q 0 0 left right lambda)+
        sourceConstraintCharge q 0 0 left right 0 := by
  rw [sourceGaussRemainderHalf_generated q left right lambda off nonrealL nonrealR,
    sourceChargeTimeHalf_initial q left right lambda off nonrealL nonrealR]
  abel_nf

end LowEnergy.PreparationVacuumPhysicalChargeTimeZero
