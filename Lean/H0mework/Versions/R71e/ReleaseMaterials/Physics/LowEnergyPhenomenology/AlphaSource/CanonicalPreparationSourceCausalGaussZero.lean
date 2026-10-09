import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceComplexCurrentZero

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalCausalZeroRead
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

open PreparationVacuumPhysicalChargeTimeZero

theorem sourceComplexGaussHalf_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun lambda : ℂ=>lambda*sourceGaussRemainderHalf q left right lambda)
      (nhdsWithin 0 {lambda | 0<lambda.re})
      (𝓝 (((gaugeScale/2 : ℝ) : ℂ)*sourceModeStaticResidue q left right)) := by
  have h:=(((sourceComplexStaticHalf_zero q left right 1 0 nonrealL nonrealR).sub
    (sourceComplexStaticHalf_zero q left right 2 1 nonrealL nonrealR)).const_mul ((gaugeScale/2 : ℝ) : ℂ)).sub
      (sourceComplexChargeTimeHalf_zero q left right nonrealL nonrealR)
  rw [sourceModeStaticResidue_generated,sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with lambda off
  rw [sourceGaussRemainderHalf_generated q left right lambda off nonrealL nonrealR]
  simp only [Complex.real_smul]
  ring

theorem sourceComplexGaussHalf_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (small : ‖lambda‖<sourceGapRadius q.F)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖lambda*sourceGaussRemainderHalf q left right lambda-
      ((gaugeScale/2 : ℝ) : ℂ)*sourceModeStaticResidue q left right‖ ≤
      2*‖lambda‖*sourceGaussRemainderPrice q left right := by
  have first:=sourceComplexStaticHalf_controlled q left right 1 0 lambda off small nonrealL nonrealR
  have second:=sourceComplexStaticHalf_controlled q left right 2 1 lambda off small nonrealL nonrealR
  have time:=sourceComplexChargeTimeHalf_controlled q left right lambda off small nonrealL nonrealR
  have factor : lambda*sourceGaussRemainderHalf q left right lambda-
      ((gaugeScale/2 : ℝ) : ℂ)*sourceModeStaticResidue q left right=
      ((gaugeScale/2 : ℝ) : ℂ)*
        ((lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 1 0)-sourceStaticResidue q left right 1 0)-
          (lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 2 1)-sourceStaticResidue q left right 2 1))-
        lambda*sourceChargeTimeHalf q left right lambda := by
    rw [sourceGaussRemainderHalf_generated q left right lambda off nonrealL nonrealR,←sourceModeStaticResidue_generated]
    simp only [Complex.real_smul]
    ring
  rw [factor]
  apply (norm_sub_le _ _).trans
  have price: ‖(lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 1 0)-sourceStaticResidue q left right 1 0)-
      (lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 2 1)-sourceStaticResidue q left right 2 1)‖ ≤
      2*‖lambda‖*sourceStaticErrorPrice q left right 1 0+2*‖lambda‖*sourceStaticErrorPrice q left right 2 1 :=
    (norm_sub_le _ _).trans (add_le_add first second)
  rw [norm_mul]
  exact (add_le_add (mul_le_mul_of_nonneg_left price (norm_nonneg _)) time).trans_eq (by
    unfold sourceGaussRemainderPrice
    ring)

theorem sourceCausalGaussHalf_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (eta omega : ℝ) (positive : 0<eta)
    (small : ‖(eta : ℂ)-Complex.I*(omega : ℂ)‖<sourceGapRadius q.F)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖((eta : ℂ)-Complex.I*(omega : ℂ))*sourceGaussRemainderHalf q left right ((eta : ℂ)-Complex.I*(omega : ℂ))-
      ((gaugeScale/2 : ℝ) : ℂ)*sourceModeStaticResidue q left right‖ ≤
      2*‖(eta : ℂ)-Complex.I*(omega : ℂ)‖*sourceGaussRemainderPrice q left right :=
  sourceComplexGaussHalf_controlled q left right _
    (by simpa only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_im,zero_mul,mul_zero,sub_zero] using positive) small nonrealL nonrealR

private theorem constraint_half_seed (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    lambda*sourceConstraintHalf114 q 0 0 left right 0 lambda=
      lambda*sourceChargeTimeHalf q left right lambda+
      lambda*sourceConstraintCharge q 0 0 left right 0-
      ((3/10 : ℂ)*rootTwo)*lambda*
        (sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 1 0)-
          sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 2 1)) := by
  rw [sourceConstraintHalf114_generated]
  unfold constraintCovariantRead
  simp only [Pi.zero_apply,zero_mul,zero_add,zero_div]
  have initial:=sourceChargeTimeHalf_initial q left right lambda off nonrealL nonrealR
  change lambda*(lambda*constraintChargeRead (sourcePoleCurrentHalf q 0 0 left right lambda)+
    (3/10 : ℂ)*rootTwo*(sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 2 1)-
      sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 1 0)))=_
  have primitive : lambda*constraintChargeRead (sourcePoleCurrentHalf q 0 0 left right lambda)=
      sourceChargeTimeHalf q left right lambda+sourceConstraintCharge q 0 0 left right 0 :=
    sub_eq_iff_eq_add.mp initial.symm
  rw [primitive]
  ring

theorem sourceComplexConstraintHalf114_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun lambda : ℂ=>lambda*sourceConstraintHalf114 q 0 0 left right 0 lambda)
      (nhdsWithin 0 {lambda | 0<lambda.re})
      (𝓝 (-(((3/10 : ℂ)*rootTwo)*sourceModeStaticResidue q left right))) := by
  have id : Tendsto (fun lambda : ℂ=>lambda) (nhdsWithin 0 {lambda | 0<lambda.re}) (𝓝 (0 : ℂ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have charge:=(sourceComplexChargeTimeHalf_zero q left right nonrealL nonrealR).add
    (id.mul_const (sourceConstraintCharge q 0 0 left right 0))
  have mode:=((sourceComplexStaticHalf_zero q left right 1 0 nonrealL nonrealR).sub
    (sourceComplexStaticHalf_zero q left right 2 1 nonrealL nonrealR)).const_mul ((3/10 : ℂ)*rootTwo)
  rw [sourceModeStaticResidue_generated] at mode
  have h:=charge.sub mode
  simp only [zero_mul,add_zero,zero_sub] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with lambda off
  rw [constraint_half_seed q left right lambda off nonrealL nonrealR]
  ring

def sourceConstraintComplexPrice (q : PhysicalResponsePoint) (left right : RestStateIndex) : ℝ :=
  2*sourceChargeTimePrice q left right+‖sourceConstraintCharge q 0 0 left right 0‖+
    2*‖(3/10 : ℂ)*rootTwo‖*(sourceStaticErrorPrice q left right 1 0+sourceStaticErrorPrice q left right 2 1)

theorem sourceComplexConstraintHalf114_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (small : ‖lambda‖<sourceGapRadius q.F)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖lambda*sourceConstraintHalf114 q 0 0 left right 0 lambda+
      ((3/10 : ℂ)*rootTwo)*sourceModeStaticResidue q left right‖ ≤
      ‖lambda‖*sourceConstraintComplexPrice q left right := by
  have first:=sourceComplexStaticHalf_controlled q left right 1 0 lambda off small nonrealL nonrealR
  have second:=sourceComplexStaticHalf_controlled q left right 2 1 lambda off small nonrealL nonrealR
  have time:=sourceComplexChargeTimeHalf_controlled q left right lambda off small nonrealL nonrealR
  have factor : lambda*sourceConstraintHalf114 q 0 0 left right 0 lambda+
      ((3/10 : ℂ)*rootTwo)*sourceModeStaticResidue q left right=
      (lambda*sourceChargeTimeHalf q left right lambda+lambda*sourceConstraintCharge q 0 0 left right 0)-
      ((3/10 : ℂ)*rootTwo)*
        ((lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 1 0)-sourceStaticResidue q left right 1 0)-
          (lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 2 1)-sourceStaticResidue q left right 2 1)) := by
    rw [constraint_half_seed q left right lambda off nonrealL nonrealR,←sourceModeStaticResidue_generated]
    ring
  rw [factor]
  apply (norm_sub_le _ _).trans
  have charge: ‖lambda*sourceChargeTimeHalf q left right lambda+lambda*sourceConstraintCharge q 0 0 left right 0‖ ≤
      2*‖lambda‖*sourceChargeTimePrice q left right+‖lambda‖*‖sourceConstraintCharge q 0 0 left right 0‖ := by
    exact (norm_add_le _ _).trans (add_le_add time (by rw [norm_mul]))
  have price: ‖(lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 1 0)-sourceStaticResidue q left right 1 0)-
      (lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot 2 1)-sourceStaticResidue q left right 2 1)‖ ≤
      2*‖lambda‖*sourceStaticErrorPrice q left right 1 0+2*‖lambda‖*sourceStaticErrorPrice q left right 2 1 :=
    (norm_sub_le _ _).trans (add_le_add first second)
  rw [norm_mul]
  exact (add_le_add charge (mul_le_mul_of_nonneg_left price (norm_nonneg _))).trans_eq (by
    unfold sourceConstraintComplexPrice
    ring)

end LowEnergy.PreparationVacuumPhysicalCausalZeroRead
