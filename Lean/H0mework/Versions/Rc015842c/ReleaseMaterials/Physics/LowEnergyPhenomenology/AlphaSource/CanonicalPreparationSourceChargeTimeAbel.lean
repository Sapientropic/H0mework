import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargeTimeSpectrum

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

private theorem phase_weighted (F : GaussUnitaryHistory.Index) (i j : Channel F) (lambda : ℂ) (t : ℝ) :
    laplaceWeight lambda t*sourceStaticPhase F i j t=
      Complex.exp (-(sourceStaticDenominator F i j lambda)*(t : ℂ)) := by
  rw [sourceStaticPhase_exp]
  unfold laplaceWeight sourceStaticDenominator
  rw [←Complex.exp_add]
  congr 1
  ring

private theorem phase_integrable (F : GaussUnitaryHistory.Index) (i j : Channel F)
    (lambda : ℂ) (off : 0<lambda.re) :
    IntegrableOn (fun t : ℝ=>laplaceWeight lambda t*sourceStaticPhase F i j t) (Ioi 0) := by
  simp_rw [phase_weighted]
  apply integrableOn_exp_mul_complex_Ioi _ 0
  simpa only [sourceStaticDenominator,Complex.neg_re,Complex.sub_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,neg_lt_zero] using off

private theorem phase_integral (F : GaussUnitaryHistory.Index) (i j : Channel F)
    (lambda : ℂ) (off : 0<lambda.re) :
    (∫t : ℝ in Ioi 0,laplaceWeight lambda t*sourceStaticPhase F i j t)=
      (sourceStaticDenominator F i j lambda)⁻¹ := by
  simp_rw [phase_weighted]
  rw [integral_exp_mul_complex_Ioi (show (-(sourceStaticDenominator F i j lambda)).re<0 from
    by simpa only [sourceStaticDenominator,Complex.neg_re,Complex.sub_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,neg_lt_zero] using off) 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,div_neg,neg_div,neg_neg,one_div]

def sourceChargeTimeHalf (q : PhysicalResponsePoint) (left right : RestStateIndex) (lambda : ℂ) : ℂ :=
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t*sourceConstraintChargeFirst q 0 0 left right t

def sourceChargeTimeAbel (q : PhysicalResponsePoint) (left right : RestStateIndex) (lambda : ℂ) : ℂ :=
  ∑i : Channel q.F,∑j : Channel q.F,
    (sourceStaticDenominator q.F i j lambda)⁻¹*sourceChargeTimeCoefficient q left right i j

theorem sourceChargeTime_integrable (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    IntegrableOn (fun t=>laplaceWeight lambda t*sourceConstraintChargeFirst q 0 0 left right t) (Ioi 0) := by
  simp_rw [sourceActualChargeFirst_channels q left right _ nonrealL nonrealR,Finset.mul_sum,←mul_assoc]
  exact integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>
    (phase_integrable q.F i j lambda off).mul_const _))

theorem sourceChargeTimeHalf_generated (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceChargeTimeHalf q left right lambda=sourceChargeTimeAbel q left right lambda := by
  unfold sourceChargeTimeHalf sourceChargeTimeAbel
  simp_rw [sourceActualChargeFirst_channels q left right _ nonrealL nonrealR,Finset.mul_sum,←mul_assoc]
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>
    (phase_integrable q.F i j lambda off).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _=>(phase_integrable q.F i j lambda off).mul_const _)]
  simp only [integral_mul_const,phase_integral q.F _ _ lambda off]

def sourceChargeTimePrice (q : PhysicalResponsePoint) (left right : RestStateIndex) : ℝ :=
  ∑i : Channel q.F,∑j : Channel q.F,‖sourceColorStaticCoefficient q left right 0 i j‖

theorem sourceChargeTimePrice_nonnegative (q : PhysicalResponsePoint) (left right : RestStateIndex) :
    0 ≤ sourceChargeTimePrice q left right := by
  unfold sourceChargeTimePrice
  exact Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))

private theorem frequency_price (eta d : ℝ) (positive : 0<eta) :
    ‖((eta : ℂ)-Complex.I*(d : ℂ))⁻¹*(Complex.I*(d : ℂ))‖≤1 := by
  have denominator : |d|≤‖(eta : ℂ)-Complex.I*(d : ℂ)‖ := by
    simpa only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,zero_mul,one_mul,zero_add,zero_sub,abs_neg] using
      Complex.abs_im_le_norm ((eta : ℂ)-Complex.I*(d : ℂ))
  have nonzero : (eta : ℂ)-Complex.I*(d : ℂ)≠0 := by
    intro zero
    have real:=congrArg Complex.re zero
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Complex.zero_re] at real
    exact positive.ne' real
  rw [norm_mul,norm_inv,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    mul_comm,←div_eq_mul_inv]
  exact (div_le_one (norm_pos_iff.mpr nonzero)).mpr denominator

theorem sourceChargeTimeAbel_price (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (eta : ℝ) (positive : 0<eta) :
    ‖sourceChargeTimeAbel q left right (eta : ℂ)‖ ≤ sourceChargeTimePrice q left right := by
  unfold sourceChargeTimeAbel sourceChargeTimePrice
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [sourceChargeTimeCoefficient,←mul_assoc,norm_mul]
  exact (mul_le_mul_of_nonneg_right (frequency_price eta (sourceStaticGap q.F i j) positive)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem sourceActualChargeTimeHalf_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (eta : ℝ) (positive : 0<eta) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖(eta : ℂ)*sourceChargeTimeHalf q left right (eta : ℂ)‖≤eta*sourceChargeTimePrice q left right := by
  rw [sourceChargeTimeHalf_generated q left right (eta : ℂ)
    (by simpa only [Complex.ofReal_re] using positive) nonrealL nonrealR,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  exact mul_le_mul_of_nonneg_left (sourceChargeTimeAbel_price q left right eta positive) positive.le

theorem sourceActualChargeTimeHalf_Abel_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta : ℂ)*sourceChargeTimeHalf q left right (eta : ℂ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℂ)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (g:=fun eta : ℝ=>eta*sourceChargeTimePrice q left right)
    (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with eta positive
    exact sourceActualChargeTimeHalf_controlled q left right eta positive nonrealL nonrealR
  · have eta : Tendsto (fun x : ℝ=>x) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul] using eta.mul_const (sourceChargeTimePrice q left right)

end LowEnergy.PreparationVacuumPhysicalChargeTimeZero
