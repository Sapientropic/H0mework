import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceColourPhysicalBalance

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

def sourceChargeTimeCoefficient (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (i j : Channel q.F) : ℂ :=
  Complex.I*(sourceStaticGap q.F i j : ℂ)*sourceColorStaticCoefficient q left right 0 i j

private theorem source_phase_derivative (F : GaussUnitaryHistory.Index) (i j : Channel F) (t : ℝ) :
    HasDerivAt (sourceStaticPhase F i j)
      (Complex.I*(sourceStaticGap F i j : ℂ)*sourceStaticPhase F i j t) t := by
  convert! (((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.const_mul
    (Complex.I*(sourceStaticGap F i j : ℂ))).cexp) using 1
  · funext x
    exact sourceStaticPhase_exp F i j x
  · simp [Complex.ofRealCLM,sourceStaticPhase_exp]
    ring

private theorem source_timeTerm_derivative (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (i j : Channel q.F) (t : ℝ) :
    HasDerivAt (fun s=>sourceStaticPhase q.F i j s*sourceColorStaticCoefficient q left right 0 i j)
      (sourceStaticPhase q.F i j t*sourceChargeTimeCoefficient q left right i j) t := by
  convert! (source_phase_derivative q.F i j t).mul_const (sourceColorStaticCoefficient q left right 0 i j) using 1
  unfold sourceChargeTimeCoefficient
  ring

theorem sourceActualChargeFirst_channels (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceConstraintChargeFirst q 0 0 left right t=
      ∑i : Channel q.F,∑j : Channel q.F,
        sourceStaticPhase q.F i j t*sourceChargeTimeCoefficient q left right i j := by
  have h : HasDerivAt
      (fun s=>∑i : Channel q.F,∑j : Channel q.F,
        sourceStaticPhase q.F i j s*sourceColorStaticCoefficient q left right 0 i j)
      (∑i : Channel q.F,∑j : Channel q.F,
        sourceStaticPhase q.F i j t*sourceChargeTimeCoefficient q left right i j) t := by
    convert! (HasDerivAt.sum (u:=Finset.univ) (fun i _=>HasDerivAt.sum (u:=Finset.univ)
      (fun j _=>source_timeTerm_derivative q left right i j t))) using 1
    funext s
    simp only [Finset.sum_apply]
  have value : sourceConstraintCharge q 0 0 left right=
      (fun s=>∑i : Channel q.F,∑j : Channel q.F,
        sourceStaticPhase q.F i j s*sourceColorStaticCoefficient q left right 0 i j) := by
    funext s
    rw [sourceConstraintCharge_color,sourceColorCurrent_channels q left right 0 s nonrealL nonrealR]
  rw [←value] at h
  exact (sourceConstraintCharge_derivative q 0 0 left right t).unique h

def sourceChargeTimeResidue (q : PhysicalResponsePoint) (left right : RestStateIndex) : ℂ :=
  ∑i : Channel q.F,∑j : Channel q.F,
    if channelValue q.F i=channelValue q.F j then sourceChargeTimeCoefficient q left right i j else 0

theorem sourceChargeTimeResidue_generated (q : PhysicalResponsePoint) (left right : RestStateIndex) :
    sourceChargeTimeResidue q left right=0 := by
  classical
  unfold sourceChargeTimeResidue
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with equalEnergy
  · simp only [sourceChargeTimeCoefficient,sourceStaticGap,equalEnergy,sub_self,
      Complex.ofReal_zero,mul_zero,zero_mul]
  · rfl

theorem sourceActualNativeChargeWard_channels (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceNativeJointRead q 0 0 left right t-Complex.I*sourceColourContactRemainderRead q 0 0 left right t=
      ∑i : Channel q.F,∑j : Channel q.F,
        sourceStaticPhase q.F i j t*sourceChargeTimeCoefficient q left right i j := by
  rw [←sourceConstraintChargeFirst_completeContact q 0 0 left right t nonrealL nonrealR,
    sourceActualChargeFirst_channels q left right t nonrealL nonrealR]

end LowEnergy.PreparationVacuumPhysicalChargeTimeZero
