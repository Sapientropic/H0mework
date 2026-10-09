import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticGaussResidue

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

def sourceNonzeroGapSet (F : GaussUnitaryHistory.Index) : Finset ℝ :=
  insert 1 ((Finset.univ.filter (fun pair : Channel F×Channel F=>sourceStaticGap F pair.1 pair.2≠0)).image
    (fun pair=>|sourceStaticGap F pair.1 pair.2|))

private theorem gapSet_nonempty (F : GaussUnitaryHistory.Index) : (sourceNonzeroGapSet F).Nonempty :=
  Finset.insert_nonempty _ _

def sourceGapRadius (F : GaussUnitaryHistory.Index) : ℝ :=
  (sourceNonzeroGapSet F).min' (gapSet_nonempty F)/2

theorem sourceGapRadius_positive (F : GaussUnitaryHistory.Index) : 0<sourceGapRadius F := by
  classical
  apply div_pos _ (by norm_num : (0 : ℝ)<2)
  have member:=Finset.min'_mem (sourceNonzeroGapSet F) (gapSet_nonempty F)
  rcases Finset.mem_insert.mp member with one|inside
  · rw [one]
    norm_num
  · rcases Finset.mem_image.mp inside with ⟨pair,hpair,value⟩
    rw [←value]
    exact abs_pos.mpr (Finset.mem_filter.mp hpair).2

theorem sourceGapRadius_gap (F : GaussUnitaryHistory.Index) (i j : Channel F)
    (different : sourceStaticGap F i j≠0) :
    2*sourceGapRadius F ≤ |sourceStaticGap F i j| := by
  classical
  have member : |sourceStaticGap F i j|∈sourceNonzeroGapSet F :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,different⟩,rfl⟩)
  have minimum:=Finset.min'_le (sourceNonzeroGapSet F) |sourceStaticGap F i j| member
  unfold sourceGapRadius
  linarith

theorem sourceSmall_denominator (F : GaussUnitaryHistory.Index) (i j : Channel F) (lambda : ℂ)
    (small : ‖lambda‖<sourceGapRadius F) (different : sourceStaticGap F i j≠0) :
    |sourceStaticGap F i j|/2 ≤ ‖sourceStaticDenominator F i j lambda‖ := by
  have radius:=sourceGapRadius_gap F i j different
  have reverse:=norm_sub_norm_le (Complex.I*(sourceStaticGap F i j : ℂ)) lambda
  rw [norm_sub_rev] at reverse
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at reverse
  unfold sourceStaticDenominator
  linarith

theorem sourceSmall_abelFactor_price (F : GaussUnitaryHistory.Index) (i j : Channel F) (lambda : ℂ)
    (small : ‖lambda‖<sourceGapRadius F) (different : sourceStaticGap F i j≠0) :
    ‖lambda*(sourceStaticDenominator F i j lambda)⁻¹‖ ≤ 2*‖lambda‖/|sourceStaticGap F i j| := by
  have denominator:=sourceSmall_denominator F i j lambda small different
  rw [norm_mul,norm_inv,←div_eq_mul_inv]
  exact (div_le_div_of_nonneg_left (norm_nonneg lambda)
    (div_pos (abs_pos.mpr different) (by norm_num : (0 : ℝ)<2)) denominator).trans_eq (by ring)

theorem sourceSmall_frequencyFactor_price (F : GaussUnitaryHistory.Index) (i j : Channel F) (lambda : ℂ)
    (small : ‖lambda‖<sourceGapRadius F) :
    ‖(sourceStaticDenominator F i j lambda)⁻¹*(Complex.I*(sourceStaticGap F i j : ℂ))‖ ≤ 2 := by
  by_cases different : sourceStaticGap F i j≠0
  · have denominator:=sourceSmall_denominator F i j lambda small different
    rw [norm_mul,norm_inv,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      mul_comm,←div_eq_mul_inv]
    exact (div_le_div_of_nonneg_left (abs_nonneg _)
      (div_pos (abs_pos.mpr different) (by norm_num : (0 : ℝ)<2)) denominator).trans_eq
        (by field_simp)
  · simp only [not_ne_iff.mp different,Complex.ofReal_zero,mul_zero,norm_zero]
    norm_num

end LowEnergy.PreparationVacuumPhysicalCausalZeroRead
