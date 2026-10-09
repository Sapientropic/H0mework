import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceN1ColourContactReturn

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalNativeColourReturn
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

theorem sourceNativeSample_contactCore (p : PhysicalMomentum) (a b : QuantumTest) (x : SourceCoordinateSlice) :
    PreparationVacuumNativeLocalWard.nativeSample (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b (0,x)=
      densityPair a (sourceNativeContactCore p b) x := by
  rw [←pairSample_source]
  by_cases inside : x∈tsupport a
  · rw [PreparationVacuumNativeLocalWard.nativeSample,nativeJointFiber,nativeNoetherFiber,
      ambientState_zero,nativeNoether_source]
    rfl
  · rw [PreparationVacuumNativeLocalWard.nativeSample_zero _ _ _ _ _ _ _ _ inside]
    simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem sourceNativeContact_integrable (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (fun x=>PreparationVacuumNativeLocalWard.nativeSample (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b (0,x))
      GaussHistoryHilbert.configurationMeasure :=
  (densityPair_integrable a (sourceNativeContactCore p b)).congr
    (Eventually.of_forall (fun x=>(sourceNativeSample_contactCore p a b x).symm))

theorem sourceNativeForm_contactCore (p : PhysicalMomentum) (a b : QuantumTest) :
    PreparationVacuumNativeLocalWard.nativeForm (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b 0=
      sourcePair a (sourceNativeContactCore p b) := by
  rw [sourcePair_integral]
  exact integral_congr_ae (Eventually.of_forall (sourceNativeSample_contactCore p a b))

attribute [local irreducible] frameVector frameTest sourceNativeContactCore
  PreparationVacuumNativeLocalWard.nativeForm PreparationVacuumNativeLocalWard.nativeReader

theorem sourceNativeReader_contactCore (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    PreparationVacuumNativeLocalWard.nativeReader (Fin.castAdd 6 (2:Fin 3)) 1 0 p F 0 y=
      sourceApprox F (embed (sourceNativeContactCore p (sourceTestApprox F y))) := by
  unfold PreparationVacuumNativeLocalWard.nativeReader finiteRiesz
  rw [sourceTestApprox_frame]
  simp only [map_sum,map_smul]
  simp_rw [sourceApprox_frame]
  simp only [Finset.smul_sum,sum_apply,smul_apply,InnerProductSpace.rankOne_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceNativeForm_contactCore]
  unfold sourcePair
  rw [frameTest_embed]
  simp only [smul_smul]
  congr 1
  ring

theorem sourceActualN1NativeReader_gauss (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    PreparationVacuumNativeLocalWard.nativeReader (Fin.castAdd 6 (2:Fin 3)) 1 0 p q.F 0
      (sourceActualN1Primal q p state z t)=
        sourceApprox q.F (embed ((-Complex.I) • weightCore
          (sourceColorWardOperator (fullSourceAction p) (sourceTestApprox q.F (sourceActualN1Primal q p state z t))-
            sourceColorWardOperator GaussNativeForm.nativeAction (sourceTestApprox q.F (sourceActualN1Primal q p state z t))+
            sourceColorWardOperator retainedCore (sourceTestApprox q.F (sourceActualN1Primal q p state z t))))) := by
  rw [sourceNativeReader_contactCore,sourceActualN1MaterialContact_gauss q p state z t nonreal]

end LowEnergy.PreparationVacuumPhysicalNativeColourReturn
