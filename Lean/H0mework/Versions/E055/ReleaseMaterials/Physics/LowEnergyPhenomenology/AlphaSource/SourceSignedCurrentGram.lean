import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceTemporalMatchedResponse
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedVolumeObservation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalSignedCurrentPoleObserver
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalSourceHarmonicReturn
open PreparationVacuumPhysicalCharacteristic ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource FullQuantum FullSpace PreparationVacuumLowerClassical

open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalFeedback
open PreparationPhysicalResponseChargeGrading PreparationVacuumLorentzFieldInjection
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalPoleChargeMatrix
open GaussFockLift GaussCoreHilbert PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalNativePhaseChargeInventory
open scoped InnerProductSpace

open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice CanonicalGradedCharge GaussCoreDifferential GaussQuantumMultiplier
open GaussFockPair GaussLiveMomentum GaussNativePotential
open scoped ContDiff

open NativeHistoryGrade GaussUnitaryHistory CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa PreparationPhysicalActualLegNormalization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalPoleAmputation PreparationPhysicalChargedScatteringPoleReturn
open GaussFockWeights GaussDensityCore MeasureTheory PreparationVacuumFieldConstraintResponse PreparationVacuumYukawaTransport
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent actualC gradedTest

open PreparationPhysicalFirstGaugeMaterialDifference PreparationPhysicalActualUnitFourPointReturn
open PreparationPhysicalActualPolarizationResponse PreparationVacuumFullFieldRiesz

open PreparationPhysicalFirstChargeFourPointReturn PreparationPhysicalFirstTemporalChargeReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumSpatialDensityTransport
open PreparationVacuumHalfDensityFiber PreparationVacuumSourceActionJets PreparationVacuumGradedTransport

open PreparationPhysicalTemporalConstraintObserver PreparationPhysicalSignedVolumeWeightReturn
open PreparationPhysicalTemporalNumberOneReturn PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalFeedback

/-- Every actual field insertion keeps the repaired full independent-dual symbol inside its source volume density. -/
theorem sourceSignedCurrent_raw (z : physicalChart) (p : PhysicalMomentum) (f : Field289) :
    rawActionSymbol f p (sourceState z.val)=
      -((Stage10.ActionNormalization.phaseMomentum*GaussNativeEnergy.volume z.val:ℝ):ℂ) •
        (sourceTimeSignMatrix*symbolFirst p (sourceState z.val) (fieldDirection f)) := by
  rw [rawActionSymbol_source f p _ (PreparationVacuumNonlinearFieldCurve.sourceState_valid z)]
  rw [neg_smul,←smul_mul_assoc]
  change -(sourceWeightSymbol z.val*symbolFirst p (sourceState z.val) (fieldDirection f))=_
  rw [sourceWeightSymbol_signed,smul_mul_assoc,neg_smul]

/-- The sign matrix and physical h are computed; all configuration-dependent Hamiltonian coefficients remain inside the same source integral. -/
def sourceSignedCurrentSample (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (z : SourceCoordinateSlice) : ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*GaussNativeEnergy.volume z:ℝ):ℂ)*
    pairSample z (a z) (quantizer (sourceTimeSignMatrix*
      symbolFirst p (sourceState z) (fieldDirection f)) (b z))

theorem sourceSignedCurrentSample_actual (f : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (z : SourceCoordinateSlice) :
    rawSample f p a b (0,z)= -sourceSignedCurrentSample f p a b z := by
  by_cases inside : z∈tsupport a
  · have chart : z∈physicalChart:=a.tsupport_subset inside
    rw [rawSample,rawFiber,ambientState_zero,sourceSignedCurrent_raw ⟨z,chart⟩ p f,
      map_smul,smul_apply,pairSample_smul_right]
    simp only [sourceSignedCurrentSample,neg_mul]
  · simp only [rawSample_zero f p a b 0 z inside,sourceSignedCurrentSample,
      image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,mul_zero,neg_zero]

theorem sourceSignedCurrentSample_integrable (f : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) : Integrable (sourceSignedCurrentSample f p a b) GaussHistoryHilbert.configurationMeasure := by
  have original : Integrable (fun z=>rawSample f p a b (0,z)) GaussHistoryHilbert.configurationMeasure :=
    parameter_slice_integrable _ (tsupport a) a.hasCompactSupport 0
      (fun z=>rawSample_near_smooth f p a b 0 z (by simpa only [norm_zero] using ambientRadius_positive a))
      (rawSample_zero f p a b)
  apply original.neg.congr
  exact Filter.Eventually.of_forall (fun z=>by simp only [Pi.neg_apply,sourceSignedCurrentSample_actual,neg_neg])

def sourceSignedCurrentForm (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,sourceSignedCurrentSample f p a b z ∂GaussHistoryHilbert.configurationMeasure

theorem sourceSignedCurrentForm_actual (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    rawForm f p a b 0= -sourceSignedCurrentForm f p a b := by
  simp only [rawForm,sourceSignedCurrentSample_actual,
    sourceSignedCurrentForm,MeasureTheory.integral_neg]

/-- The two original finite frame labels are preserved, including every cross coefficient. -/
def sourceSignedCurrentReader (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>sourceSignedCurrentForm f p (frameTest F i) (frameTest F j))

theorem sourceSignedCurrentReader_actual (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    PreparationVacuumRawJointFeedback.rawReader f p F 0= -sourceSignedCurrentReader f p F := by
  simp only [PreparationVacuumRawJointFeedback.rawReader,sourceSignedCurrentReader,
    sourceSignedCurrentForm_actual,finiteRiesz,neg_smul,Finset.sum_neg_distrib]

def sourceSignedCurrentRead (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  ∑i : FrameIndex F,∑j : FrameIndex F,
    star (inner ℂ (frameVector F i) x)*sourceSignedCurrentForm f p (frameTest F i) (frameTest F j)*
      inner ℂ (frameVector F j) y

theorem sourceSignedCurrentRead_generated (f : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (sourceSignedCurrentReader f p F y)=sourceSignedCurrentRead f p F x y :=
  finiteRiesz_pair F _ x y

theorem sourceSignedCurrentReader_bound (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖sourceSignedCurrentReader f p F‖≤finitePrice F
      (fun i j=>sourceSignedCurrentForm f p (frameTest F i) (frameTest F j)) :=
  finiteRiesz_price F _

/-- All four literal first-pole axes use their actual full native matrices and coframe, not a temporal charge substituted into spatial slots. -/
theorem sourceSignedCurrent_axis (p : PhysicalMomentum) (k : Fin 4) (a b : QuantumTest) :
    sourceSignedCurrentForm (sourceEnergyAxisField 1 k) p a b=
      ∫z,((Stage10.ActionNormalization.phaseMomentum*GaussNativeEnergy.volume z:ℝ):ℂ)*
        pairSample z (a z) (quantizer (sourceTimeSignMatrix*
          SourceRealScalarFock.branches (sourcePolarizationAxisEnergy (sourceState z) k)) (b z))
            ∂GaussHistoryHilbert.configurationMeasure := by
  unfold sourceSignedCurrentForm
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by
    by_cases inside : z∈tsupport a
    · have chart : z∈physicalChart:=a.tsupport_subset inside
      simp only [sourceSignedCurrentSample,sourcePolarizationAxis_symbol _
        (PreparationVacuumNonlinearFieldCurve.sourceState_valid ⟨z,chart⟩) p k]
    · simp only [sourceSignedCurrentSample,image_eq_zero_of_notMem_tsupport inside,
        pairSample_zero_left,mul_zero])

/-- The temporal member is the already computed physical signed-charge Gram on the same configurations. -/
theorem sourceSignedCurrent_temporal (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceSignedCurrentReader sourceTemporalAxis p F=sourceSignedVolumeReader sourceFirstChargeMatrix F := by
  have raw := sourceSignedCurrentReader_actual sourceTemporalAxis p F
  rw [sourceTemporalChargeReader_original,sourceTemporalChargeReader_volume] at raw
  exact neg_injective raw.symm

end LowEnergy.PreparationPhysicalSignedCurrentPoleObserver
