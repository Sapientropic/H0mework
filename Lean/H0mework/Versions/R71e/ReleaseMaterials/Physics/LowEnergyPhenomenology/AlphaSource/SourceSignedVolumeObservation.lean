import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedVolumeMatrix

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalSignedVolumeWeightReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance signedVolumeObservationQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

open PreparationPhysicalFinitePoleVertices PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativeWardFiniteObservation
open PreparationPhysicalNativePolarizationEmitter

open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationPhysicalFiniteObservationSoftReturn PreparationVacuumSoftPoleSelection

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalNativePhaseChargeInventory
open SU7MotherGaugeTheory SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction

open PreparationPhysicalActualPhaseChargeReturn
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open GaussQuantumMultiplier GaussHalfDensity CanonicalGradedCharge GaussHistoryHilbert
open SourceQuantumGaugeSliceCoordinates
local instance signedVolumeObservationModeIndex : DecidableEq Mode:=Classical.decEq _

open PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentRegularAnchor PreparationVacuumPhysicalPoleAmputation

open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumPhysicalPoleLegDynamics
open Stage9DEF Stage9DEF.Compatibility
attribute [local irreducible] jointGenerator jointResolvent sourceChargedGaussPrepared

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

open PreparationPhysicalActualLegNormalization PreparationVacuumPhysicalTailPrice
local instance signedVolumeObservationOperatorReal : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian

attribute [local irreducible] physicalTime timeSlope PreparationVacuumRawJointFeedback.rawReader rawReaderContact


open PreparationPhysicalActualUnitFourPointReturn PreparationPhysicalUnitCurrentFieldReturn
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstPoleGaugeRemainder
open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalFinitePoleVertices PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumActionFieldLift

open GaussCoreDifferential PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open scoped Matrix.Norms.L2Operator

local instance signedVolumeObservationCoframeNorm : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance signedVolumeObservationCoframeSemi : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance signedVolumeObservationCoframeReal : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance signedVolumeObservationMatrixReal : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance signedVolumeObservationFullReal : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationPhysicalActualPolarizationResponse PreparationPhysicalFirstGaugeMaterialDifference
open PreparationPhysicalMaterialSpectralCharge PreparationPhysicalCoframeChargeSelection

open PreparationPhysicalFirstTemporalChargeReturn PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumPhysicalColorWard PreparationVacuumPhysicalNumberOneRead
open PreparationVacuumFieldConstraintResponse GaussFockPair CanonicalGradedCurrent
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumWeightedChargeActionWard

open PreparationVacuumWeightedChargeActionWard PreparationPhysicalCoframeChargeExchange
open PreparationVacuumPhysicalSlowBlock
attribute [local irreducible] sourceN1Projection sourceTemporalWeightReader


open PreparationPhysicalTemporalNumberOneReturn PreparationPhysicalActionUnits PreparationPhysicalPoleChargeMatrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem sourceTimeSign_coordinates (s e : Fin 2) :
    sourceTimeSignMatrix*ᵥsourceChargedCoordinates s e=
      ((if s=0 then -1 else 1:ℝ):ℂ) • sourceChargedCoordinates s e := by
  rw [sourceTimeSignMatrix_diagonal,sourceChargedCoordinates_basis,Matrix.mulVec_smul,
    Matrix.diagonal_mulVec_single]
  rw [sourceTimeSignMatrix_actual]
  ext i
  simp only [Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  split_ifs <;> ring

theorem sourceTemporalSignedCharge_coordinates (s e : Fin 2) :
    (sourceTimeSignMatrix*sourceFirstChargeMatrix)*ᵥsourceChargedCoordinates s e=
      (((if s=0 then -1 else 1:ℝ):ℂ)*(sourceActualPhaseCharge e:ℂ)) • sourceChargedCoordinates s e := by
  rw [←Matrix.mulVec_mulVec,sourceFirstCharge_coordinates,Matrix.mulVec_smul,sourceTimeSign_coordinates,smul_smul,mul_comm]

theorem sourceTemporalFiber_actual (z : physicalChart) (p : PhysicalMomentum) (s e : Fin 2) :
    rawFiber (sourceEnergyAxisField 1 0) p (0,z.val) (sourceChargedFiber s e)=
      (-((Stage10.ActionNormalization.phaseMomentum*GaussNativeEnergy.volume z.val:ℝ):ℂ)*
        (((if s=0 then -1 else 1:ℝ):ℂ)*(sourceActualPhaseCharge e:ℂ))) • sourceChargedFiber s e := by
  rw [sourceTemporalFiber_signed,smul_apply]
  change _ • quantized (sourceTimeSignMatrix*sourceFirstChargeMatrix) (sourceChargedFiber s e)=_
  rw [sourceChargedFiber,quantized_oneParticle,sourceTemporalSignedCharge_coordinates]
  change _ • fiberCoordinates.symm (Fermion.oneParticleLinear (_ • sourceChargedCoordinates s e))=_
  rw [map_smul,map_smul,smul_smul]
  rfl

local instance signedVolumeObservationLabel : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

/-- The original configuration density and volume remain inside the source integral. -/
def sourceSignedVolumeSample (A : FullMatrix) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*GaussNativeEnergy.volume z:ℝ):ℂ)*
    pairSample z (a z) (quantizer (sourceTimeSignMatrix*A) (b z))

def sourceSignedVolumeForm (A : FullMatrix) (a b : QuantumTest) : ℂ :=
  ∫z,sourceSignedVolumeSample A a b z ∂GaussHistoryHilbert.configurationMeasure

theorem sourceSignedVolumeSample_actual (A : FullMatrix) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    sourceSignedVolumeSample A a b z=densityPair a (sourceTemporalMatrixCore A b) z := by
  rw [←pairSample_source]
  by_cases inside : z∈tsupport a
  · have chart : z∈physicalChart:=a.tsupport_subset inside
    have matrix:=sourceWeightSymbol_signed ⟨z,chart⟩
    change _=pairSample z (a z) (quantizer (sourceWeightSymbol z*A) (b z))
    rw [matrix,smul_mul_assoc,map_smul,smul_apply,pairSample_smul_right]
    rfl
  · simp only [sourceSignedVolumeSample,image_eq_zero_of_notMem_tsupport inside,
      pairSample_zero_left,mul_zero]

theorem sourceSignedVolumeSample_integrable (A : FullMatrix) (a b : QuantumTest) :
    Integrable (sourceSignedVolumeSample A a b) GaussHistoryHilbert.configurationMeasure := by
  have same:=funext (sourceSignedVolumeSample_actual A a b)
  rw [same]
  exact densityPair_integrable a (sourceTemporalMatrixCore A b)

theorem sourceSignedVolumeForm_actual (A : FullMatrix) (a b : QuantumTest) :
    sourceSignedVolumeForm A a b=sourcePair a (sourceTemporalMatrixCore A b) := by
  rw [sourceSignedVolumeForm,sourcePair_integral]
  exact integral_congr_ae (Eventually.of_forall (sourceSignedVolumeSample_actual A a b))

def sourceSignedVolumeReader (A : FullMatrix) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>sourceSignedVolumeForm A (frameTest F i) (frameTest F j))

/-- The coefficient matrix is computed, while both original finite frames remain. -/
def sourceSignedVolumeRead (A : FullMatrix) (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  ∑i : FrameIndex F,∑j : FrameIndex F,
    star (inner ℂ (frameVector F i) x)*sourceSignedVolumeForm A (frameTest F i) (frameTest F j)*
      inner ℂ (frameVector F j) y

theorem sourceSignedVolumeRead_generated (A : FullMatrix) (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (sourceSignedVolumeReader A F y)=sourceSignedVolumeRead A F x y :=
  finiteRiesz_pair F _ x y

theorem sourceSignedVolumeReader_bound (A : FullMatrix) (F : GaussUnitaryHistory.Index) :
    ‖sourceSignedVolumeReader A F‖≤finitePrice F
      (fun i j=>sourceSignedVolumeForm A (frameTest F i) (frameTest F j)) :=
  finiteRiesz_price F _

private theorem weight_matrix_one : sourceTemporalMatrixCore 1=weightCore := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change quantizer (sourceWeightSymbol z*1) (f z)=quantizer (sourceWeightSymbol z) (f z)
  rw [mul_one]

theorem sourceTemporalWeightReader_volume (F : GaussUnitaryHistory.Index) :
    sourceTemporalWeightReader F=sourceSignedVolumeReader 1 F := by
  unfold sourceTemporalWeightReader sourceSignedVolumeReader
  congr 1
  funext i j
  rw [sourceSignedVolumeForm_actual,weight_matrix_one]

theorem sourceTemporalChargeReader_volume (F : GaussUnitaryHistory.Index) :
    sourceTemporalChargeReader F= -sourceSignedVolumeReader sourceFirstChargeMatrix F := by
  unfold sourceTemporalChargeReader sourceSignedVolumeReader
  have entries : (fun i j=>sourceTemporalChargeForm (frameTest F i) (frameTest F j))=
      fun i j=>-sourceSignedVolumeForm sourceFirstChargeMatrix (frameTest F i) (frameTest F j) := by
    funext i j
    rw [sourceSignedVolumeForm_actual]
    change inner ℂ (embed (frameTest F i)) (embed (-(sourceTemporalMatrixCore sourceFirstChargeMatrix (frameTest F j))))=_
    rw [map_neg,inner_neg_right]
    rfl
  rw [entries]
  simp only [finiteRiesz,neg_smul,Finset.sum_neg_distrib]

theorem sourceTemporalN1Pair_volume (F : GaussUnitaryHistory.Index) (x y : H)
    (generated : sourceN1Projection y=y) :
    sourceTemporalN1Pair F x y= -sourceSignedVolumeRead sourceFirstChargeMatrix F x y := by
  rw [←sourceTemporalSpectralPair_N1 F x y generated,←sourceTemporalSpectralPair_return,
    sourceTemporalChargeReader_volume,neg_apply,inner_neg_right,sourceSignedVolumeRead_generated]

theorem sourceTemporalUnitVolume_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceActualUnitLegRead q sL eL sR eR (sourceTemporalChargeReader q.F)=
      -(sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))*
        sourceSignedVolumeRead sourceFirstChargeMatrix q.F
          ((jointResolvent 0 q.F q.z 0).adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
          (jointResolvent 0 q.F q.w 0 (sourceChargedGaussPrepared q.epsilon q.precision sR eR)) := by
  have paid:=sourceTemporalUnitReader_return q sL eL sR eR left right
  rw [sourceTemporalSpectralPair_N1 q.F _ _ (sourceTemporalGreen_N1 q 0 sR eR q.w right),
    sourceTemporalN1Pair_volume q.F _ _ (sourceTemporalGreen_N1 q 0 sR eR q.w right),mul_neg] at paid
  simpa only [neg_mul] using paid

end LowEnergy.PreparationPhysicalSignedVolumeWeightReturn
