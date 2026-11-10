import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedVolumeObservation
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHamiltonianVolume

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalSignedWeightDynamics
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
local instance signedWeightMaterialQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
local instance signedWeightMaterialModeIndex : DecidableEq Mode:=Classical.decEq _

open PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentRegularAnchor PreparationVacuumPhysicalPoleAmputation

open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumPhysicalPoleLegDynamics
open Stage9DEF Stage9DEF.Compatibility
attribute [local irreducible] jointGenerator jointResolvent sourceChargedGaussPrepared

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

open PreparationPhysicalActualLegNormalization PreparationVacuumPhysicalTailPrice
local instance signedWeightMaterialOperatorReal : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian

attribute [local irreducible] physicalTime timeSlope PreparationVacuumRawJointFeedback.rawReader rawReaderContact


open PreparationPhysicalActualUnitFourPointReturn PreparationPhysicalUnitCurrentFieldReturn
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstPoleGaugeRemainder
open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalFinitePoleVertices PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumActionFieldLift

open GaussCoreDifferential PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open scoped Matrix.Norms.L2Operator

local instance signedWeightMaterialCoframeNorm : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance signedWeightMaterialCoframeSemi : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance signedWeightMaterialCoframeReal : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance signedWeightMaterialMatrixReal : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance signedWeightMaterialFullReal : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _

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


open PreparationPhysicalSignedVolumeWeightReturn SourceCoframeVolume SourceHamiltonianVolume
open GaussLiveMomentum SourceQuantumScalarChart SourceQuantumResidualGaugeSlice
open scoped ContDiff
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalMaterialChargeTorque

private abbrev End := QuantumTest→ₗ[ℂ]QuantumTest
local instance signedWeightMaterialEnd : Semiring End:=Module.End.instSemiring (R:=ℂ) (M:=QuantumTest)

theorem sourceTimeSign_gammaFive :
    sourceTimeSignMatrix=SourceRealScalarFock.branches (GaussCoframeSpin.spinLift diracGammaFive) := by
  rw [sourceTimeSignMatrix,sourceTimeMother_generated,GaussCoframeSpin.spinLift_source]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [diracGammaFive,sourceTimeSpinSign,Matrix.diagonal_apply]

theorem sourceTimeSign_hermitian : sourceTimeSignMatrix.conjTranspose=sourceTimeSignMatrix := by
  rw [sourceTimeSignMatrix_diagonal,Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

theorem sourceTimeSign_native (a : NativeLie) :
    sourceTimeSignMatrix*nativeFull a=nativeFull a*sourceTimeSignMatrix := by
  have primal:=GaussMatterCore.spin_native_commute diracGammaFive a
  have dual:=congrArg ((starRingEnd ℂ).mapMatrix : SourceMatrix→+*SourceMatrix) primal
  simp only [map_mul] at dual
  rw [sourceTimeSign_gammaFive]
  change Matrix.fromBlocks _ 0 0 _*Matrix.fromBlocks _ 0 0 _=
    Matrix.fromBlocks _ 0 0 _*Matrix.fromBlocks _ 0 0 _
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,neg_mul,mul_neg]
  rw [primal]
  simp only [neg_zero]
  congr 1
  exact congrArg Neg.neg dual

theorem sourceTimeSign_spin (a : Fin 7) :
    sourceTimeSignMatrix*GaussCoframeSpin.full a=GaussCoframeSpin.full a*sourceTimeSignMatrix := by
  rw [sourceTimeSignMatrix_diagonal]
  ext i j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]
  cases i with
  | inl i=>cases j with
    | inl j=>
      rcases i with ⟨r,u⟩
      rcases j with ⟨s,v⟩
      by_cases same : u=v
      · fin_cases a <;> fin_cases r <;> fin_cases s <;>
          norm_num [sourceTimeModeSign,sourceTimeSpinSign,GaussCoframeSpin.full,
            GaussCoframeSpin.primal,GaussCoframeSpin.spinLift,GaussCoframeSpin.sourceSpin,same,
            diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
            Matrix.mul_apply,Fin.sum_univ_four,Matrix.diagonal_apply]
      · simp [sourceTimeModeSign,GaussCoframeSpin.full,GaussCoframeSpin.primal,GaussCoframeSpin.spinLift,same]
    | inr j=>simp [GaussCoframeSpin.full]
  | inr i=>cases j with
    | inl j=>simp [GaussCoframeSpin.full]
    | inr j=>
      rcases i with ⟨r,u⟩
      rcases j with ⟨s,v⟩
      by_cases same : u=v
      · fin_cases a <;> fin_cases r <;> fin_cases s <;>
          norm_num [sourceTimeModeSign,sourceTimeSpinSign,GaussCoframeSpin.full,
            GaussCoframeSpin.primal,GaussCoframeSpin.spinLift,GaussCoframeSpin.sourceSpin,same,
            diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
            Matrix.mul_apply,Fin.sum_univ_four,Matrix.diagonal_apply,Matrix.map_apply]
      · by_cases ha : a.val<3 <;>
          simp [sourceTimeModeSign,GaussCoframeSpin.full,GaussCoframeSpin.primal,GaussCoframeSpin.spinLift,same,Matrix.map_apply,ha]

def sourceTimeSignFiber : FockFiber→L[ℂ]FockFiber:=quantized sourceTimeSignMatrix

def sourceTimeSignCore : End:=action (fun _=>sourceTimeSignMatrix) (fun _=>contDiffAt_const)

private theorem sign_quantized (A : FullMatrix) (source : sourceTimeSignMatrix*A=A*sourceTimeSignMatrix) :
    sourceTimeSignFiber*quantized A=quantized A*sourceTimeSignFiber := by
  have paid:=congrArg quantizer (sub_eq_zero.mpr source)
  rw [paidCoframeQuantizerComm%,map_zero] at paid
  exact sub_eq_zero.mp paid

theorem sourceTimeSign_nativeFiber (a : NativeLie) :
    sourceTimeSignFiber*nativeFock a=nativeFock a*sourceTimeSignFiber :=
  sign_quantized _ (sourceTimeSign_native a)

theorem sourceTimeSign_spinCore (a : Fin 7) : Commute sourceTimeSignCore (GaussCoframeSpin.current a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z)) (sign_quantized _ (sourceTimeSign_spin a))

theorem sourceTimeSign_pair (f g : QuantumTest) :
    sourcePair f (sourceTimeSignCore g)=sourcePair (sourceTimeSignCore f) g :=
  action_pair _ _ (fun _=>sourceTimeSign_hermitian) f g

theorem sourceTimeSign_directional (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (sourceTimeSignCore f) z=sourceTimeSignFiber (directional v f z) :=
  (paidRelativeDirectional%) v sourceTimeSignFiber f z

theorem sourceTimeSign_covariant (v : Ambient) :
    (covariantMomentum v).comp sourceTimeSignCore=sourceTimeSignCore.comp (covariantMomentum v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional v (sourceTimeSignCore f) z+
    connection v z (sourceTimeSignFiber (f z)))=
      sourceTimeSignFiber ((-Complex.I) • (directional v f z+connection v z (f z)))
  rw [sourceTimeSign_directional,map_smul,map_add]
  congr 1
  congr 1
  exact (congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z))
    (sourceTimeSign_nativeFiber (inverseL z v).1)).symm

theorem sourceTimeSign_multiply (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    (GaussNativeForm.multiply c smooth).comp sourceTimeSignCore=
      sourceTimeSignCore.comp (GaussNativeForm.multiply c smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul sourceTimeSignFiber (c z:ℂ) (f z)).symm

theorem sourceTimeSign_adjoint (v : Ambient) :
    (GaussMomentumAdjoint.adjoint v).comp sourceTimeSignCore=
      sourceTimeSignCore.comp (GaussMomentumAdjoint.adjoint v) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  simp only [LinearMap.comp_apply]
  rw [GaussNativeForm.adjoint_pair,sourceTimeSign_pair]
  have commute:=LinearMap.congr_fun (sourceTimeSign_covariant v) f
  change covariantMomentum v (sourceTimeSignCore f)=sourceTimeSignCore (covariantMomentum v f) at commute
  rw [←commute,←GaussNativeForm.adjoint_pair,←sourceTimeSign_pair]

/-- The actual scalar Yukawa matrix retains every opposite-chirality transition. -/
def sourceTimeSignYukawaMatrix (phi : SourceQuantumScalarChart.Scalar) : FullMatrix :=
  GaussYukawaCoefficient.fullMatrix phi*sourceTimeSignMatrix-
    sourceTimeSignMatrix*GaussYukawaCoefficient.fullMatrix phi

theorem sourceTimeSignYukawa_entries (phi : SourceQuantumScalarChart.Scalar) (i j : Mode) :
    sourceTimeSignYukawaMatrix phi i j=
      ((sourceTimeModeSign j:ℂ)-(sourceTimeModeSign i:ℂ))*GaussYukawaCoefficient.fullMatrix phi i j := by
  simp only [sourceTimeSignYukawaMatrix,sourceTimeSignMatrix_diagonal,
    Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul]
  ring

theorem sourceTimeSignYukawa_fiber (phi : SourceQuantumScalarChart.Scalar) :
    quantizer (sourceTimeSignYukawaMatrix phi)=
      GaussYukawaCoefficient.sourceMap phi*sourceTimeSignFiber-
        sourceTimeSignFiber*GaussYukawaCoefficient.sourceMap phi := by
  unfold sourceTimeSignYukawaMatrix
  rw [paidCoframeQuantizerComm%]
  rfl

theorem sourceWeightCore_factor : weightCore=
    (Stage10.ActionNormalization.phaseMomentum:ℂ) • (SourceCoframeVolume.volumeAction.comp sourceTimeSignCore) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases chart : z∈physicalChart
  · change weightFiber z (f z)=(Stage10.ActionNormalization.phaseMomentum:ℂ) •
      ((GaussNativeEnergy.volume z:ℂ) • sourceTimeSignFiber (f z))
    rw [sourceWeightFiber_signed ⟨z,chart⟩,smul_apply,smul_smul,Complex.ofReal_mul]
    rfl
  · have outside : f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>chart (f.tsupport_subset h))
    change weightFiber z (f z)=(Stage10.ActionNormalization.phaseMomentum:ℂ) •
      ((GaussNativeEnergy.volume z:ℂ) • sourceTimeSignFiber (f z))
    rw [outside,map_zero,map_zero,smul_zero,smul_zero]

end LowEnergy.PreparationPhysicalSignedWeightDynamics
