import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeChargePotential

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCoframeChargeExchange
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
local instance CoframeExchangeCoreIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationVacuumStaticPoleResponse PreparationVacuumFullOriginResponse

open PreparationVacuumStaticSpatialSource PreparationVacuumStaticSimpleCoupling

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalActualRetardedWard

open PreparationPhysicalCommonObservableUnits PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumGaugeSlowFrequency PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumObservedPoleTensor
open PreparationVacuumActualSpatialPacket
open scoped Matrix.Norms.Operator SchwartzMap

open PreparationPhysicalCommonSpatialGreen PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn

open Set GaussianFourier


open PreparationPhysicalChannelGreen


open PreparationPhysicalChannelRadialJet PreparationVacuumObservedStaticResidue


open GaussCoreHilbert SourceJointResidualEnergy PreparationVacuumQuantumSlowResponse
open PreparationPhysicalJointRadialForcing

open PreparationVacuumPhysicalHalfAxis CanonicalGradedCurrent GaussUnitaryHistory
open PreparationPhysicalRetainerResolventSquare PreparationVacuumStaticSpatialSource
open PreparationPhysicalCausalSpatialDilation
open PreparationPhysicalMasterCorrectionReturn PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalGaugeSeedNull PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets
open PreparationPhysicalActionSeedReduction PreparationVacuumLowerClassical PreparationVacuumJointFieldResponse
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open GaussCoreDifferential GaussCoreLabel NativeHistoryGrade GaussFockLabel GaussYukawaGrade
open PreparationVacuumPropagationPencil PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalGradeZeroRead
open PreparationPhysicalLorentzSeedReturn
open PreparationVacuumYukawaTransport

open PreparationPhysicalTriangularSeedReturn PreparationVacuumPhysicalModeContact
open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumNativeLocalWard
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart


open PreparationPhysicalOriginConfigurationReturn PreparationVacuumRestModeCoupling
open PreparationPhysicalActionUnits

open PreparationPhysicalCoframeOriginPolynomial
open Stage9DEF Stage9DEF.Compatibility Stage10.ChargedPreparation.Dynamics
open GaussQuantumMultiplier GaussFockLift CanonicalGradedCharge

open PreparationPhysicalCoframePreparedReturn PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalNativePhaseChargeInventory PreparationVacuumPhysicalGaussMaterialContact
open PreparationVacuumNativeFieldInjection
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalActualLegNormalization
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourcePoleRead sourceProjection jointResolvent sourceEqualProjection
  sourceResonanceProjection frameVector frameTest finiteRiesz


open PreparationVacuumFieldConstraintResponse
open PreparationPhysicalCoframeChargeSelection GaussFockPair
open scoped ContDiff
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional

private theorem coefficient_smooth : ContDiff ℝ ∞ sourceCoframeModeCoefficient := by
  unfold sourceCoframeModeCoefficient sourceCoframeModeWeight
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  fun_prop

private theorem primal_smooth (positive : Bool) :
    ContDiff ℝ ∞ (sourceCoframePrimalChannel positive) := by
  unfold sourceCoframePrimalChannel
  split <;> exact (contDiff_const.mul coefficient_smooth).mul contDiff_const

local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℝ SourceMatrix:=FiniteDimensional.trans ℝ ℂ SourceMatrix

private def realBlocks : (SourceMatrix×SourceMatrix)→ₗ[ℝ]FullMatrix where
  toFun A:=Matrix.fromBlocks A.1 0 0 (A.2.map (starRingEnd ℂ))
  map_add' A B:=by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_smul' r A:=by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]

private theorem channel_smooth (positive : Bool) :
    ContDiff ℝ ∞ (sourceCoframeChargeChannel positive) := by
  exact realBlocks.toContinuousLinearMap.contDiff.comp
    ((primal_smooth positive).prodMk (primal_smooth (!positive)))

theorem sourceCoframeChannelFiber_smooth (positive : Bool) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceCoframeChargeFiberChannel positive) z.val := by
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp z.val
    (channel_smooth positive).contDiffAt

def sourceCoframeChannelCore (positive : Bool) : QuantumTest→ₗ[ℂ]QuantumTest :=
  localMultiplier (sourceCoframeChargeFiberChannel positive) (sourceCoframeChannelFiber_smooth positive)

def sourceCoframeChargeCore : QuantumTest→ₗ[ℂ]QuantumTest :=
  GaussQuantumMultiplier.action (fun _=>sourceActualGaussChargeMatrix) (fun _=>contDiffAt_const)

theorem sourceCoframeChargeCore_embed (f : QuantumTest) :
    sourceActualGaussCharge (embed f)=embed (sourceCoframeChargeCore f) := by
  change GaussFockLift.lift (quantized sourceActualGaussChargeMatrix) (embed f)=_
  rw [←paidPhaseGaugeBoundedLift%]
  exact CanonicalGradedCurrent.boundedMatrix_core sourceActualGaussChargeMatrix f

theorem sourceCoframeChannelCore_degree (positive : Bool) (f : QuantumTest) :
    sourceCoframeChargeCore (sourceCoframeChannelCore positive f)-
      sourceCoframeChannelCore positive (sourceCoframeChargeCore f)=
        (if positive then (1:ℂ) else -1) • sourceCoframeChannelCore positive f := by
  apply DFunLike.ext
  intro z
  have generated:=congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z))
    (sourceCoframeChargeFiberChannel_degree positive z)
  exact generated

def sourceCoframeChannelForm (positive : Bool) (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (sourceCoframeChargeFiberChannel positive z (b z))
    ∂GaussHistoryHilbert.configurationMeasure

theorem sourceCoframeChannelForm_integrable (positive : Bool) (a b : QuantumTest) :
    Integrable (fun z=>pairSample z (a z) (sourceCoframeChargeFiberChannel positive z (b z)))
      GaussHistoryHilbert.configurationMeasure := by
  exact (densityPair_integrable a (sourceCoframeChannelCore positive b)).congr
    (Eventually.of_forall (fun z=>(pairSample_source a (sourceCoframeChannelCore positive b) z).symm))

theorem sourceCoframeChannelForm_return (positive : Bool) (a b : QuantumTest) :
    sourceCoframeChannelForm positive a b=sourcePair a (sourceCoframeChannelCore positive b) := by
  rw [sourcePair_integral]
  exact integral_congr_ae (Eventually.of_forall (pairSample_source a (sourceCoframeChannelCore positive b)))

def sourceCoframeChannelReader (positive : Bool) (F : GaussUnitaryHistory.Index) : SourceOp :=
  finiteRiesz F (fun i j=>sourceCoframeChannelForm positive (frameTest F i) (frameTest F j))

theorem sourceCoframeChannelReader_return (positive : Bool) (F : GaussUnitaryHistory.Index) (y : H) :
    sourceCoframeChannelReader positive F y=
      sourceApprox F (embed (sourceCoframeChannelCore positive (sourceTestApprox F y))) := by
  unfold sourceCoframeChannelReader finiteRiesz
  rw [sourceTestApprox_frame]
  simp only [map_sum,map_smul]
  simp_rw [sourceApprox_frame]
  simp only [Finset.smul_sum,sum_apply,smul_apply,InnerProductSpace.rankOne_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceCoframeChannelForm_return]
  unfold sourcePair
  rw [frameTest_embed]
  simp only [smul_smul]
  congr 1
  ring

/-- The two errors are the original output frame and input test approximation, without a charge-invariance assumption. -/
theorem sourceCoframeChannelReader_charge (positive : Bool) (F : GaussUnitaryHistory.Index) (y : H) :
    sourceActualGaussCharge (sourceCoframeChannelReader positive F y)-
      sourceCoframeChannelReader positive F (sourceActualGaussCharge y)=
    (if positive then (1:ℂ) else -1) • sourceCoframeChannelReader positive F y+
      (sourceActualGaussCharge (sourceApprox F (embed (sourceCoframeChannelCore positive (sourceTestApprox F y))))-
        sourceApprox F (sourceActualGaussCharge (embed (sourceCoframeChannelCore positive (sourceTestApprox F y)))))+
      sourceApprox F (embed (sourceCoframeChannelCore positive
        (sourceCoframeChargeCore (sourceTestApprox F y)-sourceTestApprox F (sourceActualGaussCharge y)))) := by
  simp only [sourceCoframeChannelReader_return,map_sub]
  rw [sourceCoframeChargeCore_embed]
  have core:=sourceCoframeChannelCore_degree positive (sourceTestApprox F y)
  have lifted:=congrArg (fun f : QuantumTest=>sourceApprox F (embed f)) core
  simp only [map_sub,map_smul] at lifted
  rw [←lifted]
  abel

end LowEnergy.PreparationPhysicalCoframeChargeExchange
