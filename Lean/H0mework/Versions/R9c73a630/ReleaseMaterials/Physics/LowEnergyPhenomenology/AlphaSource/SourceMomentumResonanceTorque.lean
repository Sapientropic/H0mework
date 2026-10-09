import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyOffDiagonalCharge

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalMaterialSpectralCharge
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
local instance MomentumSpectralIndex : DecidableEq Quantum.Index:=Classical.decEq _
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


open PreparationPhysicalCoframeChargeExchange PreparationVacuumPhysicalGaussColorTorque
open GaussDiagonalHistory GaussCoframeSpin GaussLiveMomentum

open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa
open CanonicalPhysicalSpatial CanonicalPhysicalWardCore

open PreparationPhysicalMaterialChargeTorque

theorem sourceRelativeCharge_momentumMatrix (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    sourceRelativeChargeMatrix*momentumMatrix z p=momentumMatrix z p*sourceRelativeChargeMatrix := by
  simp only [momentumMatrix,mul_neg,neg_mul,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg (fun A : FullMatrix=>((p i*GaussMatterCore.coefficient i b z:ℝ):ℂ) • A)
    ((paidRelativeCore% relative_blocks) _ _)

theorem sourceRelativeCharge_momentumCore (p : PhysicalMomentum) :
    (momentumAction p).comp sourceRelativeChargeCore=sourceRelativeChargeCore.comp (momentumAction p) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have fiber:=(paidRelativeCore% relative_quantized) (momentumMatrix z p) (sourceRelativeCharge_momentumMatrix z p)
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A (f z)) fiber.symm

/-- The complete original physical momentum is neutral under the actual full charge before finite compression. -/
theorem sourceActualCharge_momentumCore (p : PhysicalMomentum) :
    (momentumAction p).comp sourceCoframeChargeCore=sourceCoframeChargeCore.comp (momentumAction p) := by
  have color : (momentumAction p).comp (chargeAction (colorGenerator 2))=
      (chargeAction (colorGenerator 2)).comp (momentumAction p) :=
    (CanonicalPhysicalWardCore.momentum_charge_commutes p (colorGenerator 2)).eq
  rw [sourceActualCharge_coreDecomposition]
  simp only [LinearMap.comp_add,LinearMap.add_comp,LinearMap.comp_smul,LinearMap.smul_comp,
    LinearMap.comp_neg,LinearMap.neg_comp,color,sourceRelativeCharge_momentumCore]

/-- These are restrictions to the identical finite set in the common realized source domain. -/
theorem sourcePhysicalSpan_momentum (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    physicalSpan p F=physicalSpan 0 F := by
  let common : Submodule ℂ H:=Submodule.span ℂ
    ((fun x : GaussCoreHilbert.Core=>(x:H)) '' (↑(show Finset GaussCoreHilbert.Core from F) : Set GaussCoreHilbert.Core))
  change common=common
  rfl

theorem sourceGradedTest_momentum (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (g : NativeHistoryGrade.Label) (x : H) : gradedTest p F g x=gradedTest 0 F g x := by
  apply embed_injective
  simp only [gradedTest,projectionTest_embed,sourcePhysicalSpan_momentum]

private theorem physical_pair (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (actualC p F y)=∑g : NativeHistoryGrade.Label,
      sourcePair (gradedTest 0 F g x) (physicalAction p (gradedTest 0 F g y)) := by
  have paid:=(gradedForm_pair (0:Field289) p F x y).self_of_nhds
  simpa only [actualC,gradedForm_zero,physicalForm_source,sourceGradedTest_momentum] using paid

/-- The affine physical velocity uses exactly the same graded finite-span tests. -/
theorem sourceVelocityMaterial_pair (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x y : H) :
    inner ℂ x (sourceVelocityLinear F n y)=∑g : NativeHistoryGrade.Label,
      sourcePair (gradedTest 0 F g x) (momentumAction n (gradedTest 0 F g y)) := by
  have delta : sourceVelocityLinear F n=actualC n F-actualC 0 F := by rw [actualC_affine];abel
  rw [delta,sub_apply,inner_sub_right,physical_pair,sourcePhysicalCompression_pair,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  simp only [physicalAction,LinearMap.add_apply,sourcePair,map_add,inner_add_right,add_sub_cancel_left]

def sourceVelocityChargeRead (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x y : H) : ℂ :=
  ∑g : NativeHistoryGrade.Label,
    (sourcePair (gradedTest 0 F g x) (momentumAction n (sourcePhysicalSpanChargeDefect F g y))-
      sourcePair (sourcePhysicalSpanChargeDefect F g x) (momentumAction n (gradedTest 0 F g y)))

theorem sourceVelocityChargeRead_return (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x y : H) :
    inner ℂ x ((sourceVelocityLinear F n*sourceActualGaussCharge-sourceActualGaussCharge*sourceVelocityLinear F n) y)=
      sourceVelocityChargeRead F n x y := by
  simp only [sub_apply,mul_apply_eq_comp,inner_sub_right]
  rw [←sourceActualGaussCharge_pair,sourceVelocityMaterial_pair,sourceVelocityMaterial_pair,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have right : gradedTest 0 F g (sourceActualGaussCharge y)=
      sourceCoframeChargeCore (gradedTest 0 F g y)+sourcePhysicalSpanChargeDefect F g y := by
    unfold sourcePhysicalSpanChargeDefect
    abel
  have left : gradedTest 0 F g (sourceActualGaussCharge x)=
      sourceCoframeChargeCore (gradedTest 0 F g x)+sourcePhysicalSpanChargeDefect F g x := by
    unfold sourcePhysicalSpanChargeDefect
    abel
  have pair : sourcePair (sourceCoframeChargeCore (gradedTest 0 F g x))
      (momentumAction n (gradedTest 0 F g y))=
      sourcePair (gradedTest 0 F g x) (sourceCoframeChargeCore (momentumAction n (gradedTest 0 F g y))) := by
    have paid:=sourceActualGaussCharge_pair (embed (gradedTest 0 F g x))
      (embed (momentumAction n (gradedTest 0 F g y)))
    rw [sourceCoframeChargeCore_embed,sourceCoframeChargeCore_embed] at paid
    exact paid
  have neutral:=LinearMap.congr_fun (sourceActualCharge_momentumCore n) (gradedTest 0 F g y)
  change momentumAction n (sourceCoframeChargeCore (gradedTest 0 F g y))=
    sourceCoframeChargeCore (momentumAction n (gradedTest 0 F g y)) at neutral
  rw [right,left,map_add]
  simp only [sourcePair,map_add,inner_add_right,inner_add_left] at pair ⊢
  rw [pair,neutral]
  abel

/-- Pinned velocity charge torque retains the actual finite-span velocity and the already-generated C0 window torque. -/
def sourcePinnedMaterialTorque (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : SourceOp :=
  sourceEqualProjection F (sourceVelocityLinear F n*sourceActualGaussCharge-sourceActualGaussCharge*sourceVelocityLinear F n)-
    sourceEqualMaterialExchange F (sourceVelocityLinear F n)

theorem sourcePinnedMaterialTorque_original (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourcePinnedMaterialTorque F n=sourcePinnedVelocity F n*sourceActualGaussCharge-sourceActualGaussCharge*sourcePinnedVelocity F n := by
  have paid:=sourceCoframeEqualExchange_return F (sourceVelocityLinear F n)
  rw [←sourceEqualMaterialExchange_original] at paid
  change sourceActualGaussCharge*sourcePinnedVelocity F n-sourcePinnedVelocity F n*sourceActualGaussCharge=
    sourceEqualProjection F (sourceActualGaussCharge*sourceVelocityLinear F n-sourceVelocityLinear F n*sourceActualGaussCharge)+
      sourceEqualMaterialExchange F (sourceVelocityLinear F n) at paid
  unfold sourcePinnedMaterialTorque
  simp only [map_sub] at paid ⊢
  have exchanged:=eq_sub_iff_add_eq.mpr (show sourceEqualMaterialExchange F (sourceVelocityLinear F n)+
      sourceEqualProjection F (sourceActualGaussCharge*sourceVelocityLinear F n-sourceVelocityLinear F n*sourceActualGaussCharge)=
      sourceActualGaussCharge*sourcePinnedVelocity F n-sourcePinnedVelocity F n*sourceActualGaussCharge from by
    rw [map_sub]
    exact (add_comm _ _).trans paid.symm)
  rw [exchanged]
  simp only [map_sub]
  abel

open Lean Meta Elab Term
elab "paidSpectralPinnedRight%" : term => do
  let wanted:=`LowEnergy.PreparationVacuumPhysicalLockedN1Balance.pinned_channel_right
  let all:=(←getEnv).constants.toList
  let candidates:=all.filter fun (name,_)=>name.toString.startsWith
    "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedStaticN1Read." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceLockedStaticN1Read.pinned_channel_right; actual owners: {all.filterMap (fun (name,_)=>if privateToUserName name==wanted then some name else none)}"

/-- The inverse on the nonzero velocity space is the original eta=0 off-pole return, with its source-fixed phase. -/
def sourceReducedVelocityInverse (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : SourceOp :=
  Complex.I • sourceOffPoleReturn F n 0 0

theorem sourceReducedVelocityInverse_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    ‖sourceReducedVelocityInverse F n‖ ≤ sourceOffPolePrice F n 0 := by
  unfold sourceReducedVelocityInverse
  rw [norm_smul,Complex.norm_I,one_mul]
  exact sourceOffPoleReturn_price F n 0 0

local instance momentumSpectralModule : Module ℂ SourceOp:=ContinuousLinearMap.module

private theorem inverse_coefficient (v : ℝ) (nonzero : v≠0) :
    Complex.I*((Complex.I*(v:ℂ))⁻¹)*(v:ℂ)=1 := by
  have realnonzero : (v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr nonzero
  rw [mul_inv_rev]
  calc
    _=(Complex.I*Complex.I⁻¹)*((v:ℂ)⁻¹*(v:ℂ)) := by ring
    _=1 := by rw [mul_inv_cancel₀ Complex.I_ne_zero,inv_mul_cancel₀ realnonzero,mul_one]

private theorem off_velocity_resolution (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    (∑i : Channel F,if sourceVelocityGap F n 0 i=0 then 0 else sourcePinnedChannel F n i)=
      1-sourceResonanceProjection F n 0 := by
  classical
  apply eq_sub_iff_add_eq.mpr
  rw [sourceResonanceProjection,←Finset.sum_add_distrib]
  calc
    _=∑i : Channel F,sourcePinnedChannel F n i := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp only [zero_add,add_zero]
    _=1 := sourcePinnedChannel_resolution F n

/-- Both source products invert precisely the nonzero velocity space; no zero mode is removed. -/
theorem sourceReducedVelocityInverse_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourcePinnedVelocity F n*sourceReducedVelocityInverse F n=1-sourceResonanceProjection F n 0 := by
  classical
  unfold sourceReducedVelocityInverse
  rw [mul_smul_comm]
  simp only [sourceOffPoleReturn,Finset.mul_sum,Finset.smul_sum]
  rw [←off_velocity_resolution F n]
  apply Finset.sum_congr rfl
  intro i _
  by_cases zero : sourceVelocityGap F n 0 i=0
  · simp only [if_pos zero,mul_zero]
    exact momentumSpectralModule.toDistribMulAction.smul_zero _
  · have nonzero : sourcePinnedValue F n i≠0 := by simpa only [sourceVelocityGap,add_zero] using zero
    simp only [sourceVelocityGap,add_zero,if_neg nonzero,Complex.ofReal_zero,zero_add,
      mul_smul_comm,sourcePinnedChannel_eigen,smul_smul]
    have coefficient : Complex.I*((Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹*(sourcePinnedValue F n i:ℂ))=1 := by
      rw [←mul_assoc]
      exact inverse_coefficient _ nonzero
    rw [coefficient,one_smul]

theorem sourceReducedVelocityInverse_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourceReducedVelocityInverse F n*sourcePinnedVelocity F n=1-sourceResonanceProjection F n 0 := by
  classical
  unfold sourceReducedVelocityInverse
  rw [smul_mul_assoc]
  simp only [sourceOffPoleReturn,Finset.sum_mul,Finset.smul_sum]
  rw [←off_velocity_resolution F n]
  apply Finset.sum_congr rfl
  intro i _
  by_cases zero : sourceVelocityGap F n 0 i=0
  · simp only [if_pos zero,zero_mul]
    exact momentumSpectralModule.toDistribMulAction.smul_zero _
  · have nonzero : sourcePinnedValue F n i≠0 := by simpa only [sourceVelocityGap,add_zero] using zero
    simp only [sourceVelocityGap,add_zero,if_neg nonzero,Complex.ofReal_zero,zero_add,
      smul_mul_assoc,paidSpectralPinnedRight%,smul_smul]
    have coefficient : Complex.I*((Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹*(sourcePinnedValue F n i:ℂ))=1 := by
      rw [←mul_assoc]
      exact inverse_coefficient _ nonzero
    rw [coefficient,one_smul]

private theorem resonance_zero_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourcePinnedVelocity F n*sourceResonanceProjection F n 0=0 := by
  have paid:=sourceResonance_eigen F n 0
  simp only [neg_zero,Complex.ofReal_zero] at paid
  exact paid.trans (momentumSpectralModule.zero_smul _)

private theorem resonance_zero_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourceResonanceProjection F n 0*sourcePinnedVelocity F n=0 := by
  classical
  rw [sourceResonanceProjection,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  by_cases zero : sourceVelocityGap F n 0 i=0
  · have value : sourcePinnedValue F n i=0 := by simpa only [sourceVelocityGap,add_zero] using zero
    rw [if_pos zero,paidSpectralPinnedRight%,value,Complex.ofReal_zero]
    exact momentumSpectralModule.zero_smul _
  · rw [if_neg zero,zero_mul]

/-- The original resonance exchange is generated by the same material and physical-span torques through the original off-pole return. -/
def sourceResonanceMaterialExchange (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : SourceOp :=
  sourceReducedVelocityInverse F n*sourcePinnedMaterialTorque F n*sourceResonanceProjection F n 0+
    sourceResonanceProjection F n 0*sourcePinnedMaterialTorque F n*sourceReducedVelocityInverse F n

theorem sourceResonanceMaterialExchange_original (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourceResonanceMaterialExchange F n=sourceCoframeResonanceExchange F n := by
  rw [←sourceCoframeResonanceExchange_return]
  unfold sourceResonanceMaterialExchange
  rw [sourcePinnedMaterialTorque_original]
  calc
    _=(sourceReducedVelocityInverse F n*sourcePinnedVelocity F n)*sourceActualGaussCharge*sourceResonanceProjection F n 0-
        sourceReducedVelocityInverse F n*sourceActualGaussCharge*(sourcePinnedVelocity F n*sourceResonanceProjection F n 0)+
        (sourceResonanceProjection F n 0*sourcePinnedVelocity F n)*sourceActualGaussCharge*sourceReducedVelocityInverse F n-
        sourceResonanceProjection F n 0*sourceActualGaussCharge*(sourcePinnedVelocity F n*sourceReducedVelocityInverse F n) := by
      simp only [mul_sub,sub_mul,mul_assoc]
      abel
    _=_ := by
      rw [sourceReducedVelocityInverse_left,sourceReducedVelocityInverse_right,
        resonance_zero_left,resonance_zero_right]
      simp only [sub_mul,mul_sub,one_mul,mul_one,zero_mul,mul_zero,sub_zero,add_zero,mul_assoc]
      abel

/-- This pointwise generated price is retained as such; whole spatial integration still uses the complete joint source price. -/
theorem sourceResonanceMaterialExchange_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    ‖sourceResonanceMaterialExchange F n‖ ≤
      2*sourceOffPolePrice F n 0*‖sourcePinnedMaterialTorque F n‖*‖sourceResonanceProjection F n 0‖ := by
  have first : ‖sourceReducedVelocityInverse F n*sourcePinnedMaterialTorque F n*sourceResonanceProjection F n 0‖ ≤
      sourceOffPolePrice F n 0*‖sourcePinnedMaterialTorque F n‖*‖sourceResonanceProjection F n 0‖ := by
    calc
      _ ≤ ‖sourceReducedVelocityInverse F n‖*‖sourcePinnedMaterialTorque F n‖*‖sourceResonanceProjection F n 0‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := by gcongr;exact sourceReducedVelocityInverse_price F n
  have second : ‖sourceResonanceProjection F n 0*sourcePinnedMaterialTorque F n*sourceReducedVelocityInverse F n‖ ≤
      ‖sourceResonanceProjection F n 0‖*‖sourcePinnedMaterialTorque F n‖*sourceOffPolePrice F n 0 := by
    calc
      _ ≤ ‖sourceResonanceProjection F n 0‖*‖sourcePinnedMaterialTorque F n‖*‖sourceReducedVelocityInverse F n‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := by gcongr;exact sourceReducedVelocityInverse_price F n
  exact (norm_add_le _ _).trans ((add_le_add first second).trans_eq (by ring))

end LowEnergy.PreparationPhysicalMaterialSpectralCharge
