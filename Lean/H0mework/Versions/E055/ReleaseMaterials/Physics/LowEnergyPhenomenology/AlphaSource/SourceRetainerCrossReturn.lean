import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceRetainerResolventSquare

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalRetainerResolventSquare
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
local instance RetainerCrossIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
attribute [local irreducible] sourceEqualProjection sourceRetainerReturn sourceFullInitialUpper sourceFullInitialBase
  sourcePinnedResolvent sourcePinnedVelocity sourcePinnedValue sourcePinnedChannel sourcePoleRead sourceStaticCurrent
  sourceResonanceProjection sourceOffPoleReturn sourceBaseCross sourceCurrentSimple actualC actualA sourceProjection

private theorem smul_zero_operator (z : ℂ) : z • (0:SourceOp)=0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply,zero_apply]
  exact smul_zero z

private theorem zero_smul_operator (A : SourceOp) : (0:ℂ) • A=0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply,zero_apply]
  exact zero_smul ℂ (A x)

private theorem adjoint_product (A B : SourceOp) :
    ContinuousLinearMap.adjoint (A*B)=ContinuousLinearMap.adjoint B*ContinuousLinearMap.adjoint A := by
  simp only [ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp]

private theorem pinned_channel_adjoint (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (i : Channel F) :
    ContinuousLinearMap.adjoint (sourcePinnedChannel F n i)=sourcePinnedChannel F n i := by
  cases i with
  | none=>
    have paid:=sourceChannel_selfAdjoint F (none:Channel F)
    change ContinuousLinearMap.adjoint (sourceChannelOp F none)=sourceChannelOp F none at paid
    simpa only [sourcePinnedChannel,sourceChannelOp] using paid
  | some i=>
    simp only [sourcePinnedChannel]
    exact InnerProductSpace.adjoint_rankOne _ _

private theorem resonance_adjoint (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    ContinuousLinearMap.adjoint (sourceResonanceProjection F n 0)=sourceResonanceProjection F n 0 := by
  simp only [sourceResonanceProjection,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · exact pinned_channel_adjoint F n i
  · exact (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=H) (F:=H)).map_zero

/-- The actual zero-velocity subspace is read by the same source resolvent. -/
theorem sourcePinnedResolvent_resonance_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) :
    sourcePinnedResolvent F n zeta*sourceResonanceProjection F n 0=
      zeta⁻¹ • sourceResonanceProjection F n 0 := by
  simp only [sourceResonanceProjection,sourceVelocityGap,add_zero,Finset.mul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases zero : sourcePinnedValue F n i=0
  · simp only [if_pos zero]
    rw [sourcePinnedResolvent_channel F n zeta positive i]
    simp only [zero,Complex.ofReal_zero,mul_zero,add_zero]
  · simp only [if_neg zero,mul_zero,smul_zero_operator]

theorem sourcePinnedResolvent_resonance_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) :
    sourceResonanceProjection F n 0*sourcePinnedResolvent F n zeta=
      zeta⁻¹ • sourceResonanceProjection F n 0 := by
  have left : sourcePinnedVelocity F n*sourceResonanceProjection F n 0=0 := by
    simpa only [Complex.ofReal_zero,neg_zero,zero_smul_operator] using sourceResonance_eigen F n 0
  have self:=sourcePinnedVelocity_selfAdjoint F n
  change ContinuousLinearMap.adjoint (sourcePinnedVelocity F n)=sourcePinnedVelocity F n at self
  have right:=congrArg (fun A : SourceOp=>ContinuousLinearMap.adjoint A) left
  simp only [adjoint_product,resonance_adjoint,self,map_zero] at right
  have pencil : sourceResonanceProjection F n 0*sourcePinnedPencil F n zeta=
      zeta • sourceResonanceProjection F n 0 := by
    simp only [sourcePinnedPencil,mul_add,mul_smul_comm,mul_one,right,smul_zero_operator,add_zero]
  have generated:=congrArg (fun A : SourceOp=>A*sourcePinnedResolvent F n zeta) pencil
  rw [mul_assoc,sourcePinnedResolvent_right F n zeta positive,mul_one,smul_mul_assoc] at generated
  have nonzero : zeta≠0 := by intro zero;rw [zero,Complex.zero_re] at positive;exact lt_irrefl _ positive
  have normalized:=congrArg (fun A : SourceOp=>zeta⁻¹ • A) generated
  rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul] at normalized
  exact normalized.symm

private theorem resonance_limit (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourcePinnedResolvent F n (d:ℂ)) (𝓝[>] 0)
      (𝓝 (sourceResonanceProjection F n 0)) := by
  simpa only [mul_one,inv_one,one_smul] using sourceComplexRadialPinned_return F n 1 (by norm_num)

theorem sourceResonanceProjection_square (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourceResonanceProjection F n 0*sourceResonanceProjection F n 0=sourceResonanceProjection F n 0 := by
  have generated:=(resonance_limit F n).mul_const (sourceResonanceProjection F n 0)
  have equal : (fun d : ℝ=>((d:ℂ) • sourcePinnedResolvent F n (d:ℂ))*sourceResonanceProjection F n 0)=ᶠ[𝓝[>] 0]
      fun _=>sourceResonanceProjection F n 0 := by
    filter_upwards [self_mem_nhdsWithin] with d dp
    rw [smul_mul_assoc,sourcePinnedResolvent_resonance_right F n (d:ℂ) (by simpa using dp),smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr dp.ne'),one_smul]
  exact tendsto_nhds_unique (generated.congr' equal) tendsto_const_nhds

theorem sourceResonanceProjection_equal (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourceEqualProjection F (sourceResonanceProjection F n 0)=sourceResonanceProjection F n 0 := by
  have generated:=(sourceEqualProjection F).continuous.continuousAt.tendsto.comp (resonance_limit F n)
  have equal : (fun d : ℝ=>sourceEqualProjection F ((d:ℂ) • sourcePinnedResolvent F n (d:ℂ)))=ᶠ[𝓝[>] 0]
      fun d=>(d:ℂ) • sourcePinnedResolvent F n (d:ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with d dp
    rw [map_smul,sourcePinnedResolvent_equal F n (d:ℂ) (by simpa using dp)]
  exact tendsto_nhds_unique (generated.congr' equal) (resonance_limit F n)

private theorem off_difference (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (eta : ℝ) (positive : 0<eta) :
    sourceOffPoleReturn F n 0 eta=sourcePinnedResolvent F n (eta:ℂ)-(eta:ℂ)⁻¹ • sourceResonanceProjection F n 0 := by
  have generated:=sourcePinnedResolvent_boundary F n 0 eta positive
  simp only [sourcePoleSide,Complex.ofReal_zero,mul_zero,add_zero] at generated
  rw [generated]
  abel

private theorem off_equal_positive (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (eta : ℝ) (positive : 0<eta) :
    sourceEqualProjection F (sourceOffPoleReturn F n 0 eta)=sourceOffPoleReturn F n 0 eta := by
  simp only [off_difference F n eta positive,map_sub,map_smul,
    sourcePinnedResolvent_equal F n (eta:ℂ) (by simpa using positive),sourceResonanceProjection_equal]

theorem sourceOffPoleReturn_equal (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (eta : ℝ) (nonnegative : 0≤eta) :
    sourceEqualProjection F (sourceOffPoleReturn F n 0 eta)=sourceOffPoleReturn F n 0 eta := by
  rcases lt_or_eq_of_le nonnegative with positive|zero
  · exact off_equal_positive F n eta positive
  · subst eta
    have limit:=(sourceOffPoleReturn_limit F n 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
    have generated:=(sourceEqualProjection F).continuous.continuousAt.tendsto.comp limit
    have equal : (fun d : ℝ=>sourceEqualProjection F (sourceOffPoleReturn F n 0 d))=ᶠ[𝓝[>] 0]
        fun d=>sourceOffPoleReturn F n 0 d := by
      filter_upwards [self_mem_nhdsWithin] with d dp
      exact off_equal_positive F n d dp
    exact tendsto_nhds_unique (generated.congr' equal) limit

private theorem off_orthogonal_positive (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (eta : ℝ) (positive : 0<eta) :
    sourceOffPoleReturn F n 0 eta*sourceResonanceProjection F n 0=0 ∧
      sourceResonanceProjection F n 0*sourceOffPoleReturn F n 0 eta=0 := by
  rw [off_difference F n eta positive]
  constructor
  · simp only [sub_mul,smul_mul_assoc,sourceResonanceProjection_square,
      sourcePinnedResolvent_resonance_right F n (eta:ℂ) (by simpa using positive),sub_self]
  · simp only [mul_sub,mul_smul_comm,sourceResonanceProjection_square,
      sourcePinnedResolvent_resonance_left F n (eta:ℂ) (by simpa using positive),sub_self]

theorem sourceOffPoleReturn_resonance_zero (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (eta : ℝ) (nonnegative : 0≤eta) :
    sourceOffPoleReturn F n 0 eta*sourceResonanceProjection F n 0=0 ∧
      sourceResonanceProjection F n 0*sourceOffPoleReturn F n 0 eta=0 := by
  rcases lt_or_eq_of_le nonnegative with positive|zero
  · exact off_orthogonal_positive F n eta positive
  · subst eta
    have limit:=(sourceOffPoleReturn_limit F n 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
    constructor
    · have generated:=limit.mul_const (sourceResonanceProjection F n 0)
      have equal : (fun d : ℝ=>sourceOffPoleReturn F n 0 d*sourceResonanceProjection F n 0)=ᶠ[𝓝[>] 0] fun _=>0 := by
        filter_upwards [self_mem_nhdsWithin] with d dp
        exact (off_orthogonal_positive F n d dp).1
      exact tendsto_nhds_unique (generated.congr' equal) tendsto_const_nhds
    · have generated:=limit.const_mul (sourceResonanceProjection F n 0)
      have equal : (fun d : ℝ=>sourceResonanceProjection F n 0*sourceOffPoleReturn F n 0 d)=ᶠ[𝓝[>] 0] fun _=>0 := by
        filter_upwards [self_mem_nhdsWithin] with d dp
        exact (off_orthogonal_positive F n d dp).2
      exact tendsto_nhds_unique (generated.congr' equal) tendsto_const_nhds

private theorem retainer_fixed (q : PhysicalResponsePoint) (A : SourceOp)
    (fixed : sourceEqualProjection q.F A=A) (i : Fin 289) :
    sourceEqualProjection q.F (sourceRetainerReturn q.F (A*sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))=
      Complex.I • (A*sourceRetainerSeed q i) := by
  rw [sourceRetainerReturn_apply,map_smul,mul_assoc]
  have generated:=sourceEqualProjection_left_module q.F A
    (sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)*(actualA 0 q.F*sourceProjection))
  simpa only [fixed,sourceRetainerSeed] using congrArg (fun B : SourceOp=>Complex.I • B) generated

/-- Both original retainer cross terms vanish by their own source right-action and spectral orthogonality. -/
theorem sourceBaseCross_zero (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (eta : ℝ) (nonnegative : 0≤eta) (i : Fin 289) : sourceBaseCross q n eta i=0 := by
  have orthogonal:=sourceOffPoleReturn_resonance_zero q.F n eta nonnegative
  rw [sourceBaseCross,retainer_fixed q _ (sourceResonanceProjection_equal q.F n),
    retainer_fixed q _ (sourceOffPoleReturn_equal q.F n eta nonnegative)]
  simp only [mul_smul_comm,←mul_assoc,orthogonal.1,orthogonal.2,zero_mul,smul_zero_operator,neg_zero,sub_zero]

/-- The existing simple full-current coefficient is computed to be zero; the original native gauge and time-reader terms remain. -/
theorem sourceCurrentSimple_zero (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    sourceCurrentSimple q n l r=0 := by
  funext i
  simp only [sourceCurrentSimple,sourceBaseCross_zero q n 0 (by norm_num),map_zero,neg_zero,Pi.zero_apply]

theorem sourceNativeSimple_gauge_time (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    sourceNativeSimple q n l r=
      sourceOriginPair ((3/10:ℂ)*rootTwo*(sourceStaticGaugeCurrent q n l r 1 0-sourceStaticGaugeCurrent q n l r 2 1))+
      sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥsourceStaticCurrent q n l r := by
  rw [sourceNativeSimple,sourceCurrentSimple_zero,Matrix.mulVec_zero,add_zero]

/-- The full causal square is resolved on every original source channel, including escape and resonant channels. -/
theorem sourcePinnedResolvent_square_channels (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) :
    (sourcePinnedResolvent F n zeta)^2=∑i : Channel F,
      ((zeta+Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹)^2 • sourcePinnedChannel F n i := by
  rw [pow_two]
  conv_lhs =>
    rhs
    rw [sourcePinnedResolvent_channels F n zeta positive]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul_comm,sourcePinnedResolvent_channel F n zeta positive,smul_smul,pow_two]

end LowEnergy.PreparationPhysicalRetainerResolventSquare
