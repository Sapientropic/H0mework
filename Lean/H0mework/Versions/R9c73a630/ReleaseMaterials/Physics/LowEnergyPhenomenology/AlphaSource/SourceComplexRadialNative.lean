import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelRadialResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalJointRadialForcing
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
local instance JointRadialNativeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
attribute [local irreducible] sourceEqualProjection sourceRetainerReturn sourceFullInitialUpper
  sourceFullInitialBase sourcePinnedResolvent sourcePoleRead sourceOriginInverse sourceBaseResidue sourceUpperResidue
  sourcePinnedChannel sourcePinnedValue sourceNativeReaderFirst sourceActualNativeResidue

private theorem scaled_positive (zeta : ℂ) (positive : 0<zeta.re) (d : ℝ) (radial : 0<d) :
    0<((d:ℂ)*zeta).re := by
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos radial positive

private theorem nonzero_of_positive (zeta : ℂ) (positive : 0<zeta.re) : zeta≠0 := by
  intro zero
  rw [zero,Complex.zero_re] at positive
  exact lt_irrefl _ positive

private theorem scalar_channel (zeta : ℂ) (positive : 0<zeta.re) (v : ℝ) :
    Tendsto (fun d : ℝ=>(d:ℂ)*((d:ℂ)*zeta+Complex.I*(v:ℂ))⁻¹) (𝓝[>] 0)
      (𝓝 (if v=0 then zeta⁻¹ else 0)) := by
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 0):=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  by_cases zero : v=0
  · rw [if_pos zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with d dp
    simp only [zero,Complex.ofReal_zero,mul_zero,add_zero,mul_inv_rev]
    field_simp [Complex.ofReal_ne_zero.mpr dp.ne',nonzero_of_positive zeta positive]
  · rw [if_neg zero]
    have inverse:=(scalar.mul_const zeta |>.add_const (Complex.I*(v:ℂ))).inv₀
      (by simpa only [zero_mul,zero_add] using mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr zero))
    simpa only [zero_mul] using scalar.mul inverse

/-- The source spectrum generates the complex radial pole, without changing to a real eta approach. -/
theorem sourceComplexRadialPinned_return (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourcePinnedResolvent F n ((d:ℂ)*zeta)) (𝓝[>] 0)
      (𝓝 (zeta⁻¹ • sourceResonanceProjection F n 0)) := by
  have generated:=tendsto_finsetSum Finset.univ (fun i _=>
    (scalar_channel zeta positive (sourcePinnedValue F n i)).smul_const (sourcePinnedChannel F n i))
  have endpoint : (∑i : Channel F,(if sourcePinnedValue F n i=0 then zeta⁻¹ else 0) • sourcePinnedChannel F n i)=
      zeta⁻¹ • sourceResonanceProjection F n 0 := by
    simp only [sourceResonanceProjection,sourceVelocityGap,add_zero,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with resonant
    · rfl
    · apply ContinuousLinearMap.ext
      intro x
      simp only [smul_apply,zero_apply,zero_smul,smul_zero]
  rw [endpoint] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with d dp
  rw [sourcePinnedResolvent_channels F n _ (scaled_positive zeta positive d dp),Finset.smul_sum]
  simp only [smul_smul]

private theorem scaled_base (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (d : ℝ) (i : Fin 289) :
    ((d:ℂ)^2) • sourceBaseResidue q n ((d:ℂ)*zeta) i=
      -(((d:ℂ) • sourcePinnedResolvent q.F n ((d:ℂ)*zeta))*sourceEqualProjection q.F
        (sourceRetainerReturn q.F (((d:ℂ) • sourcePinnedResolvent q.F n ((d:ℂ)*zeta))*
          sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))) := by
  simp only [sourceBaseResidue,sourceUpperResidue,(paidSpatial% projected_origin),
    smul_mul_assoc,map_smul,mul_smul_comm,smul_neg,smul_smul,pow_two]

private theorem base_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (i : Fin 289) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • sourceBaseResidue q n ((d:ℂ)*zeta) i) (𝓝[>] 0)
      (𝓝 ((zeta⁻¹)^2 • sourceStaticBase q n i)) := by
  have inner:=(sourceComplexRadialPinned_return q.F n zeta positive).mul_const
    (sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))
  have retained:=(sourceRetainerReturn q.F).continuous.continuousAt.tendsto.comp inner
  have projected:=(sourceEqualProjection q.F).continuous.continuousAt.tendsto.comp retained
  have generated:=((sourceComplexRadialPinned_return q.F n zeta positive).mul projected).neg
  simp only [scaled_base]
  simpa only [Function.comp_def,sourceStaticBase,smul_mul_assoc,map_smul,
    mul_smul_comm,smul_neg,smul_smul,pow_two] using generated

/-- Both original retainer returns and every one of the 289 current components survive the complex radial limit. -/
theorem sourceComplexRadialCurrent_return (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • sourceFullCurrentResidue q n ((d:ℂ)*zeta) l r)
      (𝓝[>] 0) (𝓝 ((zeta⁻¹)^2 • sourceStaticCurrent q n l r)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have generated:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.continuousAt.tendsto.comp
    (base_return q n zeta positive i)).neg
  simpa only [Function.comp_def,sourceStaticCurrent,sourceFullCurrentResidue,Pi.smul_apply,map_smul,smul_neg] using generated

private theorem current_price_scaled (q : PhysicalResponsePoint) (eta d : ℝ) (l r : RestStateIndex) :
    sourceSpatialCurrentPrice q (d*eta) l r=d⁻¹^2*sourceSpatialCurrentPrice q eta l r := by
  simp only [sourceSpatialCurrentPrice,div_eq_mul_inv,mul_inv_rev,mul_pow,one_mul]
  ring

private theorem gauge_price_scaled (q : PhysicalResponsePoint) (eta d : ℝ) (l r : RestStateIndex) :
    sourceSpatialGaugePrice q (d*eta) l r=d⁻¹*sourceSpatialGaugePrice q eta l r := by
  simp only [sourceSpatialGaugePrice,div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

private theorem scaled_origin_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (d : ℝ) (radial : 0<d) (l r : RestStateIndex) :
    ‖((d:ℂ)^2) • sourceOriginCurrentResidue q n ((d:ℂ)*zeta) l r‖≤
      d*sourceSpatialGaugePrice q zeta.re l r := by
  have bound:=(paidSpatial% origin_bound) q n ((d:ℂ)*zeta) (scaled_positive zeta positive d radial) l r
  have real : ((d:ℂ)*zeta).re=d*zeta.re := by simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [real,gauge_price_scaled] at bound
  rw [norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos radial]
  have coefficient : d^2*(d⁻¹*sourceSpatialGaugePrice q zeta.re l r)=d*sourceSpatialGaugePrice q zeta.re l r := by
    field_simp
  exact (mul_le_mul_of_nonneg_left bound (sq_nonneg d)).trans_eq coefficient

/-- The original source price is uniform over all momentum after the physical double normalization. -/
theorem sourceComplexRadialNative_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (d : ℝ) (radial : 0<d) (l r : RestStateIndex) :
    ‖((d:ℂ)^2) • sourceActualNativeResidue q n ((d:ℂ)*zeta) l r‖≤
      d*sourceSpatialGaugePrice q zeta.re l r+
      ‖sourceReaderLinear‖*(d*‖zeta‖+‖n‖)*sourceSpatialCurrentPrice q zeta.re l r := by
  have real : ((d:ℂ)*zeta).re=d*zeta.re := by simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have current:=(paidSpatial% current_bound) q n ((d:ℂ)*zeta) (scaled_positive zeta positive d radial) l r
  rw [real,current_price_scaled] at current
  have reader:=sourceReaderLinear_bound n ((d:ℂ)*zeta)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos radial] at reader
  have scaledCurrent : ‖((d:ℂ)^2) • sourceFullCurrentResidue q n ((d:ℂ)*zeta) l r‖≤
      sourceSpatialCurrentPrice q zeta.re l r := by
    rw [norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos radial]
    have coefficient : d^2*(d⁻¹^2*sourceSpatialCurrentPrice q zeta.re l r)=sourceSpatialCurrentPrice q zeta.re l r := by
      field_simp [radial.ne']
    exact (mul_le_mul_of_nonneg_left current (sq_nonneg d)).trans_eq coefficient
  rw [sourceActualNativeResidue,smul_add,←Matrix.mulVec_smul]
  apply (norm_add_le _ _).trans
  apply add_le_add (scaled_origin_bound q n zeta positive d radial l r)
  exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul reader scaledCurrent (norm_nonneg _) (by positivity))

private theorem origin_return (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • sourceOriginCurrentResidue q n ((d:ℂ)*zeta) l r)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun d=>norm_nonneg _)) _
    (by simpa only [zero_mul] using (((tendsto_id : Tendsto (fun d : ℝ=>d) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const
      (sourceSpatialGaugePrice q zeta.re l r)))
  filter_upwards [self_mem_nhdsWithin] with d dp
  exact scaled_origin_bound q n zeta positive d dp l r

/-- The full original native forcing returns its double layer on the actual complex radial side. -/
theorem sourceComplexRadialNative_return (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • sourceActualNativeResidue q n ((d:ℂ)*zeta) l r)
      (𝓝[>] 0) (𝓝 ((zeta⁻¹)^2 • sourceStaticNative q n l r)) := by
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)*zeta) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero,zero_mul] using
      ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds).mul_const zeta
  have reader : Tendsto (fun d : ℝ=>sourceNativeReaderFirst (fixedMomentum n ((d:ℂ)*zeta)))
      (𝓝[>] 0) (𝓝 (sourceNativeReaderFirst (fixedMomentum n 0))) := by
    have generated:=(tendsto_const_nhds (x:=sourceNativeReaderFirst (fixedMomentum n 0))).add (scalar.smul_const (sourceNativeReaderFirst (fixedMomentum 0 1)))
    simp only [zero_smul,add_zero] at generated
    exact generated.congr (fun d=>(sourceReaderFirst_static_split n ((d:ℂ)*zeta)).symm)
  have current:=sourceComplexRadialCurrent_return q n zeta positive l r
  have product:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp (reader.prodMk_nhds current)
  have generated:=(origin_return q n zeta positive l r).add product
  simpa only [Function.comp_def,sourceActualNativeResidue,sourceStaticNative,zero_add,smul_add,
    Matrix.mulVec_smul] using generated

/-- Every original slow coordinate reads the same complete complex-radial source return. -/
theorem sourceComplexRadialSlow_return (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) (i : Fin 3) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*sourceSlowRead (sourceActualNativeResidue q n ((d:ℂ)*zeta) l r) ⟨i.val,by omega⟩)
      (𝓝[>] 0) (𝓝 ((zeta⁻¹)^2*sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩)) := by
  have reader : Continuous (fun f : Fin 289→ℂ=>sourceSlowRead f ⟨i.val,by omega⟩) := by
    simp only [sourceSlowRead,show i.val<3 from i.isLt,ite_true]
    fun_prop
  have generated:=reader.continuousAt.tendsto.comp (sourceComplexRadialNative_return q n zeta positive l r)
  simpa only [Function.comp_def,sourceSlowRead,show i.val<3 from i.isLt,ite_true,
    Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] using generated

end LowEnergy.PreparationPhysicalJointRadialForcing
