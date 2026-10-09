import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceRetainerCrossReturn

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
local instance CausalMasterIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
  sourceNativeReaderFirst sourceActualNativeResidue sourceFullCurrentResidue sourceOriginCurrentResidue sourceRetainerSeed

private theorem source_resolvent_denominator (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (i : Channel F) : zeta+Complex.I*(sourcePinnedValue F n i:ℂ)≠0 := by
  intro zero
  have real:=congrArg Complex.re zero
  simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,Complex.zero_re] at real
  exact positive.ne' real

/-- The same causal source inverse generates its full square as the actual complex-frequency derivative. -/
theorem sourcePinnedResolvent_derivative (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) :
    HasDerivAt (sourcePinnedResolvent F n) (-(sourcePinnedResolvent F n zeta)^2) zeta := by
  have entry (i : Channel F) :
      HasDerivAt (fun z : ℂ=>(z+Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹ • sourcePinnedChannel F n i)
        (-((zeta+Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹)^2 • sourcePinnedChannel F n i) zeta := by
    have generated:=(((hasDerivAt_id zeta).add_const (Complex.I*(sourcePinnedValue F n i:ℂ))).inv
      (source_resolvent_denominator F n zeta positive i)).smul_const (sourcePinnedChannel F n i)
    convert! generated using 1
    simp only [one_div,inv_pow,neg_div,id_eq]
  have generated:=HasDerivAt.fun_sum (fun i (_ : i∈Finset.univ)=>entry i)
  have derivative : (∑i : Channel F,-((zeta+Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹)^2 • sourcePinnedChannel F n i)=
      -(sourcePinnedResolvent F n zeta)^2 := by
    rw [sourcePinnedResolvent_square_channels F n zeta positive,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply ContinuousLinearMap.ext
    intro x
    simp only [smul_apply,neg_apply]
    exact neg_smul _ _
  rw [derivative] at generated
  apply generated.congr_of_eventuallyEq
  have near : ∀ᶠ z : ℂ in 𝓝 zeta,0<z.re:=Complex.continuous_re.continuousAt.eventually_const_lt positive
  filter_upwards [near] with z zp
  exact sourcePinnedResolvent_channels F n z zp

/-- Original full289 seeds and the same independent two-Green reader generate the first-order causal current. -/
def sourceMasterCurrent (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ := fun i=>
  -Complex.I*sourcePoleRead q.epsilon q.precision 0 0 l r
    (sourcePinnedResolvent q.F n zeta*sourceRetainerSeed q i)

theorem sourceMasterCurrent_derivative (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    HasDerivAt (fun z : ℂ=>sourceMasterCurrent q n z l r) (sourceFullCurrentResidue q n zeta l r) zeta := by
  apply hasDerivAt_pi.mpr
  intro i
  have product:=(sourcePinnedResolvent_derivative q.F n zeta positive).mul_const (sourceRetainerSeed q i)
  have read:=(sourcePoleRead q.epsilon q.precision 0 0 l r).hasFDerivAt.comp_hasDerivAt zeta product
  have generated:=read.const_mul (-Complex.I)
  convert! generated using 1
  rw [sourceFullCurrentResidue_square q n zeta positive l r i]
  have operatorNeg : -(sourcePinnedResolvent q.F n zeta)^2*sourceRetainerSeed q i=
      -((sourcePinnedResolvent q.F n zeta)^2*sourceRetainerSeed q i) := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  rw [operatorNeg,map_neg]
  ring

private theorem reader_derivative (n : PhysicalMomentum) (zeta : ℂ) :
    HasDerivAt (fun z : ℂ=>sourceNativeReaderFirst (fixedMomentum n z))
      (sourceNativeReaderFirst (fixedMomentum 0 1)) zeta := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have point (z : ℂ) : sourceNativeReaderFirst (fixedMomentum n z) i j=
      sourceNativeReaderFirst (fixedMomentum n 0) i j+z*sourceNativeReaderFirst (fixedMomentum 0 1) i j := by
    rw [sourceReaderFirst_static_split]
    rfl
  have generated:=((hasDerivAt_id zeta).mul_const
    (sourceNativeReaderFirst (fixedMomentum 0 1) i j)).const_add (sourceNativeReaderFirst (fixedMomentum n 0) i j)
  simp only [one_mul] at generated
  exact generated.congr_of_eventuallyEq (Eventually.of_forall point)

def sourceMasterNative (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceNativeReaderFirst (fixedMomentum n zeta)*ᵥsourceMasterCurrent q n zeta l r

def sourceMasterNativeDerivative (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥsourceMasterCurrent q n zeta l r+
    sourceNativeReaderFirst (fixedMomentum n zeta)*ᵥsourceFullCurrentResidue q n zeta l r

theorem sourceMasterNative_derivative (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    HasDerivAt (fun z : ℂ=>sourceMasterNative q n z l r) (sourceMasterNativeDerivative q n zeta l r) zeta := by
  have reader:=reader_derivative n zeta
  have current:=sourceMasterCurrent_derivative q n zeta positive l r
  apply hasDerivAt_pi.mpr
  intro i
  have entry (j : Fin 289) :=
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp reader i) j).mul (hasDerivAt_pi.mp current j))
  simpa only [sourceMasterNative,sourceMasterNativeDerivative,Matrix.mulVec,dotProduct,Pi.add_apply,Pi.mul_apply,
    Finset.sum_add_distrib] using HasDerivAt.fun_sum (fun j (_ : j∈Finset.univ)=>entry j)

private theorem slow_derivative (f : ℂ→Fin 289→ℂ) (f' : Fin 289→ℂ) (zeta : ℂ)
    (generated : HasDerivAt f f' zeta) (i : Fin 5) :
    HasDerivAt (fun z : ℂ=>sourceSlowRead (f z) i) (sourceSlowRead f' i) zeta := by
  unfold sourceSlowRead
  split_ifs
  · change HasDerivAt (fun z : ℂ=>∑j : Fin 289,slowFastFrame.transpose (fiveIndex i) j*f z j)
      (∑j : Fin 289,slowFastFrame.transpose (fiveIndex i) j*f' j) zeta
    exact HasDerivAt.fun_sum (fun j (_ : j∈Finset.univ)=>(hasDerivAt_pi.mp generated j).const_mul _)
  · exact hasDerivAt_const zeta 0

def sourceMasterChannel (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) : ℂ :=
  (sourceChargedDenominator n zeta i)⁻¹*sourceSlowRead (sourceMasterNative q n zeta l r) ⟨i.val,by omega⟩

def sourceMasterChannelDerivative (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) : ℂ :=
  -(2*(sourceChargedTemporalCoefficient i:ℂ)*zeta)*((sourceChargedDenominator n zeta i)⁻¹)^2*
      sourceSlowRead (sourceMasterNative q n zeta l r) ⟨i.val,by omega⟩+
    (sourceChargedDenominator n zeta i)⁻¹*sourceSlowRead (sourceMasterNativeDerivative q n zeta l r) ⟨i.val,by omega⟩

def sourceMasterChannelCorrection (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) : ℂ :=
  (sourceChargedDenominator n zeta i)⁻¹*sourceSlowRead (sourceOriginCurrentResidue q n zeta l r) ⟨i.val,by omega⟩-
    (sourceChargedDenominator n zeta i)⁻¹*sourceSlowRead
      (sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥsourceMasterCurrent q n zeta l r) ⟨i.val,by omega⟩+
    (2*(sourceChargedTemporalCoefficient i:ℂ)*zeta)*((sourceChargedDenominator n zeta i)⁻¹)^2*
      sourceSlowRead (sourceMasterNative q n zeta l r) ⟨i.val,by omega⟩

/-- Every original field denominator and reader derivative is retained in the same causal master. -/
theorem sourceMasterChannel_derivative (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3) :
    HasDerivAt (fun z : ℂ=>sourceMasterChannel q n z l r i)
      (sourceMasterChannelDerivative q n (sourcePoleSide c eta) l r i) (sourcePoleSide c eta) := by
  let zeta:=sourcePoleSide c eta
  have zp : 0<zeta.re:=by simpa only [zeta,sourcePoleSide,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero] using positive
  have denominator : HasDerivAt (fun z : ℂ=>sourceChargedDenominator n z i)
      (2*(sourceChargedTemporalCoefficient i:ℂ)*zeta) zeta := by
    have generated:=((hasDerivAt_id zeta).pow 2).const_mul (sourceChargedTemporalCoefficient i:ℂ) |>.const_add
      ((sourceChargedSpatialCoefficient i:ℂ)*(spatialSquare n:ℂ))
    convert! generated using 1
    simp only [mul_one,id_eq]
    ring
  have inverse:=denominator.inv (sourceChargedDenominator_nonzero n c eta frequency positive i)
  have native:=slow_derivative (fun z=>sourceMasterNative q n z l r)
    (sourceMasterNativeDerivative q n zeta l r) zeta (sourceMasterNative_derivative q n zeta zp l r) ⟨i.val,by omega⟩
  convert! inverse.mul native using 1
  simp only [sourceMasterChannelDerivative,div_eq_mul_inv,inv_pow,Pi.inv_apply,zeta]

/-- The original complete channel is the master derivative plus its actual gauge, reader-time and field-denominator corrections. -/
theorem sourceCommonCausalChannel_master (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) :
    sourceCommonCausalChannel q n zeta l r i=
      sourceMasterChannelDerivative q n zeta l r i+sourceMasterChannelCorrection q n zeta l r i := by
  simp only [sourceCommonCausalChannel,sourceMasterChannelDerivative,sourceMasterChannelCorrection,
    sourceMasterNativeDerivative,sourceActualNativeResidue,sourceSlowRead,show i.val<3 from i.isLt,ite_true,
    Matrix.mulVec_add,Pi.add_apply]
  ring


def sourceMasterCurrentPrice (q : PhysicalResponsePoint) (l r : RestStateIndex) : ℝ :=
  ‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*∑i : Fin 289,‖sourceRetainerSeed q i‖

private theorem master_price_nonneg (q : PhysicalResponsePoint) (l r : RestStateIndex) :
    0≤ sourceMasterCurrentPrice q l r := by unfold sourceMasterCurrentPrice;positivity

private theorem master_current_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    ‖sourceMasterCurrent q n zeta l r‖≤ sourceMasterCurrentPrice q l r/zeta.re := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (master_price_nonneg q l r) positive.le)).mpr
  intro i
  have single : ‖sourceRetainerSeed q i‖≤∑j : Fin 289,‖sourceRetainerSeed q j‖:=
    Finset.single_le_sum (fun j _=>norm_nonneg _) (Finset.mem_univ i)
  simp only [sourceMasterCurrent,norm_mul,norm_neg,Complex.norm_I,one_mul]
  calc
    _≤‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*
        ‖sourcePinnedResolvent q.F n zeta*sourceRetainerSeed q i‖:=
      (sourcePoleRead q.epsilon q.precision 0 0 l r).le_opNorm _
    _≤‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*
        (‖sourcePinnedResolvent q.F n zeta‖*‖sourceRetainerSeed q i‖):=by gcongr;exact norm_mul_le _ _
    _≤‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*((1/zeta.re)*(∑j : Fin 289,‖sourceRetainerSeed q j‖)) := by
      gcongr
      exact sourcePinnedResolvent_price q.F n zeta positive
    _=_:=by unfold sourceMasterCurrentPrice;ring

private theorem source_linear_shape (zeta : ℂ) (n : PhysicalMomentum) :
    ‖zeta‖+‖n‖≤(‖zeta‖+1)*(1+‖n‖) := by
  nlinarith [norm_nonneg zeta,norm_nonneg n,mul_nonneg (norm_nonneg zeta) (norm_nonneg n)]

private theorem master_native_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    ‖sourceMasterNative q n zeta l r‖≤
      (‖sourceReaderLinear‖*(‖zeta‖+1)*(sourceMasterCurrentPrice q l r/zeta.re))*(1+‖n‖) := by
  unfold sourceMasterNative
  calc
    _≤‖sourceNativeReaderFirst (fixedMomentum n zeta)‖*‖sourceMasterCurrent q n zeta l r‖:=Matrix.linfty_opNorm_mulVec _ _
    _≤(‖sourceReaderLinear‖*(‖zeta‖+‖n‖))*(sourceMasterCurrentPrice q l r/zeta.re):=
      mul_le_mul (sourceReaderLinear_bound n zeta) (master_current_bound q n zeta positive l r)
        (norm_nonneg _) (by positivity)
    _≤(‖sourceReaderLinear‖*((‖zeta‖+1)*(1+‖n‖)))*(sourceMasterCurrentPrice q l r/zeta.re) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (source_linear_shape zeta n) (norm_nonneg _))
        (div_nonneg (master_price_nonneg q l r) positive.le)
    _=_:=by ring

private theorem master_native_derivative_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : ℂ) (positive : 0<zeta.re) (l r : RestStateIndex) :
    ‖sourceMasterNativeDerivative q n zeta l r‖≤
      (‖sourceNativeReaderFirst (fixedMomentum 0 1)‖*(sourceMasterCurrentPrice q l r/zeta.re)+
        ‖sourceReaderLinear‖*(‖zeta‖+1)*sourceSpatialCurrentPrice q zeta.re l r)*(1+‖n‖) := by
  have current:=(paidSpatial% current_bound) q n zeta positive l r
  have currentPrice : 0≤ sourceSpatialCurrentPrice q zeta.re l r:=by unfold sourceSpatialCurrentPrice;positivity
  have masterPrice:=div_nonneg (master_price_nonneg q l r) positive.le
  unfold sourceMasterNativeDerivative
  calc
    _≤‖sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥsourceMasterCurrent q n zeta l r‖+
        ‖sourceNativeReaderFirst (fixedMomentum n zeta)*ᵥsourceFullCurrentResidue q n zeta l r‖:=norm_add_le _ _
    _≤‖sourceNativeReaderFirst (fixedMomentum 0 1)‖*(sourceMasterCurrentPrice q l r/zeta.re)+
        (‖sourceReaderLinear‖*(‖zeta‖+‖n‖))*sourceSpatialCurrentPrice q zeta.re l r := by
      apply add_le_add
      · exact (Matrix.linfty_opNorm_mulVec _ _).trans
          (mul_le_mul_of_nonneg_left (master_current_bound q n zeta positive l r) (norm_nonneg _))
      · exact (Matrix.linfty_opNorm_mulVec _ _).trans
          (mul_le_mul (sourceReaderLinear_bound n zeta) current (norm_nonneg _) (by positivity))
    _≤(‖sourceNativeReaderFirst (fixedMomentum 0 1)‖*(sourceMasterCurrentPrice q l r/zeta.re))*(1+‖n‖)+
        (‖sourceReaderLinear‖*((‖zeta‖+1)*(1+‖n‖)))*sourceSpatialCurrentPrice q zeta.re l r := by
      apply add_le_add
      · exact le_mul_of_one_le_right (mul_nonneg (norm_nonneg _) masterPrice) (by linarith [norm_nonneg n])
      · gcongr
        exact source_linear_shape zeta n
    _=_:=by ring

def sourceMasterChannelPrice (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex) (i : Fin 3) : ℝ :=
  sourceChargedDenominatorPrice c eta i*‖slowFastFrame.transpose‖*
    (‖sourceReaderLinear‖*(‖sourcePoleSide c eta‖+1)*(sourceMasterCurrentPrice q l r/eta))

def sourceMasterChannelDerivativePrice (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex) (i : Fin 3) : ℝ :=
  ‖slowFastFrame.transpose‖*
    (‖2*(sourceChargedTemporalCoefficient i:ℂ)*sourcePoleSide c eta‖*(sourceChargedDenominatorPrice c eta i)^2*
      (‖sourceReaderLinear‖*(‖sourcePoleSide c eta‖+1)*(sourceMasterCurrentPrice q l r/eta))+
    sourceChargedDenominatorPrice c eta i*
      (‖sourceNativeReaderFirst (fixedMomentum 0 1)‖*(sourceMasterCurrentPrice q l r/eta)+
        ‖sourceReaderLinear‖*(‖sourcePoleSide c eta‖+1)*sourceSpatialCurrentPrice q eta l r))

private theorem side_positive (c eta : ℝ) (positive : 0<eta) : 0<(sourcePoleSide c eta).re := by
  simpa [sourcePoleSide] using positive

private theorem master_channel_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3) :
    ‖sourceMasterChannel q n (sourcePoleSide c eta) l r i‖≤ sourceMasterChannelPrice q c eta l r i*(1+‖n‖) := by
  have native:=master_native_bound q n (sourcePoleSide c eta) (side_positive c eta positive) l r
  have real : (sourcePoleSide c eta).re=eta := by simp [sourcePoleSide]
  rw [real] at native
  have slow:=(paidSpatial% slow_bound) (sourceMasterNative q n (sourcePoleSide c eta) l r) ⟨i.val,by omega⟩
  have inverse:=sourceChargedDenominator_bound n c eta frequency positive i
  have denNonneg : 0≤ sourceChargedDenominatorPrice c eta i:=by unfold sourceChargedDenominatorPrice;positivity
  have masterNonneg:=div_nonneg (master_price_nonneg q l r) positive.le
  rw [sourceMasterChannel,norm_mul]
  apply (mul_le_mul inverse (slow.trans (mul_le_mul_of_nonneg_left native (norm_nonneg _))) (norm_nonneg _) denNonneg).trans_eq
  unfold sourceMasterChannelPrice
  ring

private theorem master_channel_derivative_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3) :
    ‖sourceMasterChannelDerivative q n (sourcePoleSide c eta) l r i‖≤
      sourceMasterChannelDerivativePrice q c eta l r i*(1+‖n‖) := by
  let zeta:=sourcePoleSide c eta
  have zp:=side_positive c eta positive
  have real : zeta.re=eta:=by simp [zeta,sourcePoleSide]
  have native:=master_native_bound q n zeta zp l r
  have derivative:=master_native_derivative_bound q n zeta zp l r
  rw [real] at native derivative
  have slow:=(paidSpatial% slow_bound) (sourceMasterNative q n zeta l r) ⟨i.val,by omega⟩
  have slowDerivative:=(paidSpatial% slow_bound) (sourceMasterNativeDerivative q n zeta l r) ⟨i.val,by omega⟩
  have inverse:=sourceChargedDenominator_bound n c eta frequency positive i
  have denNonneg : 0≤ sourceChargedDenominatorPrice c eta i:=by unfold sourceChargedDenominatorPrice;positivity
  have masterNonneg:=div_nonneg (master_price_nonneg q l r) positive.le
  have currentNonneg : 0≤ sourceSpatialCurrentPrice q eta l r:=by unfold sourceSpatialCurrentPrice;positivity
  unfold sourceMasterChannelDerivative
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_neg,norm_pow]
  calc
    _≤‖2*(sourceChargedTemporalCoefficient i:ℂ)*zeta‖*(sourceChargedDenominatorPrice c eta i)^2*
        (‖slowFastFrame.transpose‖*((‖sourceReaderLinear‖*(‖zeta‖+1)*(sourceMasterCurrentPrice q l r/eta))*(1+‖n‖)))+
      sourceChargedDenominatorPrice c eta i*
        (‖slowFastFrame.transpose‖*((‖sourceNativeReaderFirst (fixedMomentum 0 1)‖*(sourceMasterCurrentPrice q l r/eta)+
          ‖sourceReaderLinear‖*(‖zeta‖+1)*sourceSpatialCurrentPrice q eta l r)*(1+‖n‖))) := by
      apply add_le_add
      · simp only [norm_mul,zeta]
        gcongr
        exact slow.trans (mul_le_mul_of_nonneg_left native (norm_nonneg _))
      · exact mul_le_mul inverse (slowDerivative.trans (mul_le_mul_of_nonneg_left derivative (norm_nonneg _)))
          (norm_nonneg _) denNonneg
    _=_:=by unfold sourceMasterChannelDerivativePrice;dsimp only [zeta];ring

private theorem slow_continuous {D : Type*} [TopologicalSpace D] (f : D→Fin 289→ℂ)
    (continuous : Continuous f) (i : Fin 5) : Continuous (fun x=>sourceSlowRead (f x) i) := by
  unfold sourceSlowRead
  split_ifs <;> fun_prop

private theorem master_current_continuous (q : PhysicalResponsePoint) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) : Continuous (fun n : PhysicalMomentum=>sourceMasterCurrent q n zeta l r) := by
  have resolvent:=(paidSpatial% resolvent_continuous) q.F zeta positive
  apply continuous_pi
  intro i
  exact (((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.comp
    (resolvent.mul_const (sourceRetainerSeed q i))).const_mul (-Complex.I)).congr (fun _=>rfl)

private theorem reader_continuous (zeta : ℂ) :
    Continuous (fun n : PhysicalMomentum=>sourceNativeReaderFirst (fixedMomentum n zeta)) := by
  simp_rw [←sourceReaderLinear_generated]
  exact sourceReaderLinear.continuous.comp ((paidSpatial% physical_point_continuous) zeta)

private theorem master_native_continuous (q : PhysicalResponsePoint) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) : Continuous (fun n : PhysicalMomentum=>sourceMasterNative q n zeta l r) :=
  ((reader_continuous zeta).matrix_mulVec (master_current_continuous q zeta positive l r)).congr (fun _=>rfl)

private theorem master_native_derivative_continuous (q : PhysicalResponsePoint) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) : Continuous (fun n : PhysicalMomentum=>sourceMasterNativeDerivative q n zeta l r) := by
  have current:=master_current_continuous q zeta positive l r
  have actual:=(paidSpatial% current_continuous) q zeta positive l r
  exact ((continuous_const.matrix_mulVec current).add ((reader_continuous zeta).matrix_mulVec actual)).congr (fun _=>rfl)

private theorem denominator_continuous (c eta : ℝ) (frequency : c≠0) (positive : 0<eta) (i : Fin 3) :
    Continuous (fun n : PhysicalMomentum=>(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹) := by
  have base : Continuous (fun n : PhysicalMomentum=>sourceChargedDenominator n (sourcePoleSide c eta) i) := by
    unfold sourceChargedDenominator spatialSquare
    fun_prop
  exact base.inv₀ (fun n=>sourceChargedDenominator_nonzero n c eta frequency positive i)

private theorem master_channel_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3) :
    Continuous (fun n : PhysicalMomentum=>sourceMasterChannel q n (sourcePoleSide c eta) l r i) := by
  have slow:=slow_continuous _ (master_native_continuous q (sourcePoleSide c eta) (side_positive c eta positive) l r) ⟨i.val,by omega⟩
  exact ((denominator_continuous c eta frequency positive i).mul slow).congr (fun _=>rfl)

private theorem master_channel_derivative_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3) :
    Continuous (fun n : PhysicalMomentum=>sourceMasterChannelDerivative q n (sourcePoleSide c eta) l r i) := by
  have inverse:=denominator_continuous c eta frequency positive i
  have slow:=slow_continuous _ (master_native_continuous q (sourcePoleSide c eta) (side_positive c eta positive) l r) ⟨i.val,by omega⟩
  have derivative:=slow_continuous _ (master_native_derivative_continuous q (sourcePoleSide c eta) (side_positive c eta positive) l r) ⟨i.val,by omega⟩
  exact (((continuous_const.mul (inverse.pow 2)).mul slow).add (inverse.mul derivative)).congr (fun _=>rfl)

private theorem side_re_im (z : ℂ) : sourcePoleSide z.im z.re=z := by
  apply Complex.ext <;> simp [sourcePoleSide]

private theorem master_price_continuousAt (q : PhysicalResponsePoint) (l r : RestStateIndex) (i : Fin 3)
    (zeta : ℂ) (positive : 0<zeta.re) (frequency : zeta.im≠0) :
    ContinuousAt (fun z : ℂ=>sourceMasterChannelDerivativePrice q z.im z.re l r i) zeta := by
  have etaNZ:=positive.ne'
  have denNZ : 2*sourceChargedTemporalCoefficient i*zeta.re*zeta.im≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (sourceChargedTemporalCoefficient_nonzero i)) etaNZ) frequency
  have absNZ:=abs_ne_zero.mpr denNZ
  unfold sourceMasterChannelDerivativePrice sourceSpatialCurrentPrice sourceChargedDenominatorPrice
  simp only [side_re_im]
  fun_prop

private theorem master_test_integrable (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun n : PhysicalMomentum=>(1+‖n‖)*‖test n‖) := by
  have paid:=test.integrable.norm.add (test.integrable_pow_mul volume 1)
  apply paid.congr
  filter_upwards with n
  simp only [Pi.add_apply,pow_one]
  ring

private theorem physical_shape (n : PhysicalMomentum) : 1+‖sourceSpatialMomentum n‖≤(1+2*Real.pi)*(1+‖n‖) := by
  have positive : 0<2*Real.pi:=by positivity
  simp only [sourceSpatialMomentum,norm_smul,Real.norm_eq_abs,abs_of_pos positive]
  nlinarith [norm_nonneg n]

private def masterIntegrand (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) : ℂ :=
  sourceSpatialPhase n x*test n*sourceMasterChannel q (sourceSpatialMomentum n) zeta l r i

private def masterDerivativeIntegrand (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) : ℂ :=
  sourceSpatialPhase n x*test n*sourceMasterChannelDerivative q (sourceSpatialMomentum n) zeta l r i

private theorem master_integrand_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) :
    ‖masterIntegrand q (sourcePoleSide c eta) l r i test x n‖≤
      (sourceMasterChannelPrice q c eta l r i*(1+2*Real.pi))*((1+‖n‖)*‖test n‖) := by
  have priceNonneg : 0≤ sourceMasterChannelPrice q c eta l r i := by
    unfold sourceMasterChannelPrice sourceChargedDenominatorPrice
    have master:=master_price_nonneg q l r
    positivity
  rw [masterIntegrand,norm_mul,norm_mul,(paidRadialGreen% phase_norm),one_mul]
  calc
    _≤‖test n‖*(sourceMasterChannelPrice q c eta l r i*(1+‖sourceSpatialMomentum n‖)) :=
      mul_le_mul_of_nonneg_left (master_channel_bound q _ c eta frequency positive l r i) (norm_nonneg _)
    _≤‖test n‖*(sourceMasterChannelPrice q c eta l r i*((1+2*Real.pi)*(1+‖n‖))) := by
      gcongr
      exact physical_shape n
    _=_:=by ring

private theorem master_derivative_integrand_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) :
    ‖masterDerivativeIntegrand q (sourcePoleSide c eta) l r i test x n‖≤
      (sourceMasterChannelDerivativePrice q c eta l r i*(1+2*Real.pi))*((1+‖n‖)*‖test n‖) := by
  have priceNonneg : 0≤ sourceMasterChannelDerivativePrice q c eta l r i := by
    unfold sourceMasterChannelDerivativePrice sourceChargedDenominatorPrice sourceSpatialCurrentPrice
    have master:=master_price_nonneg q l r
    positivity
  rw [masterDerivativeIntegrand,norm_mul,norm_mul,(paidRadialGreen% phase_norm),one_mul]
  calc
    _≤‖test n‖*(sourceMasterChannelDerivativePrice q c eta l r i*(1+‖sourceSpatialMomentum n‖)) :=
      mul_le_mul_of_nonneg_left (master_channel_derivative_bound q _ c eta frequency positive l r i) (norm_nonneg _)
    _≤‖test n‖*(sourceMasterChannelDerivativePrice q c eta l r i*((1+2*Real.pi)*(1+‖n‖))) := by
      gcongr
      exact physical_shape n
    _=_:=by ring

private theorem master_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (masterIntegrand q (sourcePoleSide c eta) l r i test x) := by
  have momentum : Continuous sourceSpatialMomentum := by unfold sourceSpatialMomentum;fun_prop
  have channel:=(master_channel_continuous q c eta frequency positive l r i).comp momentum
  have continuous : Continuous (masterIntegrand q (sourcePoleSide c eta) l r i test x) := by
    unfold masterIntegrand sourceSpatialPhase
    fun_prop
  exact ((master_test_integrable test).const_mul _).mono' continuous.aestronglyMeasurable
    (Eventually.of_forall (master_integrand_bound q c eta frequency positive l r i test x))

private theorem master_derivative_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (masterDerivativeIntegrand q (sourcePoleSide c eta) l r i test x) := by
  have momentum : Continuous sourceSpatialMomentum := by unfold sourceSpatialMomentum;fun_prop
  have channel:=(master_channel_derivative_continuous q c eta frequency positive l r i).comp momentum
  have continuous : Continuous (masterDerivativeIntegrand q (sourcePoleSide c eta) l r i test x) := by
    unfold masterDerivativeIntegrand sourceSpatialPhase
    fun_prop
  exact ((master_test_integrable test).const_mul _).mono' continuous.aestronglyMeasurable
    (Eventually.of_forall (master_derivative_integrand_bound q c eta frequency positive l r i test x))


def sourceMasterSpatialChannel (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,masterIntegrand q zeta l r i test x n

def sourceMasterSpatialChannelDerivative (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,masterDerivativeIntegrand q zeta l r i test x n

def sourceMasterSpatialChannelCorrection (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*sourceMasterChannelCorrection q (sourceSpatialMomentum n) zeta l r i

/-- The original source prices justify the complete spatial master derivative on its actual causal side. -/
theorem sourceMasterSpatialChannel_derivative (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun z : ℂ=>sourceMasterSpatialChannel q z l r i test x)
      (sourceMasterSpatialChannelDerivative q (sourcePoleSide c eta) l r i test x) (sourcePoleSide c eta) := by
  let zeta:=sourcePoleSide c eta
  have rePos:=side_positive c eta positive
  have imNZ : zeta.im≠0:=by simpa [zeta,sourcePoleSide] using frequency
  let price : ℂ→ℝ:=fun z=>sourceMasterChannelDerivativePrice q z.im z.re l r i
  let localDomain : Set ℂ:={z | 0<z.re ∧ z.im≠0 ∧ price z≤price zeta+1}
  have priceContinuous : ContinuousAt price zeta:=master_price_continuousAt q l r i zeta rePos imNZ
  have nearPrice : ∀ᶠ z in 𝓝 zeta,price z≤price zeta+1 :=
    (priceContinuous.eventually_lt_const (by linarith : price zeta<price zeta+1)).mono (fun _ h=>h.le)
  have nearPositive : ∀ᶠ z : ℂ in 𝓝 zeta,0<z.re:=Complex.continuous_re.continuousAt.eventually_const_lt rePos
  have nearImaginary : ∀ᶠ z : ℂ in 𝓝 zeta,z.im≠0:=Complex.continuous_im.continuousAt.eventually_ne imNZ
  have near : localDomain∈𝓝 zeta := by
    filter_upwards [nearPositive,nearImaginary,nearPrice] with z zp zi zb
    exact ⟨zp,zi,zb⟩
  have generated:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀:=zeta) (μ:=volume) (s:=localDomain) near
    (F:=fun z n=>masterIntegrand q z l r i test x n)
    (F':=fun z n=>masterDerivativeIntegrand q z l r i test x n)
    (bound:=fun n=>((price zeta+1)*(1+2*Real.pi))*((1+‖n‖)*‖test n‖))
    (by
      filter_upwards [nearPositive,nearImaginary] with z zp zi
      have paid:=(master_integrable q z.im z.re zi zp l r i test x).aestronglyMeasurable
      simpa only [side_re_im] using paid)
    (master_integrable q c eta frequency positive l r i test x)
    (master_derivative_integrable q c eta frequency positive l r i test x).aestronglyMeasurable
    (Eventually.of_forall (fun n z hz=>by
      have paid:=master_derivative_integrand_bound q z.im z.re hz.2.1 hz.1 l r i test x n
      rw [side_re_im] at paid
      apply paid.trans
      gcongr
      exact hz.2.2))
    ((master_test_integrable test).const_mul _)
    (Eventually.of_forall (fun n z hz=>by
      have paid:=(sourceMasterChannel_derivative q (sourceSpatialMomentum n) z.im z.re hz.2.1 hz.1 l r i).const_mul
        (sourceSpatialPhase n x*test n)
      simpa only [side_re_im,masterIntegrand,masterDerivativeIntegrand] using paid))
  exact generated.2

private theorem correction_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun n : PhysicalMomentum=>sourceSpatialPhase n x*test n*
      sourceMasterChannelCorrection q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i) := by
  have original:=sourceCommonMoment_integrable q c eta frequency positive l r i 0 0 test x
  have derivative:=master_derivative_integrable q c eta frequency positive l r i test x
  apply (original.sub derivative).congr
  filter_upwards with n
  simp only [Pi.sub_apply,sourceCommonMomentIntegrand,pow_zero,one_mul,masterDerivativeIntegrand]
  rw [sourceCommonCausalChannel_master]
  ring

/-- The same complete weighted source channel is the spatial master derivative plus every source-generated correction. -/
theorem sourceCommonSpatialMoment_master (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceCommonSpatialMoment q c eta l r i 0 0 test x=
      sourceMasterSpatialChannelDerivative q (sourcePoleSide c eta) l r i test x+
        sourceMasterSpatialChannelCorrection q (sourcePoleSide c eta) l r i test x := by
  rw [sourceMasterSpatialChannelDerivative,sourceMasterSpatialChannelCorrection,
    ←integral_add (master_derivative_integrable q c eta frequency positive l r i test x)
      (correction_integrable q c eta frequency positive l r i test x)]
  unfold sourceCommonSpatialMoment
  apply integral_congr_ae
  filter_upwards with n
  simp only [sourceCommonMomentIntegrand,pow_zero,one_mul,masterDerivativeIntegrand]
  rw [sourceCommonCausalChannel_master]
  ring

def sourceMasterSpatialField (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceMasterSpatialChannel q zeta l r i test x • sourceCommonOriginColumn i

def sourceMasterSpatialFieldDerivative (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceMasterSpatialChannelDerivative q zeta l r i test x • sourceCommonOriginColumn i

def sourceMasterSpatialFieldCorrection (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceMasterSpatialChannelCorrection q zeta l r i test x • sourceCommonOriginColumn i

private theorem master_field_derivative (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun z : ℂ=>sourceMasterSpatialField q z l r test x)
      (sourceMasterSpatialFieldDerivative q (sourcePoleSide c eta) l r test x) (sourcePoleSide c eta) :=
  HasDerivAt.fun_sum (fun i (_ : i∈Finset.univ)=>(sourceMasterSpatialChannel_derivative q c eta frequency positive l r i test x).smul_const _)

theorem sourceCommonSpatialField_master (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceCommonSpatialField q c eta l r test x=
      sourceMasterSpatialFieldDerivative q (sourcePoleSide c eta) l r test x+
        sourceMasterSpatialFieldCorrection q (sourcePoleSide c eta) l r test x := by
  rw [sourceCommonSpatialField_generated q c eta frequency positive]
  simp only [sourceCommonSpatialMoment_master q c eta frequency positive,add_smul,Finset.sum_add_distrib,
    sourceMasterSpatialFieldDerivative,sourceMasterSpatialFieldCorrection]

def sourceActualMasterSpatialField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (zeta : ℂ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceMasterSpatialField q zeta l r test x

def sourceActualMasterSpatialDerivative (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (zeta : ℂ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceMasterSpatialFieldDerivative q zeta l r test x

def sourceActualMasterSpatialCorrection (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (zeta : ℂ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceMasterSpatialFieldCorrection q zeta l r test x

/-- Actual source64 and all289 fields are carried by the same causal master derivative. -/
theorem sourceActualMasterSpatial_derivative (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (frequency : c≠0) (positive : 0<eta) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun z : ℂ=>sourceActualMasterSpatialField q sL eL sR eR z test x)
      (sourceActualMasterSpatialDerivative q sL eL sR eR (sourcePoleSide c eta) test x) (sourcePoleSide c eta) :=
  HasDerivAt.fun_sum (fun l (_ : l∈Finset.univ)=>HasDerivAt.fun_sum (fun r (_ : r∈Finset.univ)=>
    (master_field_derivative q c eta frequency positive l r test x).const_smul
      (sourceActualPreparedWeight 0 0 sL eL sR eR l r)))

theorem sourceActualSpatialField_master (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (frequency : c≠0) (positive : 0<eta) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualSpatialField q sL eL sR eR c eta test x=
      sourceActualMasterSpatialDerivative q sL eL sR eR (sourcePoleSide c eta) test x+
        sourceActualMasterSpatialCorrection q sL eL sR eR (sourcePoleSide c eta) test x := by
  rw [sourceActualSpatialField_generated q sL eL sR eR c eta frequency positive]
  simp only [sourceCommonSpatialField_master q c eta frequency positive,smul_add,Finset.sum_add_distrib,
    sourceActualMasterSpatialDerivative,sourceActualMasterSpatialCorrection]

open Lean Elab Term in
elab "paidMasterUnit% " : term => do
  let wanted:=`LowEnergy.PreparationPhysicalJointRadialForcing.unit_field_coefficients
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRadialSpatialReturn." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceJointRadialSpatialReturn.unit_field_coefficients"

open PreparationPhysicalActualLegNormalization

private theorem unit_read_derivative (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (T : ℝ)
    (left : q.z.im≠0) (right : q.w.im≠0) (f : ℂ→Fin 289→ℂ) (f' : Fin 289→ℂ) (zeta : ℂ)
    (generated : HasDerivAt f f' zeta) :
    HasDerivAt (fun z : ℂ=>sourceActualUnitFieldRead q sL eL sR eR 0 T (f z))
      (sourceActualUnitFieldRead q sL eL sR eR 0 T f') zeta := by
  simp only [(paidMasterUnit%) q sL eL sR eR 0 T left right]
  exact HasDerivAt.fun_sum (fun i (_ : i∈Finset.univ)=>(hasDerivAt_pi.mp generated i).mul_const _)

private theorem unit_read_sub (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (T : ℝ)
    (left : q.z.im≠0) (right : q.w.im≠0) (V W : Fin 289→ℂ) :
    sourceActualUnitFieldRead q sL eL sR eR 0 T (V-W)=
      sourceActualUnitFieldRead q sL eL sR eR 0 T V-sourceActualUnitFieldRead q sL eL sR eR 0 T W := by
  simp only [(paidMasterUnit%) q sL eL sR eR 0 T left right,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]

/-- The same independently normalized actual detector reads the complete spatial response as the causal-master derivative plus its source corrections. -/
theorem sourceActualUnitMaster_derivative (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun z : ℂ=>sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualMasterSpatialField q sL eL sR eR z test x))
      (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T (sourceActualSpatialField q sL eL sR eR c eta test x)-
        sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
          (sourceActualMasterSpatialCorrection q sL eL sR eR (sourcePoleSide c eta) test x)) (sourcePoleSide c eta) := by
  have generated:=unit_read_derivative qd dSL dEL dSR dER T left right _ _ _
    (sourceActualMasterSpatial_derivative q sL eL sR eR c eta frequency positive test x)
  have field : sourceActualMasterSpatialDerivative q sL eL sR eR (sourcePoleSide c eta) test x=
      sourceActualSpatialField q sL eL sR eR c eta test x-
        sourceActualMasterSpatialCorrection q sL eL sR eR (sourcePoleSide c eta) test x := by
    rw [sourceActualSpatialField_master q sL eL sR eR c eta frequency positive test x]
    abel
  rwa [field,unit_read_sub qd dSL dEL dSR dER T left right] at generated

/-- The original actual radial potential is the same d-zeta consumer of this master; all source-unit leg factors and corrections remain in the read. -/
theorem sourceActualUnitMaster_radialDerivative (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (d : ℝ) (radial : 0<d) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun s : ℝ=>sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualMasterSpatialField q sL eL sR eR ((s:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) test x))
      (sourcePoleSide (sourceSignedSpeed branch negative) eta*
        (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)-
          sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
            (sourceActualMasterSpatialCorrection q sL eL sR eR ((d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) test x))) d := by
  have side : sourcePoleSide (d*sourceSignedSpeed branch negative) (d*eta)=
      (d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta := by
    simp only [sourcePoleSide,Complex.ofReal_mul]
    ring
  have generated:=sourceActualUnitMaster_derivative qd q dSL dEL dSR dER sL eL sR eR T
    (d*sourceSignedSpeed branch negative) (d*eta) (mul_ne_zero radial.ne' (sourceSignedSpeed_nonzero branch negative))
    (mul_pos radial positive) left right test x
  rw [side,←sourceActualRadialPotential_return q sL eL sR eR branch negative eta positive d radial test x] at generated
  have cast : HasDerivAt (fun s : ℝ=>(s:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta)
      (sourcePoleSide (sourceSignedSpeed branch negative) eta) d := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using
      ((Complex.ofRealCLM.hasFDerivAt (x:=d)).hasDerivAt.mul_const (sourcePoleSide (sourceSignedSpeed branch negative) eta))
  simpa only [Function.comp_def,smul_eq_mul] using generated.scomp d cast

/-- Original finite frame, second native field, regular/contact summand and complete residual stay in the same field return. -/
theorem sourceActualFrame_master_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (z : ℂ) :
    sourceChargedActualFrameField q n (sourcePoleSide c eta) l r z+
      z • (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n (sourcePoleSide c eta) l r)=
      (∑i : Fin 3,(sourceMasterChannelDerivative q n (sourcePoleSide c eta) l r i+
          sourceMasterChannelCorrection q n (sourcePoleSide c eta) l r i) • sourceCommonOriginColumn i)+
        z • sourceChargedSecondField q n (sourcePoleSide c eta) l r+
          sourceChargedActualFieldResidual q n (sourcePoleSide c eta) l r z := by
  rw [←sourceChargedActualField_first_return q n (sourcePoleSide c eta) l r z,
    sourceChargedSecondField,
    sourceCommonJoint_channels q n ⟨sourcePoleSide c eta,sourcePoleSide_field_domain n c eta frequency positive⟩ l r]
  simp only [←sourceCommonCausalChannel_master,sourceCommonCausalChannel,smul_add]
  abel

end LowEnergy.PreparationPhysicalRetainerResolventSquare
