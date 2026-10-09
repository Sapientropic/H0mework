import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCausalSpatialEuler

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalMasterCorrectionReturn
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
local instance MasterCorrectionIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
attribute [local irreducible] sourceEqualProjection sourceRetainerReturn sourceFullInitialUpper sourceFullInitialBase
  sourcePinnedResolvent sourceResonanceProjection sourcePoleRead sourceRetainerSeed sourceStaticCurrent
  sourceMasterCurrent sourceOriginCurrentResidue sourceNativeReaderFirst

private theorem resonance_module (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (X : SourceOp) :
    sourceEqualProjection F (sourceResonanceProjection F n 0*X)=
      sourceResonanceProjection F n 0*sourceEqualProjection F X := by
  have paid:=sourceEqualProjection_left_module F (sourceResonanceProjection F n 0) X
  simpa only [sourceResonanceProjection_equal] using paid

/-- The original static retainer is computed from the same complete full289 seed and original right multiplier. -/
theorem sourceStaticBase_seed (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) :
    sourceStaticBase q n i=(-Complex.I) • (sourceResonanceProjection q.F n 0*sourceRetainerSeed q i) := by
  simp only [sourceStaticBase,sourceRetainerReturn_apply,map_smul]
  rw [mul_assoc (sourceResonanceProjection q.F n 0),resonance_module]
  simp only [mul_smul_comm,←mul_assoc,sourceResonanceProjection_square,sourceRetainerSeed]
  apply ContinuousLinearMap.ext
  intro x
  simp only [neg_apply,smul_apply]
  exact (neg_smul Complex.I _).symm

theorem sourceStaticCurrent_seed (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (i : Fin 289) :
    sourceStaticCurrent q n l r i=Complex.I*sourcePoleRead q.epsilon q.precision 0 0 l r
      (sourceResonanceProjection q.F n 0*sourceRetainerSeed q i) := by
  rw [sourceStaticCurrent,sourceStaticBase_seed,map_smul]
  simp only [smul_eq_mul,neg_mul,neg_neg]

/-- The first-order master returns the negative of the actual static full current on the same complex radial side. -/
theorem sourceMasterCurrent_simple (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (l r : RestStateIndex) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceMasterCurrent q n ((d:ℂ)*zeta) l r)
      (𝓝[>] 0) (𝓝 (-(zeta⁻¹ • sourceStaticCurrent q n l r))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have inverse:=(sourceComplexRadialPinned_return q.F n zeta causal).mul_const (sourceRetainerSeed q i)
  have generated:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.continuousAt.tendsto.comp inverse).const_mul (-Complex.I)
  convert! generated using 1
  · funext d
    simp only [sourceMasterCurrent,Pi.smul_apply,smul_mul_assoc,map_smul,smul_eq_mul,Function.comp_def]
    ring
  · congr 1
    simp only [Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
    rw [sourceStaticCurrent_seed]
    simp only [smul_mul_assoc,map_smul,smul_eq_mul]
    ring

/-- Both actual gauge coordinates return their own original static coefficient, without a real-eta substitution. -/
theorem sourceGaugeCurrent_simple (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceGaugeCurrentResidue q n ((d:ℂ)*zeta) l r mu a)
      (𝓝[>] 0) (𝓝 (zeta⁻¹*sourceStaticGaugeCurrent q n l r mu a)) := by
  have inverse:=(sourceComplexRadialPinned_return q.F n zeta causal).mul_const
    (sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (gaugeSlot mu a)))
  have generated:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.continuousAt.tendsto.comp inverse).neg
  simpa only [sourceGaugeCurrentResidue,sourceGaugeResidue,(paidSpatial% projected_origin),sourceStaticGaugeCurrent,
    sourceStaticGauge,smul_mul_assoc,map_smul,smul_eq_mul,mul_neg,Function.comp_def] using generated

private theorem originPair_continuous : Continuous sourceOriginPair := by
  apply continuous_pi
  intro i
  simp only [sourceOriginPair,Pi.add_apply,Pi.single_apply]
  split_ifs <;> fun_prop

private theorem originPair_scale (z w : ℂ) : z • sourceOriginPair w=sourceOriginPair (z*w) := by
  funext i
  simp only [sourceOriginPair,Pi.add_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  split_ifs <;> ring

theorem sourceOriginCurrent_simple (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (l r : RestStateIndex) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceOriginCurrentResidue q n ((d:ℂ)*zeta) l r)
      (𝓝[>] 0) (𝓝 (zeta⁻¹ • sourceOriginPair ((3/10:ℂ)*rootTwo*
        (sourceStaticGaugeCurrent q n l r 1 0-sourceStaticGaugeCurrent q n l r 2 1)))) := by
  have first:=sourceGaugeCurrent_simple q n zeta causal l r 1 0
  have second:=sourceGaugeCurrent_simple q n zeta causal l r 2 1
  have scalar:=(first.sub second).const_mul ((3/10:ℂ)*rootTwo)
  have generated:=originPair_continuous.continuousAt.tendsto.comp scalar
  convert! generated using 1
  · funext d
    simp only [sourceOriginCurrentResidue,originPair_scale,Function.comp_def]
    congr 1
    ring
  · rw [originPair_scale]
    congr 1
    ring

/-- This is the complete gauge and reader-time numerator already present in the original master correction. -/
def sourceMasterSimpleNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceOriginCurrentResidue q n zeta l r-
    sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥsourceMasterCurrent q n zeta l r

/-- Its complete source-generated complex radial return is exactly the existing native simple coefficient. -/
theorem sourceMasterSimpleNumerator_return (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (l r : RestStateIndex) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceMasterSimpleNumerator q n ((d:ℂ)*zeta) l r)
      (𝓝[>] 0) (𝓝 (zeta⁻¹ • sourceNativeSimple q n l r)) := by
  have reader : Continuous (fun v : Fin 289→ℂ=>sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥv):=
    continuous_const.matrix_mulVec continuous_id
  have generated:=(sourceOriginCurrent_simple q n zeta causal l r).sub
    (reader.continuousAt.tendsto.comp (sourceMasterCurrent_simple q n zeta causal l r))
  simpa only [sourceMasterSimpleNumerator,smul_sub,Matrix.mulVec_smul,Matrix.mulVec_neg,sub_neg_eq_add,
    ←smul_add,sourceNativeSimple_gauge_time,Function.comp_def] using generated

open Lean Elab Term in
elab "paidCorrectionMaster% " id:ident : term => do
  let member:=id.getId
  unless member==`master_current_bound || member==`master_current_continuous do
    throwError "Only the actual original master current price or continuity payer is accepted"
  let wanted:=`LowEnergy.PreparationPhysicalRetainerResolventSquare ++ member
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCausalMasterDerivative." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceCausalMasterDerivative payer {wanted}"

private theorem scaled_positive (d : ℝ) (radial : 0<d) (zeta : ℂ) (causal : 0<zeta.re) :
    0<((d:ℂ)*zeta).re := by
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos radial causal

/-- Original source resolvent prices control the whole normalized master current uniformly in all momentum. -/
theorem sourceMasterCurrent_simple_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (d : ℝ) (radial : 0<d) (l r : RestStateIndex) :
    ‖(d:ℂ) • sourceMasterCurrent q n ((d:ℂ)*zeta) l r‖≤ sourceMasterCurrentPrice q l r/zeta.re := by
  have paid:=(paidCorrectionMaster% master_current_bound) q n ((d:ℂ)*zeta) (scaled_positive d radial zeta causal) l r
  have real : ((d:ℂ)*zeta).re=d*zeta.re := by simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [real] at paid
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos radial]
  exact (mul_le_mul_of_nonneg_left paid radial.le).trans_eq (by field_simp)

theorem sourceOriginCurrent_simple_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (d : ℝ) (radial : 0<d) (l r : RestStateIndex) :
    ‖(d:ℂ) • sourceOriginCurrentResidue q n ((d:ℂ)*zeta) l r‖≤ sourceSpatialGaugePrice q zeta.re l r := by
  have paid:=(paidSpatial% origin_bound) q n ((d:ℂ)*zeta) (scaled_positive d radial zeta causal) l r
  have real : ((d:ℂ)*zeta).re=d*zeta.re := by simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have scale : sourceSpatialGaugePrice q (d*zeta.re) l r=d⁻¹*sourceSpatialGaugePrice q zeta.re l r := by
    simp only [sourceSpatialGaugePrice,div_eq_mul_inv,mul_inv_rev,one_mul]
    ring
  rw [real,scale] at paid
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos radial]
  exact (mul_le_mul_of_nonneg_left paid radial.le).trans_eq (by rw [←mul_assoc,mul_inv_cancel₀ radial.ne',one_mul])

def sourceMasterSimplePrice (q : PhysicalResponsePoint) (eta : ℝ) (l r : RestStateIndex) : ℝ :=
  sourceSpatialGaugePrice q eta l r+
    ‖sourceNativeReaderFirst (fixedMomentum 0 1)‖*(sourceMasterCurrentPrice q l r/eta)

theorem sourceMasterSimpleNumerator_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (d : ℝ) (radial : 0<d) (l r : RestStateIndex) :
    ‖(d:ℂ) • sourceMasterSimpleNumerator q n ((d:ℂ)*zeta) l r‖≤ sourceMasterSimplePrice q zeta.re l r := by
  rw [sourceMasterSimpleNumerator,smul_sub,←Matrix.mulVec_smul]
  apply (norm_sub_le _ _).trans
  apply add_le_add (sourceOriginCurrent_simple_bound q n zeta causal d radial l r)
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_left (sourceMasterCurrent_simple_bound q n zeta causal d radial l r) (norm_nonneg _))

/-- The original correction retains its complete numerator and the derivative of every original field denominator. -/
theorem sourceMasterCorrection_split (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) :
    sourceMasterChannelCorrection q n zeta l r i=
      (sourceChargedDenominator n zeta i)⁻¹*sourceSlowRead (sourceMasterSimpleNumerator q n zeta l r) ⟨i.val,by omega⟩+
      (2*(sourceChargedTemporalCoefficient i:ℂ)*zeta)*((sourceChargedDenominator n zeta i)⁻¹)^2*
        sourceSlowRead (sourceMasterNative q n zeta l r) ⟨i.val,by omega⟩ := by
  simp only [sourceMasterChannelCorrection,sourceMasterSimpleNumerator,sourceSlowRead,
    show i.val<3 from i.isLt,ite_true,Matrix.mulVec_sub,Pi.sub_apply,mul_sub]

end LowEnergy.PreparationPhysicalMasterCorrectionReturn
