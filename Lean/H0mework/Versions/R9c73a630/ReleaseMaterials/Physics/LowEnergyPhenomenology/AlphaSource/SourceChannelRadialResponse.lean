import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelRadialSlope
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualNormalizedVertex

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChannelRadialJet
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
local instance ChannelRadialResponseIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalActualLegNormalization PreparationVacuumObservedStaticResidue

private abbrev sourceKernel : ℂ→ℝ→PhysicalMomentum→ℂ:=paidRadialGreen% greenKernel

def sourceChannelRadialJet (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3) : ℂ :=
  -sourceChannelMass branch negative eta i/(4*(Real.pi:ℂ)*(sourceChargedSpatialCoefficient i:ℂ))

def sourceChannelRadialRemainder (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3)
    (d : ℝ) (x : PhysicalMomentum) : ℂ :=
  sourceChannelFundamentalKernel branch negative eta i d x-sourceChannelFundamentalKernel branch negative eta i 0 x-
    (d:ℂ)*sourceChannelRadialJet branch negative eta i

/-- The remainder comes from the same actual kernel, with its first-order price generated by the Gaussian layer. -/
theorem sourceChannelRadialRemainder_limit (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (x : PhysicalMomentum) (spatial : 0<spatialSquare x) :
    Tendsto (fun d : ℝ=>(d:ℂ)⁻¹*sourceChannelRadialRemainder branch negative eta i d x)
      (𝓝[>] 0) (𝓝 0) := by
  have generated:=(sourceChannelFundamentalKernel_slope branch negative eta positive i x spatial).sub_const
    (sourceChannelRadialJet branch negative eta i)
  change Tendsto _ _ (𝓝 (sourceChannelRadialJet branch negative eta i-sourceChannelRadialJet branch negative eta i)) at generated
  rw [sub_self] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with d dp
  unfold sourceChannelRadialRemainder
  field_simp [Complex.ofReal_ne_zero.mpr dp.ne']

theorem sourceChannelRadialKernel_zero (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (x : PhysicalMomentum) (spatial : 0<spatialSquare x) :
    sourceChannelFundamentalKernel branch negative eta i 0 x=
      (4*(Real.pi:ℂ)*(sourceChargedSpatialCoefficient i:ℂ)*(Real.sqrt (spatialSquare x):ℂ))⁻¹ := by
  unfold sourceChannelFundamentalKernel
  rw [(paidRadialGreen% greenKernel_zero) _ (sourceChannelMass_positive branch negative eta positive i) x spatial]
  simp only [mul_inv_rev]
  ring

private theorem scaled_side (c eta d : ℝ) :
    sourcePoleSide (d*c) (d*eta)=(d:ℂ)*sourcePoleSide c eta := by
  simp only [sourcePoleSide,Complex.ofReal_mul]
  ring

private theorem radial_denominator (branch : Fin 2) (negative : Bool) (eta d : ℝ)
    (n : PhysicalMomentum) (i : Fin 3) :
    sourceChargedDenominator n (sourcePoleSide (d*sourceSignedSpeed branch negative) (d*eta)) i=
      (sourceChargedSpatialCoefficient i:ℂ)*((spatialSquare n:ℂ)+(d:ℂ)^2*(sourceChannelMass branch negative eta i)^2) := by
  rw [scaled_side,sourceChargedDenominator,sourceChannelMass,mul_pow,mul_pow]
  have factor:=sourceChannelMassFactor_square negative i
  linear_combination -(d:ℂ)^2*(sourcePoleSide (sourceSignedSpeed branch negative) eta)^2*factor

/-- The source frequency and damping scale together with the same kernel mass. -/
def sourceChannelRadialPotential (branch : Fin 2) (negative : Bool) (eta d : ℝ)
    (q : PhysicalResponsePoint) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫y : PhysicalMomentum,sourceChannelFundamentalKernel branch negative eta i d y*
    sourceCommonSpatialForcing q (d*sourceSignedSpeed branch negative) (d*eta) l r i test (x-y)

/-- The actual d-dependent native source has the original price at the same d-zeta, so the whole convolution returns the original field coefficient. -/
theorem sourceChannelRadialPotential_return (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (d : ℝ) (radial : 0<d) (q : PhysicalResponsePoint)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceChannelRadialPotential branch negative eta d q l r i test x=
      sourceCommonSpatialMoment q (d*sourceSignedSpeed branch negative) (d*eta) l r i 0 0 test x := by
  let c:=d*sourceSignedSpeed branch negative
  let kappa:=sourceChannelMass branch negative eta i
  let forcing : PhysicalMomentum→ℂ:=fun frequency=>test frequency*
    sourceSlowRead (sourceActualNativeResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c (d*eta)) l r) ⟨i.val,by omega⟩
  have input : Integrable forcing := by
    have paid:=sourceCommonSpatialForcing_integrable q c (d*eta)
      (mul_ne_zero radial.ne' (sourceSignedSpeed_nonzero branch negative)) (mul_pos radial positive) l r i test 0
    simpa only [sourceSpatialPhase,Pi.zero_apply,mul_zero,Finset.sum_const_zero,Complex.ofReal_zero,Complex.exp_zero,one_mul] using paid
  have generated:=(paidRadialGreen% kernel_convolution) kappa
    (sourceChannelMass_positive branch negative eta positive i) d radial forcing input x
  unfold sourceChannelRadialPotential sourceChannelFundamentalKernel sourceCommonSpatialForcing
  have point (y : PhysicalMomentum) : (sourceChargedSpatialCoefficient i:ℂ)⁻¹*sourceKernel kappa d y*
      (∫frequency : PhysicalMomentum,sourceSpatialPhase frequency (x-y)*test frequency*
        sourceSlowRead (sourceActualNativeResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c (d*eta)) l r) ⟨i.val,by omega⟩)=
      (sourceChargedSpatialCoefficient i:ℂ)⁻¹*(sourceKernel kappa d y*
        (∫frequency : PhysicalMomentum,sourceSpatialPhase frequency (x-y)*forcing frequency)) := by
    simp only [forcing,mul_assoc]
  conv_lhs =>
    arg 2
    ext y
    rw [point y]
  rw [integral_const_mul,generated,←integral_const_mul]
  unfold sourceCommonSpatialMoment sourceCommonMomentIntegrand
  apply integral_congr_ae
  filter_upwards with frequency
  simp only [pow_zero,one_mul,sourceCommonCausalChannel,forcing]
  rw [radial_denominator branch negative eta d (sourceSpatialMomentum frequency) i,mul_inv_rev]
  dsimp only [kappa,c]
  ring

/-- Full289 residual on the actual complex radial side; no real-axis limit has been substituted. -/
def sourceNativeRadialRemainder (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (d : ℝ) (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceActualNativeResidue q n ((d:ℂ)*zeta) l r-
    (((d:ℂ)*zeta)⁻¹)^2 • sourceStaticNative q n l r-
    ((d:ℂ)*zeta)⁻¹ • sourceNativeSimple q n l r

private theorem native_radial_read (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (d : ℝ) (l r : RestStateIndex) (i : Fin 3) :
    sourceSlowRead (sourceActualNativeResidue q n ((d:ℂ)*zeta) l r) ⟨i.val,by omega⟩=
      (((d:ℂ)*zeta)⁻¹)^2*sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩+
      ((d:ℂ)*zeta)⁻¹*sourceSlowRead (sourceNativeSimple q n l r) ⟨i.val,by omega⟩+
      sourceSlowRead (sourceNativeRadialRemainder q n zeta d l r) ⟨i.val,by omega⟩ := by
  simp only [sourceNativeRadialRemainder,sourceSlowRead,show i.val<3 from i.isLt,ite_true,
    Matrix.mulVec_sub,Matrix.mulVec_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Every kernel/current cross remains inside one integrable source expression. Individual lower-layer integrals and their limits are not assumed. -/
theorem sourceChannelRadialPotential_expanded (branch : Fin 2) (negative : Bool) (eta d : ℝ)
    (q : PhysicalResponsePoint) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceChannelRadialPotential branch negative eta d q l r i test x=
      ∫y : PhysicalMomentum,
        (sourceChannelFundamentalKernel branch negative eta i 0 y+
          (d:ℂ)*sourceChannelRadialJet branch negative eta i+sourceChannelRadialRemainder branch negative eta i d y)*
        (∫frequency : PhysicalMomentum,sourceSpatialPhase frequency (x-y)*test frequency*
          ((((d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta)⁻¹)^2*
              sourceSlowRead (sourceStaticNative q (sourceSpatialMomentum frequency) l r) ⟨i.val,by omega⟩+
            ((d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta)⁻¹*
              sourceSlowRead (sourceNativeSimple q (sourceSpatialMomentum frequency) l r) ⟨i.val,by omega⟩+
            sourceSlowRead (sourceNativeRadialRemainder q (sourceSpatialMomentum frequency)
              (sourcePoleSide (sourceSignedSpeed branch negative) eta) d l r) ⟨i.val,by omega⟩)) := by
  unfold sourceChannelRadialPotential sourceCommonSpatialForcing
  apply integral_congr_ae
  filter_upwards with y
  have kernelIdentity : sourceChannelFundamentalKernel branch negative eta i d y=
      sourceChannelFundamentalKernel branch negative eta i 0 y+(d:ℂ)*sourceChannelRadialJet branch negative eta i+
        sourceChannelRadialRemainder branch negative eta i d y := by unfold sourceChannelRadialRemainder;ring
  rw [kernelIdentity]
  congr 1
  apply integral_congr_ae
  filter_upwards with frequency
  rw [scaled_side,native_radial_read]

/-- All source64 weights and full289 channel columns are retained at the same physical radial side. -/
def sourceActualRadialPotential (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta d : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    (∑i : Fin 3,sourceChannelRadialPotential branch negative eta d q l r i test x • sourceCommonOriginColumn i)

theorem sourceActualRadialPotential_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (positive : 0<eta) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualRadialPotential q sL eL sR eR branch negative eta d test x=
      sourceActualSpatialField q sL eL sR eR (d*sourceSignedSpeed branch negative) (d*eta) test x := by
  have nonzero:=mul_ne_zero radial.ne' (sourceSignedSpeed_nonzero branch negative)
  have damping:=mul_pos radial positive
  rw [sourceActualSpatialField_generated q sL eL sR eR _ _ nonzero damping test x]
  simp only [sourceActualRadialPotential,sourceChannelRadialPotential_return branch negative eta positive d radial,
    sourceCommonSpatialField_generated q _ _ nonzero damping]

/-- The independent actual detector64 consumes the same expanded spatial response. -/
theorem sourceActualRadialPotential_observed (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (d : ℝ) (radial : 0<d)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)=
      sourceActualSpatialAmplitude q sL eL sR eR (d*sourceSignedSpeed branch negative) (d*eta) test x*
        sourceActualPreparedGaussWeight qd dSL dEL dSR dER T := by
  rw [sourceActualRadialPotential_return q sL eL sR eR branch negative eta positive d radial test x]
  exact sourceActualSpatialDetector_generated qd q dSL dEL dSR dER sL eL sR eR T _ _
    (mul_ne_zero radial.ne' (sourceSignedSpeed_nonzero branch negative)) (mul_pos radial positive) left right test x

/-- Actual unit external legs act on the whole same-field potential; their source norm and three correction terms stay outside any unproved limit. -/
theorem sourceActualUnitRadialPotential_return (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (d : ℝ) (radial : 0<d)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)=
      sourceActualLegNormalization qd dSL dEL dSR dER*
        (sourceActualSpatialAmplitude q sL eL sR eR (d*sourceSignedSpeed branch negative) (d*eta) test x*
          sourceActualPreparedGaussWeight qd dSL dEL dSR dER T-
          sourceActualLegCorrection qd dSL dEL dSR dER
            (sourceActualPreparedKernel qd 0 0 0 T (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))) := by
  rw [sourceActualRadialPotential_return q sL eL sR eR branch negative eta positive d radial test x]
  exact sourceActualUnitSpatial_return qd q dSL dEL dSR dER sL eL sR eR T _ _
    (mul_ne_zero radial.ne' (sourceSignedSpeed_nonzero branch negative)) (mul_pos radial positive) left right test x

end LowEnergy.PreparationPhysicalChannelRadialJet
