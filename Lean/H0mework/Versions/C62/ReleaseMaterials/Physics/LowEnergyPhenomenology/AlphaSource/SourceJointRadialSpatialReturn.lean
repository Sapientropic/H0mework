import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRadialPrice

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
local instance JointRadialSpatialIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalActualLegNormalization

private theorem scaled_side (c eta d : ℝ) :
    sourcePoleSide (d*c) (d*eta)=(d:ℂ)*sourcePoleSide c eta := by
  simp only [sourcePoleSide,Complex.ofReal_mul]
  ring

private theorem spatial_positive (n : PhysicalMomentum) (nonzero : n≠0) : 0<spatialSquare n := by
  by_contra fail
  have bound : spatialSquare n≤0:=le_of_not_gt fail
  have a:=sq_nonneg (n 0)
  have b:=sq_nonneg (n 1)
  have c:=sq_nonneg (n 2)
  unfold spatialSquare at bound
  have h0 : n 0=0 := sq_eq_zero_iff.mp (by nlinarith)
  have h1 : n 1=0 := sq_eq_zero_iff.mp (by nlinarith)
  have h2 : n 2=0 := sq_eq_zero_iff.mp (by nlinarith)
  apply nonzero
  ext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

private theorem double_integrand_return (q : PhysicalResponsePoint) (c eta : ℝ)
    (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ))
    (x n : PhysicalMomentum) (nonzero : n≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*sourceCommonMomentIntegrand q (d*c) (d*eta) l r i 0 0 test x n)
      (𝓝[>] 0) (𝓝 (sourceSpatialPhase n x*test n*
        ((sourcePoleSide c eta)⁻¹^2*(sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
          sourceSlowRead (sourceStaticNative q (sourceSpatialMomentum n) l r) ⟨i.val,by omega⟩))) := by
  let zeta:=sourcePoleSide c eta
  have zp : 0<zeta.re:=by simpa only [zeta,sourcePoleSide,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero] using positive
  have momentumNonzero : sourceSpatialMomentum n≠0 := by
    unfold sourceSpatialMomentum
    exact smul_ne_zero (by positivity : (2*Real.pi:ℝ)≠0) nonzero
  have denominatorNZ : sourceChargedDenominator (sourceSpatialMomentum n) 0 i≠0 := by
    simp only [sourceChargedDenominator,zero_pow (by omega : 2≠0),mul_zero,add_zero]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sourceChargedSpatialCoefficient_positive i).ne')
      (Complex.ofReal_ne_zero.mpr (spatial_positive _ momentumNonzero).ne')
  have denominatorContinuous : Continuous (fun d : ℝ=>sourceChargedDenominator (sourceSpatialMomentum n) ((d:ℂ)*zeta) i) := by
    unfold sourceChargedDenominator
    fun_prop
  have inverse : Tendsto (fun d : ℝ=>(sourceChargedDenominator (sourceSpatialMomentum n) ((d:ℂ)*zeta) i)⁻¹)
      (𝓝[>] 0) (𝓝 ((sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹)) := by
    have generated:=(denominatorContinuous.continuousAt (x:=0)).tendsto
    simp only [Complex.ofReal_zero,zero_mul] at generated
    exact (generated.inv₀ denominatorNZ).mono_left nhdsWithin_le_nhds
  have slow:=sourceComplexRadialSlow_return q (sourceSpatialMomentum n) zeta zp l r i
  have generated:=(inverse.mul slow).const_mul (sourceSpatialPhase n x*test n)
  have endpoint : sourceSpatialPhase n x*test n*((sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      (zeta⁻¹^2*sourceSlowRead (sourceStaticNative q (sourceSpatialMomentum n) l r) ⟨i.val,by omega⟩))=
      sourceSpatialPhase n x*test n*(zeta⁻¹^2*(sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
        sourceSlowRead (sourceStaticNative q (sourceSpatialMomentum n) l r) ⟨i.val,by omega⟩) := by ring
  rw [endpoint] at generated
  apply generated.congr
  intro d
  simp only [sourceCommonMomentIntegrand,pow_zero,one_mul,sourceCommonCausalChannel,scaled_side]
  dsimp only [zeta]
  ring

/-- Literal three-channel double coefficient on the actual complex radial side. -/
def sourceJointSpatialDoubleChannel (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
    ((sourcePoleSide c eta)⁻¹^2*(sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      sourceSlowRead (sourceStaticNative q (sourceSpatialMomentum n) l r) ⟨i.val,by omega⟩)

/-- The whole Fourier integral, including the true three-dimensional small-momentum layer, consumes the generated common price. -/
theorem sourceJointSpatialDoubleChannel_return (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*sourceCommonSpatialMoment q (d*c) (d*eta) l r i 0 0 test x)
      (𝓝[>] 0) (𝓝 (sourceJointSpatialDoubleChannel q c eta l r i test x)) := by
  have aenonzero : ∀ᵐ n : PhysicalMomentum ∂volume,n≠0 := by rw [ae_iff];simp
  have small : ∀ᶠ d : ℝ in 𝓝[>] 0,d≤1 :=
    ((eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds)
  unfold sourceJointSpatialDoubleChannel
  have generated : Tendsto
      (fun d : ℝ=>∫n : PhysicalMomentum,(d:ℂ)^2*sourceCommonMomentIntegrand q (d*c) (d*eta) l r i 0 0 test x n)
      (𝓝[>] 0) (𝓝 (∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
        ((sourcePoleSide c eta)⁻¹^2*(sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
          sourceSlowRead (sourceStaticNative q (sourceSpatialMomentum n) l r) ⟨i.val,by omega⟩))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun n=>sourceJointRadialChannelPrice q c eta l r i*sourceRadialSchwartzPrice test n)
    · filter_upwards [self_mem_nhdsWithin] with d dp
      exact ((sourceCommonMoment_integrable q (d*c) (d*eta) (mul_ne_zero dp.ne' frequency)
        (mul_pos dp positive) l r i 0 0 test x).const_mul ((d:ℂ)^2)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin,small] with d dp ds
      filter_upwards [aenonzero] with n nz
      exact sourceJointRadialFourier_bound q c eta frequency positive d dp ds l r i test x n nz
    · exact (sourceRadialSchwartzPrice_integrable test).const_mul _
    · filter_upwards [aenonzero] with n nz
      exact double_integrand_return q c eta positive l r i test x n nz
  simpa only [integral_const_mul,sourceCommonSpatialMoment] using generated

def sourceJointSpatialDoubleField (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceJointSpatialDoubleChannel q c eta l r i test x • sourceCommonOriginColumn i

/-- The full289 source field, not an angular average, has the complete spatial double-layer return. -/
theorem sourceJointSpatialDoubleField_return (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • sourceCommonSpatialField q (d*c) (d*eta) l r test x)
      (𝓝[>] 0) (𝓝 (sourceJointSpatialDoubleField q c eta l r test x)) := by
  have generated:=tendsto_finsetSum Finset.univ (fun i _=>
    (sourceJointSpatialDoubleChannel_return q c eta frequency positive l r i test x).smul_const (sourceCommonOriginColumn i))
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with d dp
  rw [sourceCommonSpatialField_generated q (d*c) (d*eta) (mul_ne_zero dp.ne' frequency) (mul_pos dp positive),Finset.smul_sum]
  simp only [smul_smul]

def sourceActualJointSpatialDouble (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceJointSpatialDoubleField q c eta l r test x

/-- Every actual source overlap survives the whole-space limit at the same d-zeta. -/
theorem sourceActualJointSpatialDouble_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (positive : 0<eta)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>((d:ℂ)^2) • sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)
      (𝓝[>] 0) (𝓝 (sourceActualJointSpatialDouble q sL eL sR eR (sourceSignedSpeed branch negative) eta test x)) := by
  have generated:=tendsto_finsetSum Finset.univ (fun l _=>tendsto_finsetSum Finset.univ (fun r _=>
    (sourceJointSpatialDoubleField_return q (sourceSignedSpeed branch negative) eta
      (sourceSignedSpeed_nonzero branch negative) positive l r test x).const_smul
        (sourceActualPreparedWeight 0 0 sL eL sR eR l r)))
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with d dp
  rw [sourceActualRadialPotential_return q sL eL sR eR branch negative eta positive d dp test x,
    sourceActualSpatialField_generated q sL eL sR eR _ _
      (mul_ne_zero dp.ne' (sourceSignedSpeed_nonzero branch negative)) (mul_pos dp positive)]
  simp only [Finset.smul_sum,smul_comm ((d:ℂ)^2)]

/-- The independent actual detector64 reads the source-generated whole-space double coefficient. -/
theorem sourceActualJointSpatialDouble_observed (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)) (𝓝[>] 0)
      (𝓝 (sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
        (sourceActualJointSpatialDouble q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  have generated:=(sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T).continuous.continuousAt.tendsto.comp
    (sourceActualJointSpatialDouble_return q sL eL sR eR branch negative eta positive test x)
  simpa only [Function.comp_def,map_smul,smul_eq_mul] using generated

private theorem unit_field_coefficients (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) (V : Fin 289→ℂ) :
    sourceActualUnitFieldRead q sL eL sR eR lambda T V=
      ∑i : Fin 289,V i*(-sourceActualUnitLegRead q sL eL sR eR
        (∫t in (0:ℝ)..T,laplaceWeight lambda t • actualJointKernel q 0 0 t i)) := by
  have argument : Continuous (fun t : ℝ=>(0,0,t) : ℝ→PhysicalMomentum×PhysicalMomentum×ℝ) := by fun_prop
  have continuous (i : Fin 289) : Continuous (fun t : ℝ=>laplaceWeight lambda t • actualJointKernel q 0 0 t i) := by
    have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
    have kernel:=(actualJointKernel_continuous q i left right).comp argument
    exact (weight.smul kernel).congr (fun _=>rfl)
  have point (t : ℝ) : laplaceWeight lambda t • (∑i : Fin 289,V i • actualJointKernel q 0 0 t i)=
      ∑i : Fin 289,V i • (laplaceWeight lambda t • actualJointKernel q 0 0 t i) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  have kernel : sourceActualPreparedKernel q 0 0 lambda T V=
      ∑i : Fin 289,V i • (∫t in (0:ℝ)..T,laplaceWeight lambda t • actualJointKernel q 0 0 t i) := by
    unfold sourceActualPreparedKernel
    simp_rw [point]
    have integrable (i : Fin 289) : IntervalIntegrable
        (fun t : ℝ=>V i • (laplaceWeight lambda t • actualJointKernel q 0 0 t i)) volume 0 T := by
      have scalarContinuous : Continuous (fun t : ℝ=>V i • (laplaceWeight lambda t • actualJointKernel q 0 0 t i)) :=
        ((continuous i).const_smul (V i)).congr (fun _=>rfl)
      exact scalarContinuous.intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum (fun i _=>integrable i)]
    simp only [intervalIntegral.integral_smul]
  rw [sourceActualUnitFieldRead,kernel]
  simp only [sourceActualUnitLegRead,sum_apply,smul_apply,map_sum,map_smul,Finset.sum_neg_distrib,smul_eq_mul,mul_neg]

private theorem unit_field_continuous (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) :
    Continuous (sourceActualUnitFieldRead q sL eL sR eR lambda T) := by
  have entry (i : Fin 289) : Continuous (fun V : Fin 289→ℂ=>V i*
      (-sourceActualUnitLegRead q sL eL sR eR
        (∫t in (0:ℝ)..T,laplaceWeight lambda t • actualJointKernel q 0 0 t i))) :=
    (continuous_apply i).mul_const _
  have generated:=continuous_finsetSum Finset.univ (fun i _=>entry i)
  exact generated.congr (fun V=>(unit_field_coefficients q sL eL sR eR lambda T left right V).symm)

private theorem unit_field_smul (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) (z : ℂ) (V : Fin 289→ℂ) :
    sourceActualUnitFieldRead q sL eL sR eR lambda T (z • V)=
      z*sourceActualUnitFieldRead q sL eL sR eR lambda T V := by
  rw [unit_field_coefficients q sL eL sR eR lambda T left right,
    unit_field_coefficients q sL eL sR eR lambda T left right]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

/-- The original source-normalized external legs consume the whole Fourier double return with every norm and left/right/cross defect retained. -/
theorem sourceActualUnitJointSpatialDouble_return (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)) (𝓝[>] 0)
      (𝓝 (sourceActualLegNormalization qd dSL dEL dSR dER*
        (sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
          (sourceActualJointSpatialDouble q sL eL sR eR (sourceSignedSpeed branch negative) eta test x)-
          sourceActualLegCorrection qd dSL dEL dSR dER
            (sourceActualPreparedKernel qd 0 0 0 T
              (sourceActualJointSpatialDouble q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))))) := by
  have generated:=(unit_field_continuous qd dSL dEL dSR dER 0 T left right).continuousAt.tendsto.comp
    (sourceActualJointSpatialDouble_return q sL eL sR eR branch negative eta positive test x)
  rw [sourceActualUnitField_return qd dSL dEL dSR dER 0 T _ left right] at generated
  simpa only [Function.comp_def,unit_field_smul qd dSL dEL dSR dER 0 T left right] using generated

end LowEnergy.PreparationPhysicalJointRadialForcing
