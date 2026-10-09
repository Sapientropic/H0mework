import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceComplexRadialNative
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

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
local instance JointRadialPriceIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open Metric

private theorem scaled_side (c eta d : ℝ) :
    sourcePoleSide (d*c) (d*eta)=(d:ℂ)*sourcePoleSide c eta := by
  simp only [sourcePoleSide,Complex.ofReal_mul]
  ring

private theorem denominator_price_scaled (c eta d : ℝ) (i : Fin 3) :
    sourceChargedDenominatorPrice (d*c) (d*eta) i=d⁻¹^2*sourceChargedDenominatorPrice c eta i := by
  unfold sourceChargedDenominatorPrice
  rw [show 2*sourceChargedTemporalCoefficient i*(d*eta)*(d*c)=d^2*(2*sourceChargedTemporalCoefficient i*eta*c) by ring,
    abs_mul,abs_of_nonneg (sq_nonneg d),mul_inv_rev,inv_pow]
  ring

/-- The old three-channel quadratic price is unchanged by the actual joint frequency/damping scale. -/
theorem sourceJointRadialQuadraticPrice (c eta d : ℝ) (radial : 0<d) (i : Fin 3) :
    sourceChargedQuadraticPrice (d*c) (d*eta) i=sourceChargedQuadraticPrice c eta i := by
  unfold sourceChargedQuadraticPrice
  rw [scaled_side,denominator_price_scaled]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos radial,mul_pow]
  field_simp [radial.ne']

/-- The moving channel0 pole is retained inside the same source bound; no extra excluded region is introduced. -/
theorem sourceJointRadialInverse_bound (n : PhysicalMomentum) (c eta : ℝ) (frequency : c≠0)
    (positive : 0<eta) (d : ℝ) (radial : 0<d) (i : Fin 3) :
    ‖n‖^2*‖(sourceChargedDenominator n (sourcePoleSide (d*c) (d*eta)) i)⁻¹‖≤
      sourceChargedQuadraticPrice c eta i := by
  have paid:=sourceChargedQuadratic_bound n (d*c) (d*eta) (mul_ne_zero radial.ne' frequency) (mul_pos radial positive) i
  rw [sourceJointRadialQuadraticPrice c eta d radial] at paid
  apply le_trans _ paid
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [norm_nonneg (sourcePoleSide (d*c) (d*eta)),norm_nonneg n]

def sourceJointRadialChannelPrice (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (i : Fin 3) : ℝ :=
  sourceChargedQuadraticPrice c eta i*‖slowFastFrame.transpose‖*
    (sourceSpatialGaugePrice q eta l r+
      ‖sourceReaderLinear‖*(‖sourcePoleSide c eta‖+1)*sourceSpatialCurrentPrice q eta l r)

private theorem channel_price_nonneg (q : PhysicalResponsePoint) (c eta : ℝ) (positive : 0<eta)
    (l r : RestStateIndex) (i : Fin 3) : 0≤ sourceJointRadialChannelPrice q c eta l r i := by
  unfold sourceJointRadialChannelPrice sourceChargedQuadraticPrice sourceChargedDenominatorPrice
    sourceSpatialGaugePrice sourceSpatialCurrentPrice
  have coefficient:=(sourceChargedSpatialCoefficient_positive i).le
  positivity

/-- The complete native forcing and field inverse have one momentum price after double normalization. -/
theorem sourceJointRadialChannel_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (nonzero : n≠0)
    (c eta : ℝ) (frequency : c≠0) (positive : 0<eta) (d : ℝ) (radial : 0<d) (small : d≤1)
    (l r : RestStateIndex) (i : Fin 3) :
    ‖(d:ℂ)^2*sourceCommonCausalChannel q n (sourcePoleSide (d*c) (d*eta)) l r i‖≤
      sourceJointRadialChannelPrice q c eta l r i*(1+‖n‖)*(‖n‖^2)⁻¹ := by
  let zeta:=sourcePoleSide c eta
  have zp : 0<zeta.re := by simpa only [zeta,sourcePoleSide,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero] using positive
  have real : zeta.re=eta := by simp [zeta,sourcePoleSide]
  have native:=sourceComplexRadialNative_bound q n zeta zp d radial l r
  rw [real] at native
  have slow:=(paidSpatial% slow_bound) (((d:ℂ)^2) • sourceActualNativeResidue q n ((d:ℂ)*zeta) l r) ⟨i.val,by omega⟩
  simp only [sourceSlowRead,show i.val<3 from i.isLt,ite_true,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] at slow
  have slowBound : ‖(d:ℂ)^2*sourceSlowRead (sourceActualNativeResidue q n ((d:ℂ)*zeta) l r) ⟨i.val,by omega⟩‖≤
      ‖slowFastFrame.transpose‖*(d*sourceSpatialGaugePrice q eta l r+
        ‖sourceReaderLinear‖*(d*‖zeta‖+‖n‖)*sourceSpatialCurrentPrice q eta l r) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left native (norm_nonneg _))
    simpa only [sourceSlowRead,show i.val<3 from i.isLt,ite_true] using slow
  have gaugeNonneg : 0≤ sourceSpatialGaugePrice q eta l r := by unfold sourceSpatialGaugePrice;positivity
  have currentNonneg : 0≤ sourceSpatialCurrentPrice q eta l r := by unfold sourceSpatialCurrentPrice;positivity
  have nativePrice : d*sourceSpatialGaugePrice q eta l r+
      ‖sourceReaderLinear‖*(d*‖zeta‖+‖n‖)*sourceSpatialCurrentPrice q eta l r≤
      (sourceSpatialGaugePrice q eta l r+‖sourceReaderLinear‖*(‖zeta‖+1)*sourceSpatialCurrentPrice q eta l r)*(1+‖n‖) := by
    have npos:=norm_nonneg n
    have zpos:=norm_nonneg zeta
    calc
      _≤ sourceSpatialGaugePrice q eta l r+
          ‖sourceReaderLinear‖*(‖zeta‖+‖n‖)*sourceSpatialCurrentPrice q eta l r := by gcongr <;> nlinarith
      _≤ sourceSpatialGaugePrice q eta l r*(1+‖n‖)+
          ‖sourceReaderLinear‖*((‖zeta‖+1)*(1+‖n‖))*sourceSpatialCurrentPrice q eta l r := by
        apply add_le_add
        · nlinarith [mul_nonneg gaugeNonneg npos]
        · gcongr
          nlinarith [mul_nonneg zpos npos]
      _=_:=by ring
  have inverse:=sourceJointRadialInverse_bound n c eta frequency positive d radial i
  have normPositive : 0<‖n‖:=norm_pos_iff.mpr nonzero
  have inverseBound : ‖(sourceChargedDenominator n (sourcePoleSide (d*c) (d*eta)) i)⁻¹‖≤
      sourceChargedQuadraticPrice c eta i/(‖n‖^2) := by
    apply (le_div_iff₀ (sq_pos_of_pos normPositive)).mpr
    simpa only [mul_comm] using inverse
  have quadraticNonneg : 0≤ sourceChargedQuadraticPrice c eta i := by
    unfold sourceChargedQuadraticPrice sourceChargedDenominatorPrice
    have coefficient:=(sourceChargedSpatialCoefficient_positive i).le
    positivity
  have expression : (d:ℂ)^2*sourceCommonCausalChannel q n (sourcePoleSide (d*c) (d*eta)) l r i=
      (sourceChargedDenominator n (sourcePoleSide (d*c) (d*eta)) i)⁻¹*
        ((d:ℂ)^2*sourceSlowRead (sourceActualNativeResidue q n ((d:ℂ)*zeta) l r) ⟨i.val,by omega⟩) := by
    unfold sourceCommonCausalChannel
    rw [scaled_side]
    ring
  rw [expression,norm_mul]
  calc
    _≤(sourceChargedQuadraticPrice c eta i/(‖n‖^2))*(‖slowFastFrame.transpose‖*
        ((sourceSpatialGaugePrice q eta l r+‖sourceReaderLinear‖*(‖zeta‖+1)*sourceSpatialCurrentPrice q eta l r)*(1+‖n‖))) := by
      apply mul_le_mul inverseBound
        (slowBound.trans (mul_le_mul_of_nonneg_left nativePrice (norm_nonneg _))) (norm_nonneg _) (by positivity)
    _=_:=by unfold sourceJointRadialChannelPrice;dsimp only [zeta];ring

/-- One source-independent analytic shape controls both the true three-dimensional origin and the Schwartz tail. -/
def sourceRadialSchwartzPrice (test : 𝓢(PhysicalMomentum,ℂ)) (n : PhysicalMomentum) : ℝ :=
  ‖test n‖*(1+‖n‖)*(‖n‖^2)⁻¹

theorem sourceRadialSchwartzPrice_integrable (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (sourceRadialSchwartzPrice test) := by
  have measurable : Measurable (sourceRadialSchwartzPrice test) := by unfold sourceRadialSchwartzPrice;fun_prop
  have near : IntegrableOn (sourceRadialSchwartzPrice test) (ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp : 1≤Module.finrank ℝ PhysicalMomentum)
      (α:=2) (C:=2*SchwartzMap.seminorm ℝ 0 0 test) (by norm_num [Module.finrank_fin_fun]) _ measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball] with n hn
    have radius : ‖n‖<1:=by simpa only [mem_ball,dist_zero_right] using hn
    have semi:=SchwartzMap.norm_le_seminorm ℝ test n
    rw [Real.norm_of_nonneg (by unfold sourceRadialSchwartzPrice;positivity)]
    simp only [sourceRadialSchwartzPrice,Real.rpow_neg_eq_inv_rpow,Real.rpow_ofNat,inv_pow]
    have core := mul_le_mul semi (show 1+‖n‖≤2 by linarith)
      (by positivity) ((norm_nonneg (test n)).trans semi)
    calc
      _≤((SchwartzMap.seminorm ℝ 0 0) test*2)*(‖n‖^2)⁻¹ :=
        mul_le_mul_of_nonneg_right core (by positivity)
      _=_:=by ring
  have tail : IntegrableOn (sourceRadialSchwartzPrice test) (ball 0 1)ᶜ := by
    have whole : Integrable (fun n : PhysicalMomentum=>‖test n‖*(1+‖n‖)) := by
      have generated:=test.integrable.norm.add (test.integrable_pow_mul volume 1)
      apply generated.congr
      filter_upwards with n
      simp only [pow_one,Pi.add_apply]
      ring
    apply whole.integrableOn.mono' measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with n hn
    have radius : 1≤‖n‖:=by simpa only [mem_compl_iff,mem_ball,dist_zero_right,not_lt] using hn
    rw [Real.norm_of_nonneg (by unfold sourceRadialSchwartzPrice;positivity)]
    unfold sourceRadialSchwartzPrice
    have bound : (‖n‖^2)⁻¹≤1 := by apply inv_le_one_of_one_le₀; nlinarith
    exact mul_le_of_le_one_right (by positivity) bound
  simpa only [union_compl_self,integrableOn_univ] using near.union tail

private theorem physical_price_shape (n : PhysicalMomentum) (nonzero : n≠0) :
    (1+‖sourceSpatialMomentum n‖)*(‖sourceSpatialMomentum n‖^2)⁻¹≤(1+‖n‖)*(‖n‖^2)⁻¹ := by
  have piPositive : 0<2*Real.pi:=by positivity
  have piLarge : 1≤2*Real.pi:=by linarith [Real.pi_gt_three]
  have normPositive : 0<‖n‖:=norm_pos_iff.mpr nonzero
  have physicalNorm : ‖sourceSpatialMomentum n‖=(2*Real.pi)*‖n‖ := by
    simp only [sourceSpatialMomentum,norm_smul,Real.norm_eq_abs,abs_of_pos piPositive]
  rw [physicalNorm,←div_eq_mul_inv,←div_eq_mul_inv]
  apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos piPositive normPositive)) (sq_pos_of_pos normPositive)).mpr
  have quadratic : 0≤(2*Real.pi)^2-(2*Real.pi):=by nlinarith
  have core : 1+(2*Real.pi)*‖n‖≤(1+‖n‖)*(2*Real.pi)^2 := by
    nlinarith [mul_nonneg quadratic normPositive.le]
  simpa only [mul_pow,mul_assoc] using mul_le_mul_of_nonneg_right core (sq_nonneg ‖n‖)

/-- The original 2pi Fourier phase and actual test are bounded by the same integrable spatial price. -/
theorem sourceJointRadialFourier_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (d : ℝ) (radial : 0<d) (small : d≤1)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ))
    (x n : PhysicalMomentum) (nonzero : n≠0) :
    ‖(d:ℂ)^2*sourceCommonMomentIntegrand q (d*c) (d*eta) l r i 0 0 test x n‖≤
      sourceJointRadialChannelPrice q c eta l r i*sourceRadialSchwartzPrice test n := by
  have momentumNonzero : sourceSpatialMomentum n≠0 := by
    unfold sourceSpatialMomentum
    exact smul_ne_zero (by positivity : (2*Real.pi:ℝ)≠0) nonzero
  have bound:=sourceJointRadialChannel_bound q (sourceSpatialMomentum n) momentumNonzero c eta frequency positive d radial small l r i
  have normalized : (d:ℂ)^2*sourceCommonMomentIntegrand q (d*c) (d*eta) l r i 0 0 test x n=
      sourceSpatialPhase n x*test n*((d:ℂ)^2*sourceCommonCausalChannel q (sourceSpatialMomentum n)
        (sourcePoleSide (d*c) (d*eta)) l r i) := by
    simp only [sourceCommonMomentIntegrand,pow_zero,one_mul]
    ring
  rw [normalized,norm_mul,norm_mul,(paidRadialGreen% phase_norm),one_mul]
  calc
    _≤‖test n‖*(sourceJointRadialChannelPrice q c eta l r i*(1+‖sourceSpatialMomentum n‖)*(‖sourceSpatialMomentum n‖^2)⁻¹) :=
      mul_le_mul_of_nonneg_left bound (norm_nonneg _)
    _=(sourceJointRadialChannelPrice q c eta l r i*‖test n‖)*
      ((1+‖sourceSpatialMomentum n‖)*(‖sourceSpatialMomentum n‖^2)⁻¹) := by ring
    _≤(sourceJointRadialChannelPrice q c eta l r i*‖test n‖)*((1+‖n‖)*(‖n‖^2)⁻¹) :=
      mul_le_mul_of_nonneg_left (physical_price_shape n nonzero)
        (mul_nonneg (channel_price_nonneg q c eta positive l r i) (norm_nonneg _))
    _=_:=by unfold sourceRadialSchwartzPrice;ring

end LowEnergy.PreparationPhysicalJointRadialForcing
