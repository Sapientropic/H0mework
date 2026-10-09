import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelHeatFourier
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNoetherObservationMeter

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChannelGreen
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
local instance ChannelFundamentalIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

private theorem nonzero_of_re_pos {z : ℂ} (positive : 0<z.re) : z≠0 := by
  intro zero
  rw [zero,Complex.zero_re] at positive
  exact lt_irrefl _ positive

private theorem cpow_mul_positive (z : ℂ) (nonzero : z≠0) (r : ℝ) (positive : 0<r) (w : ℂ) :
    (z*(r:ℂ))^w=z^w*(r:ℂ)^w := by
  have rnz : (r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr positive.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero nonzero rnz),Complex.cpow_def_of_ne_zero nonzero,
    Complex.cpow_def_of_ne_zero rnz,Complex.log_mul_ofReal r positive z nonzero,
    ←Complex.ofReal_log positive.le,add_mul,Complex.exp_add,mul_comm]

private theorem cpow_half_square (z : ℂ) : (z^(1/2:ℂ))^2=z := by
  simpa only [one_div] using Complex.cpow_ofNat_inv_pow z 2

private theorem gaussian_scale (z : ℂ) (nonzero : z≠0) (u : ℝ) (positive : 0<u) :
    (z*(u:ℂ)^2)^(3/2:ℂ)=(z^(1/2:ℂ))^3*(u:ℂ)^3 := by
  have sqroot : ((u:ℂ)^2)^(1/2:ℂ)=(u:ℂ) := by
    simpa only [one_div] using Complex.sq_cpow_two_inv (by simpa using positive : 0<(u:ℂ).re)
  rw [show (3/2:ℂ)=3*(1/2:ℂ) by ring,Complex.cpow_ofNat_mul]
  rw [←Complex.ofReal_pow,cpow_mul_positive z nonzero (u^2) (sq_pos_of_pos positive),Complex.ofReal_pow,sqroot,mul_pow]

private def greenAmplitude (kappa : ℂ) : ℂ := ((kappa/(Real.pi:ℂ))^(1/2:ℂ))^3/(2*kappa)

private def greenDensity (kappa : ℂ) (d u : ℝ) (x : PhysicalMomentum) : ℂ :=
  greenAmplitude kappa*Complex.exp (-kappa*
    ((spatialSquare x:ℂ)*(u:ℂ)^2+(d:ℂ)^2/(4*(u:ℂ)^2)))

private def greenKernel (kappa : ℂ) (d : ℝ) (x : PhysicalMomentum) : ℂ :=
  ∫u : ℝ in Ioi 0,greenDensity kappa d u x

private theorem greenDensity_bound (kappa : ℂ) (positive : 0<kappa.re)
    (d u : ℝ) (x : PhysicalMomentum) :
    ‖greenDensity kappa d u x‖≤‖greenAmplitude kappa‖*
      Real.exp (-(kappa.re*spatialSquare x)*u^2) := by
  rw [greenDensity,norm_mul,Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have realForm : (spatialSquare x:ℂ)*(u:ℂ)^2+(d:ℂ)^2/(4*(u:ℂ)^2)=
      ((spatialSquare x*u^2+d^2/(4*u^2):ℝ):ℂ) := by push_cast;ring
  rw [realForm]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have nonnegative : 0≤kappa.re*(d^2/(4*u^2)) := mul_nonneg positive.le (by positivity)
  nlinarith

private theorem greenDensity_integrable (kappa : ℂ) (positive : 0<kappa.re)
    (d : ℝ) (x : PhysicalMomentum) (spatial : 0<spatialSquare x) :
    IntegrableOn (fun u=>greenDensity kappa d u x) (Ioi 0) := by
  have measurable : Measurable (fun u : ℝ=>greenDensity kappa d u x) := by
    unfold greenDensity
    fun_prop
  apply (((integrable_exp_neg_mul_sq (mul_pos positive spatial)).const_mul ‖greenAmplitude kappa‖).integrableOn).mono'
    measurable.aestronglyMeasurable
  exact Eventually.of_forall (fun u=>greenDensity_bound kappa positive d u x)

private theorem greenKernel_limit (kappa : ℂ) (positive : 0<kappa.re)
    (x : PhysicalMomentum) (spatial : 0<spatialSquare x) :
    Tendsto (fun d : ℝ=>greenKernel kappa d x) (𝓝[>] 0) (𝓝 (greenKernel kappa 0 x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (μ:=volume.restrict (Ioi 0))
    (fun u=>‖greenAmplitude kappa‖*Real.exp (-(kappa.re*spatialSquare x)*u^2))
  · exact Eventually.of_forall (fun d=>(greenDensity_integrable kappa positive d x spatial).aestronglyMeasurable)
  · exact Eventually.of_forall (fun d=>Eventually.of_forall (fun u=>greenDensity_bound kappa positive d u x))
  · exact ((integrable_exp_neg_mul_sq (mul_pos positive spatial)).const_mul ‖greenAmplitude kappa‖).integrableOn
  · filter_upwards with u
    have continuous : Continuous (fun d : ℝ=>greenDensity kappa d u x) := by
      unfold greenDensity
      fun_prop
    exact continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem greenKernel_zero (kappa : ℂ) (positive : 0<kappa.re)
    (x : PhysicalMomentum) (spatial : 0<spatialSquare x) :
    greenKernel kappa 0 x=(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare x):ℂ))⁻¹ := by
  let r:=Real.sqrt (spatialSquare x)
  have rp : 0<r:=Real.sqrt_pos.mpr spatial
  have rsquare : r^2=spatialSquare x:=Real.sq_sqrt spatial.le
  have scale:=integral_comp_mul_left_Ioi (fun u : ℝ=>Complex.exp (-kappa*(u:ℂ)^2)) 0 rp
  simp only [mul_zero,Complex.ofReal_mul,mul_pow] at scale
  have gaussian:=integral_gaussian_complex_Ioi positive
  have integral : (∫u : ℝ in Ioi 0,Complex.exp (-kappa*((spatialSquare x:ℂ)*(u:ℂ)^2)))=
      ((r:ℂ)⁻¹)*(((Real.pi:ℂ)/kappa)^(1/2:ℂ)/2) := by
    rw [←rsquare,Complex.ofReal_pow]
    simpa only [mul_assoc,Complex.real_smul,Complex.ofReal_inv,gaussian] using scale
  have knz:=nonzero_of_re_pos positive
  have pnz : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have rnz : (r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr rp.ne'
  let z:=kappa/(Real.pi:ℂ)
  let s:=z^(1/2:ℂ)
  have zp : 0<z.re := by
    simp only [z,Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,Complex.normSq_ofReal]
    simpa only [zero_div,add_zero,pow_two] using div_pos (mul_pos positive Real.pi_pos) (sq_pos_of_pos Real.pi_pos)
  have znz:=nonzero_of_re_pos zp
  have snz : s≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl znz)
  have ssquare : s^2=z:=cpow_half_square z
  have inverse : ((Real.pi:ℂ)/kappa)^(1/2:ℂ)=s⁻¹ := by
    have divided : (Real.pi:ℂ)/kappa=z⁻¹ := by dsimp [z];field_simp
    rw [divided,Complex.inv_cpow z (1/2:ℂ) (Complex.slitPlane_arg_ne_pi (Or.inl zp))]
  simp only [greenKernel,greenDensity,Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_div,add_zero,integral_const_mul]
  rw [integral,inverse]
  change (s^3/(2*kappa))*((r:ℂ)⁻¹*(s⁻¹/2))=(4*(Real.pi:ℂ)*(r:ℂ))⁻¹
  calc
    _=s^2/(4*kappa*(r:ℂ)) := by field_simp [knz,rnz,snz];ring
    _=_ := by rw [ssquare];dsimp only [z];field_simp [knz,pnz,rnz]

/-- Complete generated channel kernel; its Gaussian coefficient comes from the literal source Fourier integral. -/
def sourceChannelFundamentalKernel (branch : Fin 2) (negative : Bool) (eta : ℝ) (i : Fin 3)
    (d : ℝ) (x : PhysicalMomentum) : ℂ :=
  (sourceChargedSpatialCoefficient i:ℂ)⁻¹*greenKernel (sourceChannelMass branch negative eta i) d x

/-- Fixed causal-side radial mass scaling generates the standard coefficient once. The source forcing has not been frozen or moved through this limit. -/
theorem sourceChannelFundamentalKernel_radial (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (x : PhysicalMomentum) (spatial : 0<spatialSquare x) :
    Tendsto (fun d : ℝ=>sourceChannelFundamentalKernel branch negative eta i d x) (𝓝[>] 0)
      (𝓝 ((4*(Real.pi:ℂ)*(sourceChargedSpatialCoefficient i:ℂ)*(Real.sqrt (spatialSquare x):ℂ))⁻¹)) := by
  have result:=(greenKernel_limit (sourceChannelMass branch negative eta i)
    (sourceChannelMass_positive branch negative eta positive i) x spatial).const_mul
      (sourceChargedSpatialCoefficient i:ℂ)⁻¹
  rw [greenKernel_zero _ (sourceChannelMass_positive branch negative eta positive i) x spatial] at result
  have coefficient : (sourceChargedSpatialCoefficient i:ℂ)⁻¹*(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare x):ℂ))⁻¹=
      (4*(Real.pi:ℂ)*(sourceChargedSpatialCoefficient i:ℂ)*(Real.sqrt (spatialSquare x):ℂ))⁻¹ := by
    simp only [mul_inv_rev]
    ring
  rw [coefficient] at result
  simpa only [sourceChannelFundamentalKernel] using result

private def inverseSquareDensity (A : ℂ) (u : ℝ) : ℂ :=
  (u:ℂ)⁻¹^3*Complex.exp (-A/(4*(u:ℂ)^2))

private theorem inverseSquare_integrable (A : ℂ) (positive : 0<A.re) :
    IntegrableOn (inverseSquareDensity A) (Ioi 0) := by
  have expIntegral:=integrableOn_exp_mul_complex_Ioi (a:= -A/4) (by simp only [Complex.div_ofNat_re,Complex.neg_re];linarith) 0
  have changed:=(integrableOn_Ioi_comp_rpow_iff' (fun t : ℝ=>Complex.exp ((-A/4)*(t:ℂ)))
    (p:=(-2:ℝ)) (by norm_num)).mpr expIntegral
  convert changed using 1
  funext u
  simp only [inverseSquareDensity,show (-2:ℝ)-1= -3 by norm_num,Real.rpow_neg_eq_inv_rpow,Real.rpow_ofNat,
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  congr 2
  ring

private theorem inverseSquare_integral (A : ℂ) (positive : 0<A.re) :
    (∫u : ℝ in Ioi 0,inverseSquareDensity A u)=2/A := by
  have changed:=integral_comp_rpow_Ioi (fun t : ℝ=>Complex.exp ((-A/4)*(t:ℂ)))
    (p:=(-2:ℝ)) (by norm_num)
  have point (u : ℝ) : ((|(-2:ℝ)| * u^((-2:ℝ)-1)) • Complex.exp ((-A/4)*(u^(-2:ℝ):ℝ)))=
      2*inverseSquareDensity A u := by
    simp only [show (-2:ℝ)-1= -3 by norm_num,Real.rpow_neg_eq_inv_rpow,Real.rpow_ofNat,
      Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_mul,inverseSquareDensity]
    norm_num only [abs_neg,Complex.ofReal_ofNat]
    have exponent : (-A/4)*(u:ℂ)⁻¹^2= -A/(4*(u:ℂ)^2) := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring
    rw [exponent]
    ring
  simp_rw [point] at changed
  rw [integral_const_mul,integral_exp_mul_complex_Ioi (by simp only [Complex.div_ofNat_re,Complex.neg_re];linarith)] at changed
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero] at changed
  have anz:=nonzero_of_re_pos positive
  apply (mul_left_cancel₀ (by norm_num : (2:ℂ)≠0))
  rw [changed]
  field_simp [anz]
  ring

private def realGaussian (a : ℝ) (x : PhysicalMomentum) : ℝ := Real.exp (-a*spatialSquare x)

private theorem realGaussian_integrable (a : ℝ) (positive : 0<a) : Integrable (realGaussian a) := by
  have h:=GaussianFourier.integrable_cexp_neg_mul_sum_add (b:=(a:ℂ))
    (by simpa using positive) (fun _ : Fin 3=>(0:ℂ))
  convert h.norm using 1
  funext x
  simp only [realGaussian,spatialSquare,Fin.sum_univ_three,zero_mul,add_zero,Complex.norm_exp,
    Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    ←Complex.ofReal_pow,←Complex.ofReal_add,Complex.ofReal_re]

private theorem gaussian_integral_scale (a u : ℝ) (positive : 0<u) :
    (∫x : PhysicalMomentum,realGaussian a (u • x))=u⁻¹^3*(∫x : PhysicalMomentum,realGaussian a x) := by
  have generated:=MeasureTheory.Measure.integral_comp_smul (μ:=volume) (realGaussian a) u
  simpa only [Module.finrank_fin_fun,inv_pow,abs_of_pos (inv_pos.mpr (pow_pos positive 3)),smul_eq_mul] using generated

private theorem density_norm (kappa : ℂ) (d u : ℝ) (x : PhysicalMomentum) :
    ‖greenDensity kappa d u x‖=
      ‖greenAmplitude kappa‖*Real.exp (-(kappa.re*d^2)/(4*u^2))*realGaussian kappa.re (u • x) := by
  have realForm :
      (spatialSquare x:ℂ)*(u:ℂ)^2+(d:ℂ)^2/(4*(u:ℂ)^2)=
        ((spatialSquare x*u^2+d^2/(4*u^2):ℝ):ℂ) := by push_cast;ring
  rw [greenDensity,norm_mul,Complex.norm_exp,realForm]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [realGaussian,mul_assoc,←Real.exp_add]
  congr 2
  simp only [spatialSquare,Pi.smul_apply,smul_eq_mul]
  ring

private theorem density_slice_integrable (kappa : ℂ) (positive : 0<kappa.re) (d u : ℝ) (up : 0<u) :
    Integrable (greenDensity kappa d u) := by
  have measurable : Measurable (greenDensity kappa d u) := by unfold greenDensity spatialSquare;fun_prop
  apply (integrable_norm_iff measurable.aestronglyMeasurable).mp
  simp_rw [density_norm]
  exact ((realGaussian_integrable kappa.re positive).comp_smul up.ne').const_mul _

private theorem density_joint_integrable (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d) :
    Integrable (fun pair : ℝ×PhysicalMomentum=>greenDensity kappa d pair.1 pair.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have measurable : Measurable (fun pair : ℝ×PhysicalMomentum=>greenDensity kappa d pair.1 pair.2) := by
    unfold greenDensity spatialSquare
    fun_prop
  apply (integrable_prod_iff measurable.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u up
    exact density_slice_integrable kappa positive d u up
  · have decay:=(inverseSquare_integrable ((kappa.re*d^2:ℝ):ℂ) (by simpa only [Complex.ofReal_re] using mul_pos positive (sq_pos_of_pos radial))).norm
    have normDecay : (fun u : ℝ=>‖inverseSquareDensity ((kappa.re*d^2:ℝ):ℂ) u‖)=
        fun u=>|u|⁻¹^3*Real.exp (-(kappa.re*d^2)/(4*u^2)) := by
      funext u
      have realForm : -((kappa.re*d^2:ℝ):ℂ)/(4*(u:ℂ)^2)=
          ((-(kappa.re*d^2)/(4*u^2):ℝ):ℂ) := by push_cast;ring
      simp only [inverseSquareDensity,norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_exp,realForm,Complex.ofReal_re]

    rw [normDecay] at decay
    apply ((decay.const_mul ‖greenAmplitude kappa‖).mul_const (∫x : PhysicalMomentum,realGaussian kappa.re x)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u up
    simp only [density_norm,integral_const_mul,gaussian_integral_scale kappa.re u up,abs_of_pos (show 0<u from up)]
    ring

private theorem greenKernel_integrable (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d) :
    Integrable (greenKernel kappa d) := by
  exact (density_joint_integrable kappa positive d radial).integral_prod_right

private theorem reciprocal_gaussian (kappa : ℂ) (positive : 0<kappa.re) (u : ℝ) (up : 0<u) :
    greenAmplitude kappa*((Real.pi:ℂ)/(kappa*(u:ℂ)^2))^(3/2:ℂ)=
      (2*kappa*(u:ℂ)^3)⁻¹ := by
  have knz:=nonzero_of_re_pos positive
  have pnz : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have unz : (u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr up.ne'
  let z:=kappa/(Real.pi:ℂ)
  have znz : z≠0:=div_ne_zero knz pnz
  have real : 0<(z*(u:ℂ)^2).re := by
    simp only [z,←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
      Complex.div_re,Complex.normSq_ofReal]
    simpa only [zero_div,add_zero,pow_two] using mul_pos (div_pos (mul_pos positive Real.pi_pos) (sq_pos_of_pos Real.pi_pos)) (sq_pos_of_pos up)
  have reciprocal : (Real.pi:ℂ)/(kappa*(u:ℂ)^2)=(z*(u:ℂ)^2)⁻¹ := by dsimp only [z];field_simp
  rw [reciprocal,Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi (Or.inl real)),gaussian_scale z znz u up]
  have rootnz : z^(1/2:ℂ)≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl znz)
  unfold greenAmplitude
  change ((z^(1/2:ℂ))^3/(2*kappa))*((z^(1/2:ℂ))^3*(u:ℂ)^3)⁻¹=_
  field_simp [rootnz,knz,unz]

private theorem phase_norm (frequency x : PhysicalMomentum) : ‖sourceSpatialPhase frequency x‖=1 := by
  simp [sourceSpatialPhase,Complex.norm_exp]

private theorem density_fourier (kappa : ℂ) (positive : 0<kappa.re) (d u : ℝ) (up : 0<u)
    (frequency : PhysicalMomentum) :
    (∫x : PhysicalMomentum,sourceSpatialPhase (-frequency) x*greenDensity kappa d u x)=
      (2*kappa)⁻¹*inverseSquareDensity
        ((spatialSquare (sourceSpatialMomentum frequency):ℂ)/kappa+(d:ℂ)^2*kappa) u := by
  have knz:=nonzero_of_re_pos positive
  have unz : (u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr up.ne'
  let b:=kappa*(u:ℂ)^2
  let c : Fin 3→ℂ:=fun j=> -((2*Real.pi:ℝ):ℂ)*Complex.I*(frequency j:ℂ)
  have bp : 0<b.re := by
    simp only [b,←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_pos positive (sq_pos_of_pos up)
  have point (x : PhysicalMomentum) : sourceSpatialPhase (-frequency) x*greenDensity kappa d u x=
      (greenAmplitude kappa*Complex.exp (-kappa*(d:ℂ)^2/(4*(u:ℂ)^2)))*
        Complex.exp (-b*(∑j : Fin 3,(x j:ℂ)^2)+∑j : Fin 3,c j*(x j:ℂ)) := by
    have exponents : Complex.I*((∑j : Fin 3,sourceSpatialMomentum (-frequency) j*x j:ℝ):ℂ)+
        -kappa*((spatialSquare x:ℂ)*(u:ℂ)^2+(d:ℂ)^2/(4*(u:ℂ)^2))=
      -kappa*(d:ℂ)^2/(4*(u:ℂ)^2)+(-b*(∑j : Fin 3,(x j:ℂ)^2)+∑j : Fin 3,c j*(x j:ℂ)) := by
      simp only [b,c,sourceSpatialMomentum,spatialSquare,Pi.smul_apply,Pi.neg_apply,smul_eq_mul,
        Fin.sum_univ_three,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg]
      ring
    rw [sourceSpatialPhase,greenDensity]
    calc
      _=greenAmplitude kappa*(Complex.exp (Complex.I*((∑j : Fin 3,sourceSpatialMomentum (-frequency) j*x j:ℝ):ℂ))*
        Complex.exp (-kappa*((spatialSquare x:ℂ)*(u:ℂ)^2+(d:ℂ)^2/(4*(u:ℂ)^2)))) := by ring
      _=_ := by rw [←Complex.exp_add,exponents,Complex.exp_add];ring
  simp_rw [point]
  rw [integral_const_mul,GaussianFourier.integral_cexp_neg_mul_sum_add bp]
  norm_num only [Fintype.card_fin]
  have spatialExponent : (∑j : Fin 3,c j^2)/(4*b)=
      -(spatialSquare (sourceSpatialMomentum frequency):ℂ)/(4*kappa*(u:ℂ)^2) := by
    simp only [c,b,sourceSpatialMomentum,spatialSquare,Pi.smul_apply,smul_eq_mul,
      Fin.sum_univ_three,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
    ring_nf
    simp only [Complex.I_sq,Complex.ofReal_ofNat]
    ring
  rw [spatialExponent]
  calc
    _=(greenAmplitude kappa*((Real.pi:ℂ)/(kappa*(u:ℂ)^2))^(3/2:ℂ))*
      (Complex.exp (-kappa*(d:ℂ)^2/(4*(u:ℂ)^2))*
        Complex.exp (-(spatialSquare (sourceSpatialMomentum frequency):ℂ)/(4*kappa*(u:ℂ)^2))) := by dsimp only [b];ring
    _=_ := by
      rw [reciprocal_gaussian kappa positive u up,←Complex.exp_add]
      unfold inverseSquareDensity
      have exponents : -kappa*(d:ℂ)^2/(4*(u:ℂ)^2)-
          (spatialSquare (sourceSpatialMomentum frequency):ℂ)/(4*kappa*(u:ℂ)^2)=
        -((spatialSquare (sourceSpatialMomentum frequency):ℂ)/kappa+(d:ℂ)^2*kappa)/(4*(u:ℂ)^2) := by ring
      rw [neg_div,←sub_eq_add_neg,exponents]
      field_simp [knz,unz]

private theorem kernel_rate_positive (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (n : PhysicalMomentum) : 0<((spatialSquare n:ℂ)/kappa+(d:ℂ)^2*kappa).re := by
  have knz:=nonzero_of_re_pos positive
  simp only [Complex.add_re,Complex.div_re,←Complex.ofReal_pow,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  apply add_pos_of_nonneg_of_pos
  · simpa only [zero_div,add_zero] using div_nonneg (mul_nonneg (show 0 ≤ spatialSquare n by unfold spatialSquare;positivity) positive.le) (Complex.normSq_nonneg kappa)
  · exact mul_pos (sq_pos_of_pos radial) positive

private theorem greenKernel_fourier (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (frequency : PhysicalMomentum) :
    (∫x : PhysicalMomentum,sourceSpatialPhase (-frequency) x*greenKernel kappa d x)=
      ((spatialSquare (sourceSpatialMomentum frequency):ℂ)+(d:ℂ)^2*kappa^2)⁻¹ := by
  have raw:=density_joint_integrable kappa positive d radial
  have measurable : Measurable (fun pair : ℝ×PhysicalMomentum=>sourceSpatialPhase (-frequency) pair.2*greenDensity kappa d pair.1 pair.2) := by
    unfold sourceSpatialPhase sourceSpatialMomentum greenDensity spatialSquare
    fun_prop
  have joint : Integrable (fun pair : ℝ×PhysicalMomentum=>sourceSpatialPhase (-frequency) pair.2*greenDensity kappa d pair.1 pair.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
    apply raw.norm.mono' measurable.aestronglyMeasurable
    filter_upwards with pair
    rw [norm_mul,phase_norm,one_mul]
  unfold greenKernel
  simp_rw [←integral_const_mul]
  rw [←integral_integral_swap joint]
  have generated : (∫u : ℝ in Ioi 0,∫x : PhysicalMomentum,sourceSpatialPhase (-frequency) x*greenDensity kappa d u x)=
      (2*kappa)⁻¹*(∫u : ℝ in Ioi 0,inverseSquareDensity
        ((spatialSquare (sourceSpatialMomentum frequency):ℂ)/kappa+(d:ℂ)^2*kappa) u) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u up
    exact density_fourier kappa positive d u up frequency
  rw [generated,inverseSquare_integral _ (kernel_rate_positive kappa positive d radial _)]
  have knz:=nonzero_of_re_pos positive
  have rateNZ:=nonzero_of_re_pos (kernel_rate_positive kappa positive d radial (sourceSpatialMomentum frequency))
  have denominatorNZ : (spatialSquare (sourceSpatialMomentum frequency):ℂ)+(d:ℂ)^2*kappa^2≠0 := by
    intro zero
    apply rateNZ
    field_simp [knz]
    linear_combination zero
  field_simp [knz,rateNZ,denominatorNZ]

/-- The full fundamental kernel has exactly the original physical Fourier multiplier. -/
theorem sourceChannelFundamentalKernel_fourier (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (d : ℝ) (radial : 0<d) (frequency : PhysicalMomentum) :
    (∫x : PhysicalMomentum,sourceSpatialPhase (-frequency) x*sourceChannelFundamentalKernel branch negative eta i d x)=
      ((sourceChargedSpatialCoefficient i:ℂ)*((spatialSquare (sourceSpatialMomentum frequency):ℂ)+
        (d:ℂ)^2*(sourceChannelMass branch negative eta i)^2))⁻¹ := by
  have point (x : PhysicalMomentum) : sourceSpatialPhase (-frequency) x*sourceChannelFundamentalKernel branch negative eta i d x=
      (sourceChargedSpatialCoefficient i:ℂ)⁻¹*(sourceSpatialPhase (-frequency) x*greenKernel (sourceChannelMass branch negative eta i) d x) := by
    unfold sourceChannelFundamentalKernel
    ring
  simp_rw [point]
  rw [integral_const_mul,greenKernel_fourier _ (sourceChannelMass_positive branch negative eta positive i) d radial]
  simp only [mul_inv_rev,mul_comm]

private theorem phase_sub (frequency x y : PhysicalMomentum) :
    sourceSpatialPhase frequency (x-y)=sourceSpatialPhase frequency x*sourceSpatialPhase (-frequency) y := by
  rw [sourceSpatialPhase,sourceSpatialPhase,sourceSpatialPhase,←Complex.exp_add]
  congr 1
  simp only [sourceSpatialMomentum,Pi.smul_apply,Pi.sub_apply,Pi.neg_apply,smul_eq_mul,
    Fin.sum_univ_three,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

private theorem kernel_convolution (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (forcing : PhysicalMomentum→ℂ) (integrable : Integrable forcing) (x : PhysicalMomentum) :
    (∫y : PhysicalMomentum,greenKernel kappa d y*
      (∫frequency : PhysicalMomentum,sourceSpatialPhase frequency (x-y)*forcing frequency))=
    ∫frequency : PhysicalMomentum,sourceSpatialPhase frequency x*
      (((spatialSquare (sourceSpatialMomentum frequency):ℂ)+(d:ℂ)^2*kappa^2)⁻¹*forcing frequency) := by
  have kernel:=greenKernel_integrable kappa positive d radial
  have phase : Continuous (fun pair : PhysicalMomentum×PhysicalMomentum=>sourceSpatialPhase pair.2 (x-pair.1)) := by
    unfold sourceSpatialPhase sourceSpatialMomentum
    fun_prop
  have measurable : AEStronglyMeasurable
      (fun pair : PhysicalMomentum×PhysicalMomentum=>greenKernel kappa d pair.1*
        sourceSpatialPhase pair.2 (x-pair.1)*forcing pair.2) (volume.prod volume) :=
    (kernel.aestronglyMeasurable.comp_fst.mul phase.aestronglyMeasurable).mul integrable.aestronglyMeasurable.comp_snd
  have joint : Integrable
      (fun pair : PhysicalMomentum×PhysicalMomentum=>greenKernel kappa d pair.1*
        sourceSpatialPhase pair.2 (x-pair.1)*forcing pair.2) (volume.prod volume) := by
    apply (kernel.norm.mul_prod integrable.norm).mono' measurable
    filter_upwards with pair
    rw [norm_mul,norm_mul,phase_norm,mul_one]
  simp_rw [←integral_const_mul]
  have reassociate (y frequency : PhysicalMomentum) : greenKernel kappa d y*
      (sourceSpatialPhase frequency (x-y)*forcing frequency)=
      greenKernel kappa d y*sourceSpatialPhase frequency (x-y)*forcing frequency := by ring
  simp_rw [reassociate]
  rw [integral_integral_swap joint]
  apply integral_congr_ae
  filter_upwards with frequency
  have point (y : PhysicalMomentum) : greenKernel kappa d y*sourceSpatialPhase frequency (x-y)*forcing frequency=
      (sourceSpatialPhase frequency x*forcing frequency)*(sourceSpatialPhase (-frequency) y*greenKernel kappa d y) := by
    rw [phase_sub]
    ring
  simp_rw [point]
  rw [integral_const_mul,greenKernel_fourier kappa positive d radial frequency]
  ring

/-- Actual source forcing enters the spatial fundamental kernel as a legal convolution. -/
def sourceChannelPhysicalPotential (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (q : PhysicalResponsePoint) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫y : PhysicalMomentum,sourceChannelFundamentalKernel branch negative eta i 1 y*
    sourceCommonSpatialForcing q (sourceSignedSpeed branch negative) eta l r i test (x-y)

/-- The original full current's spatial source has its already generated integrability, without an angular or terminal scalar premise. -/
theorem sourceChannelPhysicalPotential_return (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (q : PhysicalResponsePoint) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceChannelPhysicalPotential branch negative eta q l r i test x=
      sourceCommonSpatialMoment q (sourceSignedSpeed branch negative) eta l r i 0 0 test x := by
  let c:=sourceSignedSpeed branch negative
  let kappa:=sourceChannelMass branch negative eta i
  let forcing : PhysicalMomentum→ℂ:=fun frequency=>test frequency*
    sourceSlowRead (sourceActualNativeResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r) ⟨i.val,by omega⟩
  have input : Integrable forcing := by
    have paid:=sourceCommonSpatialForcing_integrable q c eta (sourceSignedSpeed_nonzero branch negative) positive l r i test 0
    simpa only [sourceSpatialPhase,Pi.zero_apply,mul_zero,Finset.sum_const_zero,Complex.ofReal_zero,Complex.exp_zero,one_mul] using paid
  have generated:=kernel_convolution kappa (sourceChannelMass_positive branch negative eta positive i) 1 (by norm_num) forcing input x
  unfold sourceChannelPhysicalPotential sourceChannelFundamentalKernel sourceCommonSpatialForcing
  have point (y : PhysicalMomentum) : (sourceChargedSpatialCoefficient i:ℂ)⁻¹*greenKernel kappa 1 y*
      (∫frequency : PhysicalMomentum,sourceSpatialPhase frequency (x-y)*test frequency*
        sourceSlowRead (sourceActualNativeResidue q (sourceSpatialMomentum frequency) (sourcePoleSide c eta) l r) ⟨i.val,by omega⟩)=
      (sourceChargedSpatialCoefficient i:ℂ)⁻¹*(greenKernel kappa 1 y*
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
  simp only [pow_zero,one_mul,Complex.ofReal_one,one_pow,sourceCommonCausalChannel,forcing]
  rw [sourceChannelDenominator_generated branch negative eta (sourceSpatialMomentum frequency) i,mul_inv_rev]
  dsimp only [kappa,c]
  ring

/-- The complete original source64 field is assembled from the three actual fundamental potentials. -/
def sourceActualFundamentalPotential (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    (∑i : Fin 3,sourceChannelPhysicalPotential branch negative eta q l r i test x • sourceCommonOriginColumn i)

theorem sourceActualFundamentalPotential_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (positive : 0<eta)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualFundamentalPotential q sL eL sR eR branch negative eta test x=
      sourceActualSpatialField q sL eL sR eR (sourceSignedSpeed branch negative) eta test x := by
  rw [sourceActualSpatialField_generated q sL eL sR eR _ eta (sourceSignedSpeed_nonzero branch negative) positive test x]
  simp only [sourceActualFundamentalPotential,sourceChannelPhysicalPotential_return branch negative eta positive,
    sourceCommonSpatialField_generated q _ eta (sourceSignedSpeed_nonzero branch negative) positive]

/-- Both actual current families observe the same fundamental potential, including every source64 and detector64 coefficient. -/
theorem sourceActualFundamentalPotential_observed (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (nonrealL : qd.z.im≠0) (nonrealR : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
      (sourceActualFundamentalPotential q sL eL sR eR branch negative eta test x)=
      sourceActualSpatialAmplitude q sL eL sR eR (sourceSignedSpeed branch negative) eta test x*
        (∑a : RestStateIndex,∑b : RestStateIndex,sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*actualGaussWeight qd a b T) := by
  rw [sourceActualFundamentalPotential_return q sL eL sR eR branch negative eta positive test x]
  exact sourceActualSpatialDetector_generated qd q dSL dEL dSR dER sL eL sR eR T _ eta
    (sourceSignedSpeed_nonzero branch negative) positive nonrealL nonrealR test x

/-- The original action-derived hQ meter reads this same fundamental potential; its charge insertion is not identified with the raw field response. -/
theorem sourceActualFundamentalPotential_charge (qd q : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (i j : ActualPreparedIndex) :
    sourceNoetherFieldMeter qd 0 0 0 T
      (sourceActualFundamentalPotential q sL eL sR eR branch negative eta test x) i j=
      sourceActualSpatialAmplitude q sL eL sR eR (sourceSignedSpeed branch negative) eta test x*
        sourceActualPreparedGaussWeight qd i.1 i.2 j.1 j.2 T*(sourceActualPhaseCharge j.2:ℂ) := by
  rw [sourceActualFundamentalPotential_return q sL eL sR eR branch negative eta positive test x]
  exact sourceNoetherSpatialMeter_return qd q sL eL sR eR T _ eta
    (sourceSignedSpeed_nonzero branch negative) positive left right test x i j

end LowEnergy.PreparationPhysicalChannelGreen
