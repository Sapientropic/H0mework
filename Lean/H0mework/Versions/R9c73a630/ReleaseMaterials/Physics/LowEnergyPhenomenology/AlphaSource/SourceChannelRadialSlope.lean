import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelRadialLayer

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
local instance ChannelRadialSlopeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open Lean Elab Term in
elab "paidRadialGreen% " id:ident : term => do
  let wanted:=`LowEnergy.PreparationPhysicalChannelGreen ++ id.getId
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelFundamentalPotential." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceChannelFundamentalPotential payer {wanted}"

open Lean Elab Term in
elab "paidRadialLayer% " id:ident : term => do
  let wanted:=`LowEnergy.PreparationPhysicalChannelRadialJet ++ id.getId
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelRadialLayer." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceChannelRadialLayer payer {wanted}"

private abbrev amplitude : ℂ→ℂ:=paidRadialGreen% greenAmplitude
private abbrev density : ℂ→ℝ→ℝ→PhysicalMomentum→ℂ:=paidRadialGreen% greenDensity
private abbrev kernel : ℂ→ℝ→PhysicalMomentum→ℂ:=paidRadialGreen% greenKernel
private abbrev deficit : ℂ→ℝ→ℂ:=paidRadialLayer% gaussianDeficit

private def smallLayer (kappa : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-kappa/(4*(u:ℂ)^2))-1

private theorem smallLayer_integrable (kappa : ℂ) (positive : 0<kappa.re) :
    IntegrableOn (smallLayer kappa) (Ioi 0) := by
  have paid : IntegrableOn (deficit kappa) (Ioi 0):=(paidRadialLayer% deficit_integrable) kappa positive
  have changed:=(integrableOn_Ioi_comp_rpow_iff' (deficit kappa) (p:=(-1:ℝ)) (by norm_num)).mpr paid
  have inverse : IntegrableOn (fun u : ℝ=>Complex.exp (-kappa/(u:ℂ)^2)-1) (Ioi 0) := by
    apply changed.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u up
    change u^((-1:ℝ)-1) • ((Complex.exp (-kappa*((u^(-1:ℝ):ℝ):ℂ)^2)-1)/((u^(-1:ℝ):ℝ):ℂ)^2)=_
    simp only [show (-1:ℝ)-1= -2 by norm_num,Real.rpow_neg_eq_inv_rpow,
      Real.rpow_ofNat,Real.rpow_one,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
    have unz : (u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr up.ne'
    have exponent : -kappa*(u:ℂ)⁻¹^2= -kappa/(u:ℂ)^2 := by rw [div_eq_mul_inv,inv_pow]
    rw [exponent]
    field_simp
  have scaled:=(integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ=>Complex.exp (-kappa/(u:ℂ)^2)-1) 0 (by norm_num : (0:ℝ)<2)).mpr (by simpa using inverse)
  convert scaled using 1
  funext u
  simp only [smallLayer,Complex.ofReal_mul,Complex.ofReal_ofNat,mul_pow]
  norm_num

private theorem smallLayer_integral (kappa : ℂ) (positive : 0<kappa.re) :
    (∫u : ℝ in Ioi 0,smallLayer kappa u)=
      -kappa*((Real.pi:ℂ)/kappa)^(1/2:ℂ)/2 := by
  have changed:=integral_comp_rpow_Ioi (deficit kappa) (p:=(-1:ℝ)) (by norm_num)
  have inverse : (∫u : ℝ in Ioi 0,Complex.exp (-kappa/(u:ℂ)^2)-1)=∫t : ℝ in Ioi 0,deficit kappa t := by
    rw [←changed]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u up
    change _=(|(-1:ℝ)| * u^((-1:ℝ)-1)) •
      ((Complex.exp (-kappa*((u^(-1:ℝ):ℝ):ℂ)^2)-1)/((u^(-1:ℝ):ℝ):ℂ)^2)
    simp only [show (-1:ℝ)-1= -2 by norm_num,Real.rpow_neg_eq_inv_rpow,
      Real.rpow_ofNat,Real.rpow_one,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_mul]
    norm_num only [abs_neg,abs_one,Complex.ofReal_one,one_mul]
    have unz : (u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr up.ne'
    have exponent : -kappa*(u:ℂ)⁻¹^2= -kappa/(u:ℂ)^2 := by rw [div_eq_mul_inv,inv_pow]
    rw [exponent]
    field_simp
  have scaled:=integral_comp_mul_left_Ioi (fun u : ℝ=>Complex.exp (-kappa/(u:ℂ)^2)-1) 0 (by norm_num : (0:ℝ)<2)
  have point (u : ℝ) : Complex.exp (-kappa/((2*u:ℝ):ℂ)^2)-1=smallLayer kappa u := by
    simp only [smallLayer,Complex.ofReal_mul,Complex.ofReal_ofNat,mul_pow]
    norm_num
  simp_rw [point] at scaled
  simp only [mul_zero,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_ofNat] at scaled
  rw [scaled,inverse,(paidRadialLayer% deficit_integral) kappa positive]
  ring

private def rescaledLayer (kappa : ℂ) (x : PhysicalMomentum) (d u : ℝ) : ℂ :=
  amplitude kappa*Complex.exp (-kappa*((spatialSquare x:ℂ)*(d:ℂ)^2*(u:ℂ)^2))*smallLayer kappa u

private theorem rescaledLayer_bound (kappa : ℂ) (positive : 0<kappa.re)
    (x : PhysicalMomentum) (d u : ℝ) :
    ‖rescaledLayer kappa x d u‖≤‖amplitude kappa‖*‖smallLayer kappa u‖ := by
  have exponential : ‖Complex.exp (-kappa*((spatialSquare x:ℂ)*(d:ℂ)^2*(u:ℂ)^2))‖≤1 := by
    rw [Complex.norm_exp,←Real.exp_zero]
    apply Real.exp_le_exp.mpr
    rw [show (spatialSquare x:ℂ)*(d:ℂ)^2*(u:ℂ)^2=((spatialSquare x*d^2*u^2:ℝ):ℂ) by push_cast;ring]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr positive.le) (by unfold spatialSquare;positivity)
  simp only [rescaledLayer,norm_mul]
  calc
    _≤‖amplitude kappa‖*1*‖smallLayer kappa u‖:=by gcongr
    _=_:=by ring

private theorem rescaledLayer_integrable (kappa : ℂ) (positive : 0<kappa.re)
    (x : PhysicalMomentum) (d : ℝ) : IntegrableOn (rescaledLayer kappa x d) (Ioi 0) := by
  have measurable : Measurable (rescaledLayer kappa x d) := by unfold rescaledLayer smallLayer;fun_prop
  apply ((smallLayer_integrable kappa positive).norm.const_mul ‖amplitude kappa‖).mono' measurable.aestronglyMeasurable
  exact Eventually.of_forall (rescaledLayer_bound kappa positive x d)

private theorem rescaledLayer_limit (kappa : ℂ) (positive : 0<kappa.re) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>∫u : ℝ in Ioi 0,rescaledLayer kappa x d u) (𝓝[>] 0)
      (𝓝 (amplitude kappa*(-kappa*((Real.pi:ℂ)/kappa)^(1/2:ℂ)/2))) := by
  have integral : (∫u : ℝ in Ioi 0,rescaledLayer kappa x 0 u)=
      amplitude kappa*(-kappa*((Real.pi:ℂ)/kappa)^(1/2:ℂ)/2) := by
    simp only [rescaledLayer,Complex.ofReal_zero,zero_pow (by omega : 2≠0),mul_zero,zero_mul,Complex.exp_zero,mul_one]
    rw [integral_const_mul,smallLayer_integral kappa positive]
  rw [←integral]
  apply tendsto_integral_filter_of_dominated_convergence (μ:=volume.restrict (Ioi 0))
    (fun u=>‖amplitude kappa‖*‖smallLayer kappa u‖)
  · exact Eventually.of_forall (fun d=>(rescaledLayer_integrable kappa positive x d).aestronglyMeasurable)
  · exact Eventually.of_forall (fun d=>Eventually.of_forall (rescaledLayer_bound kappa positive x d))
  · exact (smallLayer_integrable kappa positive).norm.const_mul _
  · filter_upwards with u
    have continuous : Continuous (fun d : ℝ=>rescaledLayer kappa x d u) := by unfold rescaledLayer;fun_prop
    exact continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem kernel_slope_generated (kappa : ℂ) (positive : 0<kappa.re)
    (x : PhysicalMomentum) (spatial : 0<spatialSquare x) (d : ℝ) (radial : 0<d) :
    (d:ℂ)⁻¹*(kernel kappa d x-kernel kappa 0 x)=
      ∫u : ℝ in Ioi 0,rescaledLayer kappa x d u := by
  have one : IntegrableOn (fun u=>density kappa d u x) (Ioi 0):=
    (paidRadialGreen% greenDensity_integrable) kappa positive d x spatial
  have zero : IntegrableOn (fun u=>density kappa 0 u x) (Ioi 0):=
    (paidRadialGreen% greenDensity_integrable) kappa positive 0 x spatial
  have scaled:=integral_comp_mul_left_Ioi (fun u : ℝ=>density kappa d u x-density kappa 0 u x) 0 radial
  have point (u : ℝ) (up : u∈Ioi (0:ℝ)) :
      density kappa d (d*u) x-density kappa 0 (d*u) x=rescaledLayer kappa x d u := by
    change amplitude kappa*Complex.exp (-kappa*((spatialSquare x:ℂ)*((d*u:ℝ):ℂ)^2+(d:ℂ)^2/(4*((d*u:ℝ):ℂ)^2)))-
      amplitude kappa*Complex.exp (-kappa*((spatialSquare x:ℂ)*((d*u:ℝ):ℂ)^2+(0:ℂ)^2/(4*((d*u:ℝ):ℂ)^2)))=_
    have exponent : -kappa*((spatialSquare x:ℂ)*((d*u:ℝ):ℂ)^2+(d:ℂ)^2/(4*((d*u:ℝ):ℂ)^2))=
        -kappa*((spatialSquare x:ℂ)*(d:ℂ)^2*(u:ℂ)^2)+(-kappa/(4*(u:ℂ)^2)) := by
      simp only [Complex.ofReal_mul,mul_pow]
      field_simp [Complex.ofReal_ne_zero.mpr radial.ne',Complex.ofReal_ne_zero.mpr up.ne']
      ring
    rw [exponent,Complex.exp_add]
    simp only [rescaledLayer,smallLayer,Complex.ofReal_mul,mul_pow,zero_pow (by omega : 2≠0),zero_div,add_zero]
    ring
  have replaced : (∫u : ℝ in Ioi 0,density kappa d (d*u) x-density kappa 0 (d*u) x)=
      ∫u : ℝ in Ioi 0,rescaledLayer kappa x d u:=setIntegral_congr_fun measurableSet_Ioi point
  rw [replaced] at scaled
  simp only [mul_zero,Complex.real_smul,Complex.ofReal_inv] at scaled
  rw [integral_sub one zero] at scaled
  exact scaled.symm

private theorem amplitude_coefficient (kappa : ℂ) (positive : 0<kappa.re) :
    amplitude kappa*(-kappa*((Real.pi:ℂ)/kappa)^(1/2:ℂ)/2)= -kappa/(4*(Real.pi:ℂ)) := by
  have knz : kappa≠0:=by intro zero;rw [zero,Complex.zero_re] at positive;exact lt_irrefl _ positive
  have pnz : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have reciprocal:= (paidRadialGreen% reciprocal_gaussian) kappa positive 1 (by norm_num)
  simp only [Complex.ofReal_one,one_pow,mul_one] at reciprocal
  have power : ((Real.pi:ℂ)/kappa)^(3/2:ℂ)=((Real.pi:ℂ)/kappa)^(1/2:ℂ)*((Real.pi:ℂ)/kappa) := by
    rw [show (3/2:ℂ)=(1/2:ℂ)+1 by ring,Complex.cpow_add _ _ (div_ne_zero pnz knz),Complex.cpow_one]
  rw [power] at reciprocal
  field_simp [knz,pnz] at reciprocal
  change amplitude kappa*(Real.pi:ℂ)*2*((Real.pi:ℂ)/kappa)^(1/2:ℂ)=1 at reciprocal
  calc
    _=(-kappa/(4*(Real.pi:ℂ)))*(amplitude kappa*(Real.pi:ℂ)*2*((Real.pi:ℂ)/kappa)^(1/2:ℂ)) := by
      field_simp [pnz]
      ring
    _=_ := by rw [reciprocal,mul_one]

/-- The actual spatial kernel has a nonzero first radial jet from its complete small-u layer. -/
theorem sourceChannelFundamentalKernel_slope (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) (x : PhysicalMomentum) (spatial : 0<spatialSquare x) :
    Tendsto (fun d : ℝ=>(d:ℂ)⁻¹*(sourceChannelFundamentalKernel branch negative eta i d x-
      sourceChannelFundamentalKernel branch negative eta i 0 x)) (𝓝[>] 0)
      (𝓝 (-sourceChannelMass branch negative eta i/(4*(Real.pi:ℂ)*(sourceChargedSpatialCoefficient i:ℂ)))) := by
  let kappa:=sourceChannelMass branch negative eta i
  have kp:=sourceChannelMass_positive branch negative eta positive i
  have generated:=(rescaledLayer_limit kappa kp x).const_mul (sourceChargedSpatialCoefficient i:ℂ)⁻¹
  rw [amplitude_coefficient kappa kp] at generated
  have coefficient : (sourceChargedSpatialCoefficient i:ℂ)⁻¹*(-kappa/(4*(Real.pi:ℂ)))=
      -kappa/(4*(Real.pi:ℂ)*(sourceChargedSpatialCoefficient i:ℂ)) := by ring
  rw [coefficient] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with d dp
  rw [←kernel_slope_generated kappa kp x spatial d dp]
  unfold sourceChannelFundamentalKernel
  ring

end LowEnergy.PreparationPhysicalChannelRadialJet
