import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCausalSpatialDilation

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCausalSpatialDilation
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
local instance CausalEulerIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
attribute [local irreducible] sourceMasterChannel sourceMasterChannelDerivative sourceMasterChannelCorrection
  sourceActualPreparedWeight sourceCommonOriginColumn sourceMasterSpatialChannel

open Lean Elab Term in
elab "paidDilationContinuity%" : term => do
  let wanted:=`LowEnergy.PreparationPhysicalRetainerResolventSquare.master_channel_continuous
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCausalMasterDerivative." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original master_channel_continuous payer"

private def phaseLinear (x : PhysicalMomentum) : PhysicalMomentum→L[ℝ]ℝ :=
  (show PhysicalMomentum→ₗ[ℝ]ℝ from
    {toFun:=fun n=>∑j,sourceSpatialMomentum n j*x j
     map_add':=by intro n m;simp [sourceSpatialMomentum,Pi.add_apply,add_mul,mul_add,Finset.sum_add_distrib]
     map_smul':=by
       intro s n
       simp only [sourceSpatialMomentum,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
       apply Finset.sum_congr rfl
       intro j _
       ring}).toContinuousLinearMap

private theorem phase_scaled (n x : PhysicalMomentum) (s : ℝ) :
    sourceSpatialPhase n (s • x)=Complex.exp ((s:ℂ)*(Complex.I*(phaseLinear x n:ℂ))) := by
  unfold sourceSpatialPhase
  have argument : (∑j,sourceSpatialMomentum n j*(s • x) j : ℝ)=s*phaseLinear x n := by
    change (∑j,sourceSpatialMomentum n j*(s • x) j)=s*(∑j,sourceSpatialMomentum n j*x j)
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [argument,Complex.ofReal_mul]
  congr 1
  ring

private theorem phase_norm (n x : PhysicalMomentum) : ‖sourceSpatialPhase n x‖=1 :=
  (paidRadialGreen% phase_norm) n x

private def decayPrice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (test : 𝓢(PhysicalMomentum,F)) : ℝ :=
  2^6*(Finset.Iic (6,0)).sup (fun m=>SchwartzMap.seminorm ℝ m.1 m.2) test

private theorem decay_price_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (test : 𝓢(PhysicalMomentum,F)) : 0≤ decayPrice test := by unfold decayPrice;positivity

private theorem decay_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (test : 𝓢(PhysicalMomentum,F)) (n : PhysicalMomentum) :
    (1+‖n‖)^6*‖test n‖≤ decayPrice test := by
  simpa only [norm_iteratedFDeriv_zero,decayPrice] using
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ) (m:=(6,0)) (k:=6) (n:=0) le_rfl le_rfl test n

private def dilationPrice (d : ℝ) : ℝ:=1+2/d

private theorem dilation_compare (d : ℝ) (positive : 0<d) (s : ℝ) (lower : d/2≤ s)
    (n : PhysicalMomentum) : 1+‖n‖≤ dilationPrice d*(1+‖s • n‖) := by
  have sp : 0<s:=lt_of_lt_of_le (by positivity) lower
  have reciprocal : 1≤(2/d)*s := by
    rw [div_mul_eq_mul_div]
    apply (one_le_div positive).mpr
    linarith
  have inverseNonneg : 0≤2/d:=by positivity
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos sp,dilationPrice]
  calc
    1+‖n‖≤1+((2/d)*s)*‖n‖:=add_le_add (le_refl 1) (le_mul_of_one_le_left (norm_nonneg n) reciprocal)
    _≤1+((2/d)*s)*‖n‖+2/d+s*‖n‖:=by linarith [mul_nonneg sp.le (norm_nonneg n)]
    _=(1+2/d)*(1+s*‖n‖):=by ring

private theorem dilated_decay {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (test : 𝓢(PhysicalMomentum,F)) (d : ℝ) (positive : 0<d) (s : ℝ) (lower : d/2≤ s)
    (n : PhysicalMomentum) : ‖test (s • n)‖≤(dilationPrice d)^6*decayPrice test/(1+‖n‖)^6 := by
  apply (le_div_iff₀ (pow_pos (by positivity : 0<1+‖n‖) 6)).mpr
  calc
    _=(1+‖n‖)^6*‖test (s • n)‖:=by ring
    _≤(dilationPrice d*(1+‖s • n‖))^6*‖test (s • n)‖:=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (dilation_compare d positive s lower n) 6) (norm_nonneg _)
    _=(dilationPrice d)^6*((1+‖s • n‖)^6*‖test (s • n)‖):=by ring
    _≤(dilationPrice d)^6*decayPrice test:=mul_le_mul_of_nonneg_left (decay_bound test (s • n)) (by positivity)

/-- The generator differentiates the actual Schwartz observation and original physical Fourier phase. -/
def sourceDilationWeightDerivative (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum)
    (d : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourceSpatialPhase n (d • x)*
    ((SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test) (d • n) n+
      Complex.I*(phaseLinear x n:ℂ)*test (d • n))

private theorem dilation_weight_derivative (test : 𝓢(PhysicalMomentum,ℂ)) (x n : PhysicalMomentum) (d : ℝ) :
    HasDerivAt (fun s : ℝ=>sourceSpatialPhase n (s • x)*test (s • n))
      (sourceDilationWeightDerivative test x d n) d := by
  have argument : HasDerivAt (fun s : ℝ=>(s:ℂ)*(Complex.I*(phaseLinear x n:ℂ)))
      (Complex.I*(phaseLinear x n:ℂ)) d := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using
      ((Complex.ofRealCLM.hasFDerivAt (x:=d)).hasDerivAt.mul_const (Complex.I*(phaseLinear x n:ℂ)))
  have phase : HasDerivAt (fun s : ℝ=>sourceSpatialPhase n (s • x))
      (sourceSpatialPhase n (d • x)*(Complex.I*(phaseLinear x n:ℂ))) d := by
    simpa only [phase_scaled] using argument.cexp
  have prepare : HasDerivAt (fun s : ℝ=>test (s • n))
      ((SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test) (d • n) n) d := by
    have generated:=(test.hasFDerivAt (d • n)).comp_hasDerivAt d ((hasDerivAt_id d).smul_const n)
    simpa only [id_eq,one_smul,Function.comp_def,SchwartzMap.fderivCLM_apply] using generated
  convert! phase.mul prepare using 1
  simp only [sourceDilationWeightDerivative]
  ring

private def weightPrice (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) : ℝ :=
  (dilationPrice d)^6*(decayPrice (SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test)+‖phaseLinear x‖*decayPrice test)

private theorem weight_price_nonneg (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) :
    0≤ weightPrice test x d := by
  unfold weightPrice
  have f:=decay_price_nonneg test
  have df:=decay_price_nonneg (SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test)
  positivity

private theorem dilation_weight_bound (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum)
    (d : ℝ) (positive : 0<d) (s : ℝ) (lower : d/2≤ s) (n : PhysicalMomentum) :
    ‖sourceDilationWeightDerivative test x s n‖≤ weightPrice test x d*(1+‖n‖)/(1+‖n‖)^6 := by
  have value:=dilated_decay test d positive s lower n
  have derivative:=dilated_decay (SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test) d positive s lower n
  have phase:=(phaseLinear x).le_opNorm n
  have application:=((SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test) (s • n)).le_opNorm n
  have valueNonneg:=decay_price_nonneg test
  have derivativeNonneg:=decay_price_nonneg (SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test)
  rw [sourceDilationWeightDerivative,norm_mul,phase_norm,one_mul]
  calc
    _≤‖(SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test) (s • n) n‖+
      ‖Complex.I*(phaseLinear x n:ℂ)*test (s • n)‖:=norm_add_le _ _
    _≤((dilationPrice d)^6*decayPrice (SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test)/(1+‖n‖)^6)*‖n‖+
      (‖phaseLinear x‖*‖n‖)*((dilationPrice d)^6*decayPrice test/(1+‖n‖)^6) := by
      apply add_le_add
      · exact application.trans (mul_le_mul_of_nonneg_right derivative (norm_nonneg _))
      · simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real]
        exact mul_le_mul phase value (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _≤((dilationPrice d)^6*decayPrice (SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test)/(1+‖n‖)^6)*(1+‖n‖)+
      (‖phaseLinear x‖*(1+‖n‖))*((dilationPrice d)^6*decayPrice test/(1+‖n‖)^6) := by
      gcongr <;> linarith
    _=_:=by unfold weightPrice;ring

private def channelPrice (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex) (i : Fin 3) : ℝ :=
  sourceMasterChannelPrice q c eta l r i*(1+2*Real.pi)

private theorem channel_price_nonneg (q : PhysicalResponsePoint) (c eta : ℝ) (causal : 0<eta)
    (l r : RestStateIndex) (i : Fin 3) : 0≤ channelPrice q c eta l r i := by
  unfold channelPrice sourceMasterChannelPrice sourceMasterCurrentPrice sourceChargedDenominatorPrice
  positivity

private theorem channel_bound (q : PhysicalResponsePoint) (c eta : ℝ) (frequency : c≠0) (causal : 0<eta)
    (l r : RestStateIndex) (i : Fin 3) (n : PhysicalMomentum) :
    ‖sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i‖≤ channelPrice q c eta l r i*(1+‖n‖) := by
  have paid:=(paidDilationMaster% master_channel_bound) q (sourceSpatialMomentum n) c eta frequency causal l r i
  have sourcePrice : 0≤ sourceMasterChannelPrice q c eta l r i := by
    unfold sourceMasterChannelPrice sourceMasterCurrentPrice sourceChargedDenominatorPrice
    positivity
  have shape : 1+‖sourceSpatialMomentum n‖≤(1+2*Real.pi)*(1+‖n‖) := by
    simp only [sourceSpatialMomentum,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<2*Real.pi)]
    nlinarith [norm_nonneg n,Real.pi_pos]
  exact paid.trans ((mul_le_mul_of_nonneg_left shape sourcePrice).trans_eq (by unfold channelPrice;ring))

def sourceMasterDilationRead (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n (d • x)*test (d • n)*
    sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i

def sourceMasterDilationGenerator (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) : ℂ :=
  ∫n : PhysicalMomentum,sourceDilationWeightDerivative test x d n*
    sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i

private theorem dilation_generator_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) (positive : 0<d)
    (s : ℝ) (lower : d/2≤ s) (n : PhysicalMomentum) :
    ‖sourceDilationWeightDerivative test x s n*
      sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i‖≤
      (weightPrice test x d*channelPrice q c eta l r i)/(1+‖n‖)^4 := by
  rw [norm_mul]
  apply (mul_le_mul (dilation_weight_bound test x d positive s lower n)
    (channel_bound q c eta frequency causal l r i n) (norm_nonneg _) (by
      exact div_nonneg (mul_nonneg (weight_price_nonneg test x d) (by positivity)) (by positivity))).trans_eq
  field_simp

private theorem generator_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) :
    Continuous (fun n : PhysicalMomentum=>sourceDilationWeightDerivative test x d n*
      sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i) := by
  have momentum : Continuous sourceSpatialMomentum := by unfold sourceSpatialMomentum;fun_prop
  have kernel:=((paidDilationContinuity%) q c eta frequency causal l r i).comp momentum
  have gradient:=(SchwartzMap.fderivCLM ℝ PhysicalMomentum ℂ test).continuous
  have phase:=(phaseLinear x).continuous
  unfold sourceDilationWeightDerivative sourceSpatialPhase
  fun_prop

/-- The actual test gradient and physical phase pay the derivative of the complete fixed-side spatial master. -/
theorem sourceMasterDilationRead_derivative (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) (positive : 0<d) :
    HasDerivAt (sourceMasterDilationRead q c eta l r i test x)
      (sourceMasterDilationGenerator q c eta l r i test x d) d := by
  let neighborhood : Set ℝ:=Ioo (d/2) (3*d/2)
  have near : neighborhood∈𝓝 d:=Ioo_mem_nhds (by linarith) (by linarith)
  have majorant : Integrable (fun n : PhysicalMomentum=>(weightPrice test x d*channelPrice q c eta l r i)/(1+‖n‖)^4) := by
    have paid:=integrable_one_add_norm (μ:=volume) (E:=PhysicalMomentum) (r:=4) (by norm_num : (Module.finrank ℝ PhysicalMomentum:ℝ)<4)
    apply (paid.const_mul (weightPrice test x d*channelPrice q c eta l r i)).congr
    filter_upwards with n
    simp only [Real.rpow_neg (show 0≤1+‖n‖ by positivity),Real.rpow_ofNat,div_eq_mul_inv]
  have generated:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀:=d) (μ:=volume) (s:=neighborhood) near
    (F:=fun s n=>sourceSpatialPhase n (s • x)*test (s • n)*sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i)
    (F':=fun s n=>sourceDilationWeightDerivative test x s n*sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i)
    (bound:=fun n=>(weightPrice test x d*channelPrice q c eta l r i)/(1+‖n‖)^4)
    (by
      filter_upwards [near] with s hs
      have sp : 0<s:=by have h:=hs.1;linarith
      exact (sourceMasterDilation_integrable q c eta frequency causal s sp l r i test x).2.aestronglyMeasurable)
    (sourceMasterDilation_integrable q c eta frequency causal d positive l r i test x).2
    (generator_continuous q c eta frequency causal l r i test x d).aestronglyMeasurable
    (Eventually.of_forall (fun n s hs=>dilation_generator_bound q c eta frequency causal l r i test x d positive s hs.1.le n))
    majorant
    (Eventually.of_forall (fun n s _=>(dilation_weight_derivative test x n s).mul_const _))
  exact generated.2

private theorem side_radial_euler (d c eta : ℝ) :
    sourcePoleSide (d*c) (d*eta)=(d:ℂ)*sourcePoleSide c eta := by
  simp only [sourcePoleSide,Complex.ofReal_mul]
  ring

/-- The complete spatial master obeys the source Euler identity with the actual test and phase generator. -/
theorem sourceMasterSpatialChannel_euler (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) (positive : 0<d) :
    sourcePoleSide c eta*sourceMasterSpatialChannelDerivative q ((d:ℂ)*sourcePoleSide c eta) l r i test x=
      sourceMasterDilationRead q c eta l r i test x d+(d:ℂ)*sourceMasterDilationGenerator q c eta l r i test x d := by
  have cast : HasDerivAt (fun s : ℝ=>(s:ℂ)) (1:ℂ) d := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using! (Complex.ofRealCLM.hasFDerivAt (x:=d)).hasDerivAt
  have product:=cast.mul (sourceMasterDilationRead_derivative q c eta frequency causal l r i test x d positive)
  simp only [one_mul] at product
  have near : ∀ᶠ s : ℝ in 𝓝 d,0<s:=Ioi_mem_nhds positive
  have observed : HasDerivAt
      (fun s : ℝ=>sourceMasterSpatialChannel q ((s:ℂ)*sourcePoleSide c eta) l r i test x)
      (sourceMasterDilationRead q c eta l r i test x d+(d:ℂ)*sourceMasterDilationGenerator q c eta l r i test x d) d := by
    apply product.congr_of_eventuallyEq
    filter_upwards [near] with s sp
    have exactDilation:=sourceMasterSpatialChannel_dilation q c eta frequency causal s sp l r i test x
    rw [side_radial_euler] at exactDilation
    have same : sourceMasterSpatialChannel q (sourcePoleSide c eta) l r i (sourceDilatedTest s sp.ne' test) (s • x)=
        sourceMasterDilationRead q c eta l r i test x s := by
      unfold sourceMasterSpatialChannel sourceMasterDilationRead
      apply integral_congr_ae
      filter_upwards with n
      change sourceSpatialPhase n (s • x)*sourceDilatedTest s sp.ne' test n*
        sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i=_
      rw [sourceDilatedTest_apply]
    rw [same] at exactDilation
    exact exactDilation
  have native:=sourceMasterSpatialChannel_derivative q (d*c) (d*eta)
    (mul_ne_zero positive.ne' frequency) (mul_pos positive causal) l r i test x
  rw [side_radial_euler] at native
  have nativeReal:=native.scomp d (cast.mul_const (sourcePoleSide c eta))
  simp only [Function.comp_def,one_mul,smul_eq_mul] at nativeReal
  exact nativeReal.unique observed

/-- Every original channel response is returned by the same Euler generator and complete master correction. -/
theorem sourceCommonSpatialMoment_euler (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) (positive : 0<d) :
    sourcePoleSide c eta*sourceCommonSpatialMoment q (d*c) (d*eta) l r i 0 0 test x=
      sourceMasterDilationRead q c eta l r i test x d+(d:ℂ)*sourceMasterDilationGenerator q c eta l r i test x d+
        sourcePoleSide c eta*sourceMasterSpatialChannelCorrection q ((d:ℂ)*sourcePoleSide c eta) l r i test x := by
  rw [sourceCommonSpatialMoment_master q (d*c) (d*eta) (mul_ne_zero positive.ne' frequency) (mul_pos positive causal),
    side_radial_euler,mul_add,sourceMasterSpatialChannel_euler q c eta frequency causal l r i test x d positive]

def sourceDilationField (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceMasterDilationRead q c eta l r i test x d • sourceCommonOriginColumn i

def sourceDilationGeneratorField (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceMasterDilationGenerator q c eta l r i test x d • sourceCommonOriginColumn i

theorem sourceCommonSpatialField_euler (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) (positive : 0<d) :
    sourcePoleSide c eta • sourceCommonSpatialField q (d*c) (d*eta) l r test x=
      sourceDilationField q c eta l r test x d+(d:ℂ) • sourceDilationGeneratorField q c eta l r test x d+
        sourcePoleSide c eta • sourceMasterSpatialFieldCorrection q ((d:ℂ)*sourcePoleSide c eta) l r test x := by
  rw [sourceCommonSpatialField_generated q (d*c) (d*eta) (mul_ne_zero positive.ne' frequency) (mul_pos positive causal)]
  simp only [sourceDilationField,sourceDilationGeneratorField,sourceMasterSpatialFieldCorrection,
    Finset.smul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_smul,←add_smul]
  congr 1
  exact sourceCommonSpatialMoment_euler q c eta frequency causal l r i test x d positive

def sourceActualDilationField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (c eta : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceDilationField q c eta l r test x d

def sourceActualDilationGenerator (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (c eta : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (d : ℝ) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceDilationGeneratorField q c eta l r test x d

/-- Actual source64 carries the same complete full289 spatial Euler response. -/
theorem sourceActualSpatialField_euler (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (c eta : ℝ)
    (frequency : c≠0) (causal : 0<eta) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum)
    (d : ℝ) (positive : 0<d) :
    sourcePoleSide c eta • sourceActualSpatialField q sL eL sR eR (d*c) (d*eta) test x=
      sourceActualDilationField q sL eL sR eR c eta test x d+
        (d:ℂ) • sourceActualDilationGenerator q sL eL sR eR c eta test x d+
          sourcePoleSide c eta • sourceActualMasterSpatialCorrection q sL eL sR eR ((d:ℂ)*sourcePoleSide c eta) test x := by
  rw [sourceActualSpatialField_generated q sL eL sR eR (d*c) (d*eta)
    (mul_ne_zero positive.ne' frequency) (mul_pos positive causal)]
  simp only [sourceActualDilationField,sourceActualDilationGenerator,sourceActualMasterSpatialCorrection,
    Finset.smul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  let weight:=sourceActualPreparedWeight 0 0 sL eL sR eR l r
  have paid:=congrArg (fun V : Fin 289→ℂ=>weight • V)
    (sourceCommonSpatialField_euler q c eta frequency causal l r test x d positive)
  simpa only [smul_add,smul_smul,mul_comm weight (sourcePoleSide c eta),mul_comm weight (d:ℂ)] using paid

open PreparationPhysicalActualLegNormalization

private theorem unit_read_smul (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (T : ℝ)
    (left : q.z.im≠0) (right : q.w.im≠0) (z : ℂ) (V : Fin 289→ℂ) :
    sourceActualUnitFieldRead q sL eL sR eR 0 T (z • V)=z*sourceActualUnitFieldRead q sL eL sR eR 0 T V := by
  simp only [(paidMasterUnit%) q sL eL sR eR 0 T left right,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

private theorem unit_read_add (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (T : ℝ)
    (left : q.z.im≠0) (right : q.w.im≠0) (V W : Fin 289→ℂ) :
    sourceActualUnitFieldRead q sL eL sR eR 0 T (V+W)=
      sourceActualUnitFieldRead q sL eL sR eR 0 T V+sourceActualUnitFieldRead q sL eL sR eR 0 T W := by
  simp only [(paidMasterUnit%) q sL eL sR eR 0 T left right,Pi.add_apply,add_mul,Finset.sum_add_distrib]

/-- The existing actual radial potential, read by the independently normalized detector, is generated by the true observation dilation and complete source correction. -/
theorem sourceActualUnitRadialPotential_euler (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (d : ℝ) (positive : 0<d)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourcePoleSide (sourceSignedSpeed branch negative) eta*
      sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
        (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)=
      sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
        (sourceActualDilationField q sL eL sR eR (sourceSignedSpeed branch negative) eta test x d)+
      (d:ℂ)*sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
        (sourceActualDilationGenerator q sL eL sR eR (sourceSignedSpeed branch negative) eta test x d)+
      sourcePoleSide (sourceSignedSpeed branch negative) eta*
        sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
          (sourceActualMasterSpatialCorrection q sL eL sR eR
            ((d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) test x) := by
  have paid:=congrArg (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T)
    (sourceActualSpatialField_euler q sL eL sR eR (sourceSignedSpeed branch negative) eta
      (sourceSignedSpeed_nonzero branch negative) causal test x d positive)
  rw [←sourceActualRadialPotential_return q sL eL sR eR branch negative eta causal d positive test x] at paid
  simpa only [unit_read_smul qd dSL dEL dSR dER T left right,unit_read_add qd dSL dEL dSR dER T left right] using paid

end LowEnergy.PreparationPhysicalCausalSpatialDilation
