import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelFundamentalPotential
import Mathlib.Analysis.Calculus.DSlope

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
local instance ChannelRadialIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

private def gaussianDeficit (kappa : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-kappa*(t:ℂ)^2)-1)/(t:ℂ)^2

private def deficitExtension (kappa : ℂ) (t : ℝ) : ℂ :=
  -kappa*dslope Complex.exp 0 (-kappa*(t:ℂ)^2)

private theorem deficitExtension_continuous (kappa : ℂ) : Continuous (deficitExtension kappa) := by
  have slopeContinuous : Continuous (dslope Complex.exp 0) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases zero : z=0
    · subst z
      exact continuousAt_dslope_same.mpr (Complex.differentiable_exp 0)
    · exact (continuousAt_dslope_of_ne zero).mpr Complex.continuous_exp.continuousAt
  exact continuous_const.mul (slopeContinuous.comp (by fun_prop))

private theorem deficitExtension_return (kappa : ℂ) (nonzero : kappa≠0) (t : ℝ) (tnz : t≠0) :
    deficitExtension kappa t=gaussianDeficit kappa t := by
  have castNZ : (t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr tnz
  have inputNZ : -kappa*(t:ℂ)^2≠0:=mul_ne_zero (neg_ne_zero.mpr nonzero) (pow_ne_zero _ castNZ)
  rw [deficitExtension,dslope_of_ne _ inputNZ,slope_def_field]
  simp only [sub_zero,Complex.exp_zero,gaussianDeficit]
  field_simp

private theorem gaussian_norm_le (kappa : ℂ) (positive : 0<kappa.re) (t : ℝ) :
    ‖Complex.exp (-kappa*(t:ℂ)^2)‖≤1 := by
  rw [Complex.norm_exp,←Real.exp_zero]
  apply Real.exp_le_exp.mpr
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr positive.le) (sq_nonneg t)

private theorem deficit_bound (kappa : ℂ) (positive : 0<kappa.re) (t : ℝ) :
    ‖gaussianDeficit kappa t‖≤2*(t^2)⁻¹ := by
  have numerator : ‖Complex.exp (-kappa*(t:ℂ)^2)-1‖≤2 := by
    calc
      _≤‖Complex.exp (-kappa*(t:ℂ)^2)‖+‖(1:ℂ)‖:=norm_sub_le _ _
      _≤2 := by simp only [norm_one];linarith [gaussian_norm_le kappa positive t]
  simp only [gaussianDeficit,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right numerator (sq_nonneg t)

private theorem deficit_integrable (kappa : ℂ) (positive : 0<kappa.re) :
    IntegrableOn (gaussianDeficit kappa) (Ioi 0) := by
  have nonzero : kappa≠0 := by intro zero;rw [zero,Complex.zero_re] at positive;exact lt_irrefl _ positive
  have near : IntegrableOn (gaussianDeficit kappa) (Ioc 0 1) := by
    apply ((deficitExtension_continuous kappa).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
      (fun t ht=>deficitExtension_return kappa nonzero t ht.1.ne') measurableSet_Ioc
  have tail : IntegrableOn (gaussianDeficit kappa) (Ioi 1) := by
    have price:=(integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (by norm_num : (0:ℝ)<1)).const_mul 2
    have measurable : Measurable (gaussianDeficit kappa) := by unfold gaussianDeficit;fun_prop
    apply price.mono' measurable.aestronglyMeasurable
    filter_upwards with t
    simpa only [Real.rpow_neg_eq_inv_rpow,Real.rpow_ofNat,inv_pow] using deficit_bound kappa positive t
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)] using near.union tail

private theorem deficit_integral (kappa : ℂ) (positive : 0<kappa.re) :
    (∫t : ℝ in Ioi 0,gaussianDeficit kappa t)=
      -kappa*((Real.pi:ℂ)/kappa)^(1/2:ℂ) := by
  have nonzero : kappa≠0 := by intro zero;rw [zero,Complex.zero_re] at positive;exact lt_irrefl _ positive
  let u : ℝ→ℂ:=fun t=>(t:ℂ)⁻¹
  let v : ℝ→ℂ:=fun t=>Complex.exp (-kappa*(t:ℂ)^2)-1
  let u' : ℝ→ℂ:=fun t=>-(t:ℂ)⁻¹^2
  let v' : ℝ→ℂ:=fun t=>(-2*kappa*(t:ℂ))*Complex.exp (-kappa*(t:ℂ)^2)
  have du (t : ℝ) (ht : t∈Ioi (0:ℝ)) : HasDerivAt u (u' t) t := by
    have h:=(Complex.ofRealCLM.hasFDerivAt (x:=t)).hasDerivAt.inv (Complex.ofReal_ne_zero.mpr ht.ne')
    convert! h using 1
    norm_num [u,u',Complex.ofRealCLM,div_eq_mul_inv,inv_pow]
  have dv (t : ℝ) (_ht : t∈Ioi (0:ℝ)) : HasDerivAt v (v' t) t := by
    have cast:=(Complex.ofRealCLM.hasFDerivAt (x:=t)).hasDerivAt
    have h:=((cast.pow 2).const_mul (-kappa)).cexp.sub_const 1
    convert! h using 1
    norm_num [v,v',Complex.ofRealCLM]
    ring
  have leftPoint (t : ℝ) : u' t*v t= -gaussianDeficit kappa t := by
    unfold u' v gaussianDeficit
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have rightPoint (t : ℝ) (ht : t∈Ioi (0:ℝ)) :
      u t*v' t=(-2*kappa)*Complex.exp (-kappa*(t:ℂ)^2) := by
    dsimp only [u,v']
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  have leftIntegral : IntegrableOn (fun t=>u' t*v t) (Ioi 0) := by
    apply ((deficit_integrable kappa positive).const_mul (-1:ℂ)).congr
    filter_upwards with t
    rw [leftPoint]
    ring
  have rightIntegral : IntegrableOn (fun t=>u t*v' t) (Ioi 0) := by
    apply ((integrable_cexp_neg_mul_sq positive).integrableOn.const_mul (-2*kappa)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (rightPoint t ht).symm
  have zero : Tendsto (u*v) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have generated : Tendsto (fun t : ℝ=>(t:ℂ)*deficitExtension kappa t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have paid:=((Complex.continuous_ofReal.mul (deficitExtension_continuous kappa)).continuousAt (x:=0)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
      simp only [Pi.mul_apply,Complex.ofReal_zero,zero_mul] at paid
      apply paid.congr
      intro t
      rfl
    apply generated.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [deficitExtension_return kappa nonzero t ht.ne']
    dsimp only [Pi.mul_apply,u,v,gaussianDeficit]
    field_simp
  have infinity : Tendsto (u*v) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun t=>norm_nonneg ((u*v) t))) _
      (by simpa using (tendsto_inv_atTop_zero.const_mul (2:ℝ)))
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have numerator : ‖v t‖≤2 := by
      calc
        _≤‖Complex.exp (-kappa*(t:ℂ)^2)‖+‖(1:ℂ)‖:=norm_sub_le _ _
        _≤2 := by simp only [norm_one];linarith [gaussian_norm_le kappa positive t]
    simp only [Pi.mul_apply,u,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    nlinarith [mul_le_mul_of_nonneg_left numerator (inv_nonneg.mpr ht.le)]
  have boundary:=integral_Ioi_deriv_mul_eq_sub du dv (leftIntegral.add rightIntegral) zero infinity
  rw [integral_add leftIntegral rightIntegral] at boundary
  simp_rw [leftPoint] at boundary
  rw [integral_neg] at boundary
  have right : (∫t : ℝ in Ioi 0,u t*v' t)=
      (-2*kappa)*(((Real.pi:ℂ)/kappa)^(1/2:ℂ)/2) := by
    calc
      _=∫t : ℝ in Ioi 0,(-2*kappa)*Complex.exp (-kappa*(t:ℂ)^2) :=
        setIntegral_congr_fun measurableSet_Ioi rightPoint
      _=_ := by rw [integral_const_mul,integral_gaussian_complex_Ioi positive]
  rw [right] at boundary
  linear_combination -boundary

/-- The source mass pays the complete complex Gaussian boundary layer, including its nonzero integral. -/
theorem sourceChannelDeficit_integrable (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) :
    IntegrableOn (fun t : ℝ=>(Complex.exp (-sourceChannelMass branch negative eta i*(t:ℂ)^2)-1)/(t:ℂ)^2) (Ioi 0) :=
  deficit_integrable _ (sourceChannelMass_positive branch negative eta positive i)

theorem sourceChannelDeficit_integral (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (i : Fin 3) :
    (∫t : ℝ in Ioi 0,(Complex.exp (-sourceChannelMass branch negative eta i*(t:ℂ)^2)-1)/(t:ℂ)^2)=
      -sourceChannelMass branch negative eta i*((Real.pi:ℂ)/sourceChannelMass branch negative eta i)^(1/2:ℂ) :=
  deficit_integral _ (sourceChannelMass_positive branch negative eta positive i)

end LowEnergy.PreparationPhysicalChannelRadialJet
