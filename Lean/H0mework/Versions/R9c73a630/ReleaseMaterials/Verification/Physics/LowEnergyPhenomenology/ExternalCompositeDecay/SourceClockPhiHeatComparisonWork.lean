import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiConservativeHeatSource
import Mathlib.Analysis.Convex.Mul
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatComparisonJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatComparisonPrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForwardDriftTransport
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiComparisonNativeClosedGraph
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeSignedWorkIntegrable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiHeatComparisonWork
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare ClockPhiMatchedNoiseCore SourceClockPhiCoframeForwardCore
open ClockPhiConservativeHeatSource SourceClockPhiCombinedScalePressure MeasureTheory Set Filter
open scoped ContDiff Topology Distributions InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private def heatInput(t:ℝ)(ht:0<t)(ξ:ℝ):End:=
  (show {N:End // sourceForwardCore t ht.le*N=sourceHeatCore t ht ξ} from ⟨_,rfl⟩).val
private theorem heatInput_source(t:ℝ)(ht:0<t)(ξ:ℝ):
    sourceForwardCore t ht.le*heatInput t ht ξ=sourceHeatCore t ht ξ:=rfl
private theorem heatInput_point(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    heatInput t ht ξ f z=(Real.exp ((25/2:ℝ)*(heatMean t z+Real.sqrt (heatVariance t z)*ξ)):ℂ) •
      f (combinedMap (heatMean t z+Real.sqrt (heatVariance t z)*ξ) z):=by
  change (Real.exp ((25/2:ℝ)*(1*(heatMean t z+Real.sqrt (heatVariance t z)*ξ))):ℂ) •
    f (combinedMap (1*(heatMean t z+Real.sqrt (heatVariance t z)*ξ)) z)=_
  simp only [one_mul]
private theorem actual_heat_forward_point(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    sourceHeatCore t ht ξ f (forwardPoint t z.val) word=
      (Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*
      ((Real.exp ((25/2:ℝ)*(heatMean t z.val+Real.sqrt (heatVariance t z.val)*ξ)):ℂ)*
        f (combinedMap (heatMean t z.val+Real.sqrt (heatVariance t z.val)*ξ) z.val) word):=by
  unfold sourceHeatCore
  rw [Module.End.mul_apply,forwardCore_apply]
  change (Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*
      ((Real.exp ((25/2:ℝ)*(1*(heatMean t z.val+Real.sqrt (heatVariance t z.val)*ξ))):ℂ)*
        f (combinedMap (1*(heatMean t z.val+Real.sqrt (heatVariance t z.val)*ξ)) z.val) word)=_
  simp only [one_mul]

private theorem gaussian_norm_square (F:ℝ→H)(hi:Integrable F γ)
    (h2:Integrable (fun ξ=>‖F ξ‖^2) γ):
    ‖∫ξ,F ξ ∂γ‖^2≤∫ξ,‖F ξ‖^2 ∂γ:=by
  have hc:ConvexOn ℝ (univ:Set H) (fun x:H=>‖x‖^2):=
    convexOn_univ_norm.pow (fun _ _=>norm_nonneg _) 2
  exact hc.map_integral_le (by fun_prop) isClosed_univ (Eventually.of_forall (fun _=>mem_univ _)) hi h2
private theorem gaussian_shift_square(a b:H):
    Integrable (fun ξ:ℝ=>‖a-(ξ:ℂ) • b‖^2) γ ∧
      (∫ξ:ℝ,‖a-(ξ:ℂ) • b‖^2 ∂γ)=‖a‖^2+‖b‖^2:=by
  have h1:Integrable (fun ξ:ℝ=>ξ) γ:=
    (ProbabilityTheory.memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  have h2:Integrable (fun ξ:ℝ=>ξ^2) γ:=
    (ProbabilityTheory.memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  have he(ξ:ℝ):‖a-(ξ:ℂ) • b‖^2=‖a‖^2-(2*(inner ℂ a b).re)*ξ+‖b‖^2*ξ^2:=by
    rw [norm_sub_sq (𝕜:=ℂ)]
    simp only [inner_smul_right,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    change ‖a‖^2-2*((ξ:ℂ)*inner ℂ a b).re+ξ^2*‖b‖^2=_
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hc:Integrable (fun ξ:ℝ=>‖a‖^2-(2*(inner ℂ a b).re)*ξ+‖b‖^2*ξ^2) γ:=
    ((integrable_const _).sub (h1.const_mul _)).add (h2.const_mul _)
  refine ⟨hc.congr (Eventually.of_forall (fun ξ=>(he ξ).symm)),?_⟩
  simp_rw [he]
  have hc0:Integrable (fun _:ℝ=>‖a‖^2) γ:=integrable_const _
  have hc1:Integrable (fun ξ:ℝ=>(2*(inner ℂ a b).re)*ξ) γ:=h1.const_mul _
  have hc2:Integrable (fun ξ:ℝ=>‖b‖^2*ξ^2) γ:=h2.const_mul _
  calc
    _=(∫ξ:ℝ,‖a‖^2-(2*(inner ℂ a b).re)*ξ ∂γ)+(∫ξ:ℝ,‖b‖^2*ξ^2 ∂γ):=
      integral_add (hc0.sub hc1) hc2
    _=(∫_:ℝ,‖a‖^2 ∂γ)-(∫ξ:ℝ,(2*(inner ℂ a b).re)*ξ ∂γ)+
        (∫ξ:ℝ,‖b‖^2*ξ^2 ∂γ):=by rw [integral_sub hc0 hc1]
    _=_:=by
      rw [integral_const_mul,integral_const_mul,ProbabilityTheory.integral_id_gaussianReal,
        SourceClockPhiGaussianComplexIBP.standard_gaussian_square_moment]
      simp only [integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul,mul_zero,sub_zero]

private theorem gaussian_shifted_column
    (K:ℝ→QuantumTest→ₗ[ℂ]H)
    (hI:∀ξ f,‖K ξ f‖=‖embed f‖)
    (hK:∀f,Integrable (fun ξ=>K ξ f) γ)
    (hW:∀f,Integrable (fun ξ:ℝ=>(ξ:ℂ) • K ξ f) γ)
    (f g:QuantumTest):
    ‖(∫ξ,K ξ f ∂γ)-(∫ξ:ℝ,(ξ:ℂ) • K ξ g ∂γ)‖^2≤‖embed f‖^2+‖embed g‖^2:=by
  let F:ℝ→H:=fun ξ=>K ξ f-(ξ:ℂ) • K ξ g
  have hn(ξ:ℝ):‖F ξ‖^2=‖embed f-(ξ:ℂ) • embed g‖^2:=by
    have he:K ξ f-(ξ:ℂ) • K ξ g=K ξ (f-(ξ:ℂ) • g):=by simp only [map_sub,map_smul]
    dsimp only [F]
    rw [he,hI,map_sub,map_smul]
  have hi:Integrable F γ:=(hK f).sub (hW g)
  have h2:Integrable (fun ξ=>‖F ξ‖^2) γ:=
    (gaussian_shift_square (embed f) (embed g)).1.congr (Eventually.of_forall (fun ξ=>(hn ξ).symm))
  have h:=gaussian_norm_square F hi h2
  have hF:(∫ξ,F ξ ∂γ)=(∫ξ,K ξ f ∂γ)-(∫ξ:ℝ,(ξ:ℂ) • K ξ g ∂γ):=integral_sub (hK f) (hW g)
  have hN:(∫ξ,‖F ξ‖^2 ∂γ)=‖embed f‖^2+‖embed g‖^2:=
    (integral_congr_ae (Eventually.of_forall hn)).trans (gaussian_shift_square (embed f) (embed g)).2
  rw [hF,hN] at h
  exact h
private theorem gaussian_source_columns
    (K:ℝ→QuantumTest→ₗ[ℂ]H)
    (hI:∀ξ f,‖K ξ f‖=‖embed f‖)
    (hK:∀f,Integrable (fun ξ=>K ξ f) γ)
    (hW:∀f,Integrable (fun ξ:ℝ=>(ξ:ℂ) • K ξ f) γ)
    (f g h:QuantumTest):
    ‖(∫ξ,K ξ f ∂γ)-(∫ξ:ℝ,(ξ:ℂ) • K ξ g ∂γ)‖^2+
      (1/2:ℝ)*‖∫ξ,K ξ h ∂γ‖^2≤‖embed f‖^2+‖embed g‖^2+(1/2:ℝ)*‖embed h‖^2:=by
  have h1:=gaussian_shifted_column K hI hK hW f g
  have h0:=gaussian_shifted_column K hI hK hW h 0
  simp only [map_zero,smul_zero,integral_zero,sub_zero,norm_zero] at h0
  linarith

open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent SourceClockPhiForwardNativeReturn SourceScalarVirialBulk
private def heatCoefficient(t ξ:ℝ)(z:SourceCoordinateSlice):ℝ:=
  heatMean t z+Real.sqrt (heatVariance t z)*ξ
def heatKappa(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  (reciprocalVolume z-forwardU t z)/Real.sqrt (heatLog t z)
private def heatDelta(t ξ:ℝ)(z:SourceCoordinateSlice):ℝ:=
  reciprocalVolume z-forwardU t z-heatKappa t z*ξ
private theorem volume_euler_jet(z:SourceCoordinateSlice):
    HasDerivAt (fun s:ℝ=>GaussNativeEnergy.volume (z+s • euler z))
      (3*GaussNativeEnergy.volume z) 0:=by
  have he(s:ℝ):z+s • euler z=scale (1+s) z:=by
    apply Prod.ext
    · change z.1+s • z.1=(1+s) • z.1
      module
    · change z.2+s • 0=z.2
      simp only [smul_zero,add_zero]
  have h:=(((hasDerivAt_id (0:ℝ)).const_add 1).pow 3).mul_const (GaussNativeEnergy.volume z)
  simpa only [he,volume_scale,Pi.pow_apply,Pi.add_apply,id_eq,add_zero,one_pow,Nat.cast_ofNat,mul_one,one_mul] using h
private theorem coefficient_euler_jet(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart):
    HasDerivAt (fun s:ℝ=>heatCoefficient t ξ (z.val+s • euler z.val))
      ((GaussNativeEnergy.volume z.val/2)*heatDelta t ξ z.val) 0:=by
  have h:=(SourceClockPhiHeatComparisonJet.clock_noise_parameter_derivative
    (GaussNativeEnergy.volume z.val) t ξ (volume_pos z) ht).comp_of_eq (0:ℝ)
      (volume_euler_jet z.val) (by simp)
  have he(s:ℝ):ξ*Real.sqrt (Real.log (1+18*t/GaussNativeEnergy.volume (z.val+s • euler z.val))/9)-
      Real.log (1+18*t/GaussNativeEnergy.volume (z.val+s • euler z.val))/6=
      heatCoefficient t ξ (z.val+s • euler z.val):=by
    unfold heatCoefficient heatMean heatVariance heatLog reciprocalVolume
    rw [div_eq_mul_inv (18*t)]
    ring
  have hd:(((1/GaussNativeEnergy.volume z.val-1/(GaussNativeEnergy.volume z.val+18*t))-
      ((1/GaussNativeEnergy.volume z.val-1/(GaussNativeEnergy.volume z.val+18*t))/
        Real.sqrt (Real.log (1+18*t/GaussNativeEnergy.volume z.val)))*ξ)/6)*
        (3*GaussNativeEnergy.volume z.val)=(GaussNativeEnergy.volume z.val/2)*heatDelta t ξ z.val:=by
    unfold heatDelta heatKappa heatLog forwardU reciprocalVolume
    rw [div_eq_mul_inv (18*t)]
    simp only [one_div]
    ring
  simpa only [Function.comp_def,he,hd] using h
private def inputMap(t ξ:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  combinedMap (heatCoefficient t ξ z) z
private theorem inputMap_euler_jet(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart):
    HasDerivAt (fun s:ℝ=>inputMap t ξ (z.val+s • euler z.val))
      (euler z.val+((GaussNativeEnergy.volume z.val/2)*heatDelta t ξ z.val) •
        (SourceScalarVirialBulk.phiEuler (inputMap t ξ z.val)-SourceGaugeRadialCurrent.gaugeEuler (inputMap t ξ z.val))) 0:=by
  let c:=heatCoefficient t ξ z.val
  let dc:=(GaussNativeEnergy.volume z.val/2)*heatDelta t ξ z.val
  have hc:=coefficient_euler_jet t ht ξ z
  have he:=hc.exp
  have hn:=hc.neg.exp
  have hco:HasDerivAt (fun s:ℝ=>z.val.1+s • z.val.1) z.val.1 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const z.val.1).const_add z.val.1
  have h:=hco.prodMk (((he.smul_const (z.val.2.1+vacuumSlice)).sub_const vacuumSlice).prodMk
    (hn.smul_const z.val.2.2))
  have hp:heatCoefficient t ξ (z.val+(0:ℝ) • euler z.val)=c:=by simp [c]
  simp only [Pi.neg_apply,hp] at h
  have hd:(z.val.1,(Real.exp c*dc) • (z.val.2.1+vacuumSlice),(Real.exp (-c)*(-dc)) • z.val.2.2)=
      euler z.val+dc • (SourceScalarVirialBulk.phiEuler (inputMap t ξ z.val)-
        SourceGaugeRadialCurrent.gaugeEuler (inputMap t ξ z.val)):=by
    simp only [inputMap,combinedMap_apply,SourceScalarVirialBulk.phiEuler,SourceGaugeRadialCurrent.gaugeEuler,euler]
    apply Prod.ext
    · simp
    apply Prod.ext
    · change (Real.exp c*dc) • (z.val.2.1+vacuumSlice)=
        0+dc • (vacuumSlice+(Real.exp c • (z.val.2.1+vacuumSlice)-vacuumSlice)-0)
      module
    · change (Real.exp (-c)*(-dc)) • z.val.2.2=0+dc • (0-Real.exp (-c) • z.val.2.2)
      module
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  exact Eventually.of_forall (fun s=>by
    simp only [inputMap,combinedMap_apply,euler,Prod.fst_add,Prod.snd_add,Prod.smul_mk,smul_zero,add_zero])

private theorem component_fderiv(f:QuantumTest)(z v:SourceCoordinateSlice)(word:Occupation):
    fderiv ℝ f z v word=fderiv ℝ (component word f) z v:=by
  have h:=congrArg (fun g:GaussDensityCore.ScalarTest=>g z) (GaussCoframeCore.component_derivative v f word)
  change GaussCoframeCore.derivative v f z word=GaussDensityCore.derivative v (component word f) z at h
  simpa only [GaussCoframeCore.derivative_apply,GaussDensityCore.derivative_apply] using h
private theorem combined_component(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    combinedGenerator f z word=fderiv ℝ (component word f) z
      (SourceScalarVirialBulk.phiEuler z-SourceGaugeRadialCurrent.gaugeEuler z)+(25/2:ℂ)*f z word:=by
  have h:=congrArg (fun v:FockFiber=>v word) (combined_generator_point f z)
  simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,component_fderiv] using h
private theorem input_euler_derivative(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    fderiv ℝ (component word (heatInput t ht ξ f)) z.val (euler z.val)=
      (Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*
        (fderiv ℝ (component word f) (inputMap t ξ z.val) (euler z.val)+
          ((GaussNativeEnergy.volume z.val/2)*heatDelta t ξ z.val:ℝ)*
            combinedGenerator f (inputMap t ξ z.val) word):=by
  have hc:=coefficient_euler_jet t ht ξ z
  have hx:=inputMap_euler_jet t ht ξ z
  have hz:HasDerivAt (fun s:ℝ=>z.val+s • euler z.val) (euler z.val) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (euler z.val)).const_add z.val
  have hf:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=inputMap t ξ z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hl:=(((component word (heatInput t ht ξ f)).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hz (by simp)
  have he0:=(hc.const_mul (25/2:ℝ)).exp
  have he:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) he0
  have hh:=he.mul hf
  have heq:(fun s:ℝ=>(Real.exp ((25/2:ℝ)*heatCoefficient t ξ (z.val+s • euler z.val)):ℂ)*
      f (inputMap t ξ (z.val+s • euler z.val)) word)=
      fun s:ℝ=>heatInput t ht ξ f (z.val+s • euler z.val) word:=by
    funext s
    rw [heatInput_point]
    rfl
  have hcomp(q:QuantumTest)(x:SourceCoordinateSlice):(component word q) x=q x word:=rfl
  dsimp only [Function.comp_def,Complex.ofRealCLM_apply,Pi.mul_apply] at hh hl
  simp only [hcomp] at hh hl
  change HasDerivAt (fun s:ℝ=>(Real.exp ((25/2:ℝ)*heatCoefficient t ξ (z.val+s • euler z.val)):ℂ)*
    f (inputMap t ξ (z.val+s • euler z.val)) word) _ 0 at hh
  rw [heq] at hh
  have h:=hl.unique hh
  rw [h,combined_component]
  simp only [zero_smul,add_zero,map_add,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.ofReal_eq_complex_ofReal,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

private theorem heat_log_pos(t:ℝ)(ht:0<t)(z:physicalChart):0<heatLog t z.val:=by
  apply Real.log_pos
  have hu:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
  change 1<1+18*t*reciprocalVolume z.val
  have hp:0<18*t*reciprocalVolume z.val:=by positivity
  linarith
private theorem heat_log_smooth(t:ℝ)(ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (heatLog t) z.val:=by
  apply (contDiffAt_const.add ((contDiffAt_const.mul contDiffAt_const).mul (reciprocal_volume_smooth z))).log
  have hu:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
  positivity
private theorem kappa_smooth(t:ℝ)(ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (heatKappa t) z.val:=
  ((reciprocal_volume_smooth z).sub (forwardU_smooth t ht.le z)).div
    ((heat_log_smooth t ht z).sqrt (heat_log_pos t ht z).ne')
    (Real.sqrt_pos.mpr (heat_log_pos t ht z)).ne'
private theorem delta_smooth(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (heatDelta t ξ) z.val:=
  ((reciprocal_volume_smooth z).sub (forwardU_smooth t ht.le z)).sub
    ((kappa_smooth t ht z).mul contDiffAt_const)
def kappaAction(t:ℝ)(ht:0<t):End:=multiply (heatKappa t) (kappa_smooth t ht)
private def deltaAction(t:ℝ)(ht:0<t)(ξ:ℝ):End:=multiply (heatDelta t ξ) (delta_smooth t ht ξ)
private theorem source_comparison_coefficient(t:ℝ)(ht:0<t)(z:physicalChart):
    heatKappa t z.val^2+(1/2:ℝ)*(forwardU t z.val)^2≤(1/2:ℝ)*(reciprocalVolume z.val)^2:=by
  have h:=SourceClockPhiHeatComparisonPrice.clock_comparison_price
    (GaussNativeEnergy.volume z.val) t (volume_pos z) ht
  have he:1+18*t*reciprocalVolume z.val=
      (GaussNativeEnergy.volume z.val+18*t)/GaussNativeEnergy.volume z.val:=by
    unfold reciprocalVolume
    field_simp [(volume_pos z).ne']
  dsimp only [heatKappa,heatLog,forwardU]
  rw [he]
  simpa only [reciprocalVolume,one_div] using h
private theorem multiplier_density(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest)(z:SourceCoordinateSlice):
    (densityPair (multiply c hc f) (multiply c hc f) z).re=c z^2*(densityPair f f z).re:=by
  change (inner ℂ (GaussFockWeights.weight (fun N=>GaussDensityCore.complexDensity N z)
    ((c z:ℂ) • f z)) ((c z:ℂ) • f z)).re=_
  rw [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  change ((c z:ℂ)*((c z:ℂ)*densityPair f f z)).re=_
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring
private theorem density_positive(f:QuantumTest)(z:physicalChart):0≤(densityPair f f z.val).re:=by
  have h: (densityPair f f z.val).re=
      ‖GaussBoundedMultiplier.halfWeight (fun N=>GaussDensityCore.density N z.val) (f z.val)‖^2:=by
    change RCLike.re (inner ℂ (GaussFockWeights.weight
      (fun N=>(GaussDensityCore.density N z.val:ℂ)) (f z.val)) (f z.val))=_
    exact GaussBoundedMultiplier.weighted_square _ (fun N=>(GaussDensityCore.density_pos N z).le) _
  rw [h];positivity
private theorem actual_coefficient_columns(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖embed (kappaAction t ht f)‖^2+(1/2:ℝ)*‖embed (forwardUAction t ht.le f)‖^2≤
      (1/2:ℝ)*‖embed (inverseVolumeAction f)‖^2:=by
  have hp(z:SourceCoordinateSlice):
      (densityPair (kappaAction t ht f) (kappaAction t ht f) z).re+
        (1/2:ℝ)*(densityPair (forwardUAction t ht.le f) (forwardUAction t ht.le f) z).re≤
        (1/2:ℝ)*(densityPair (inverseVolumeAction f) (inverseVolumeAction f) z).re:=by
    change (densityPair (multiply (heatKappa t) _ f) (multiply (heatKappa t) _ f) z).re+
      (1/2:ℝ)*(densityPair (multiply (forwardU t) _ f) (multiply (forwardU t) _ f) z).re≤
      (1/2:ℝ)*(densityPair (multiply reciprocalVolume _ f) (multiply reciprocalVolume _ f) z).re
    rw [multiplier_density,multiplier_density,multiplier_density]
    by_cases hz:z∈physicalChart
    · have h:=mul_le_mul_of_nonneg_right (source_comparison_coefficient t ht ⟨z,hz⟩) (density_positive f ⟨z,hz⟩)
      nlinarith only [h]
    · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
      simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,mul_zero,add_zero,le_refl]
  have hκ:Integrable (fun z=>(densityPair (kappaAction t ht f) (kappaAction t ht f) z).re)
      GaussHistoryHilbert.configurationMeasure:=(densityPair_integrable _ _).re
  have hu:Integrable (fun z=>(densityPair (forwardUAction t ht.le f) (forwardUAction t ht.le f) z).re)
      GaussHistoryHilbert.configurationMeasure:=(densityPair_integrable _ _).re
  have hU:Integrable (fun z=>(densityPair (inverseVolumeAction f) (inverseVolumeAction f) z).re)
      GaussHistoryHilbert.configurationMeasure:=(densityPair_integrable _ _).re
  have h:=integral_mono (hκ.add (hu.const_mul (1/2:ℝ))) (hU.const_mul (1/2:ℝ)) hp
  simp only [Pi.add_apply] at h
  rw [integral_add hκ (hu.const_mul (1/2:ℝ)),integral_const_mul,integral_const_mul] at h
  have hn(q:QuantumTest):‖embed q‖^2=(∫z,(densityPair q q z).re ∂GaussHistoryHilbert.configurationMeasure):=
    GaussBoundedMultiplier.norm_square_integral q
  rw [←hn,←hn,←hn] at h
  exact h
private theorem inputMap_chart(t ξ:ℝ)(z:physicalChart):inputMap t ξ z.val∈physicalChart:=
  ((SourceGaugeScaleTransport.scale_chart_iff (Real.exp (-heatCoefficient t ξ z.val)) (Real.exp_pos _)
    (SourceScalarAffineScaleTransport.scaleEquiv (heatCoefficient t ξ z.val) z.val)).trans
    (SourceScalarAffineScaleTransport.scale_chart_iff (heatCoefficient t ξ z.val) z.val)).mpr z.property
private theorem forward_component(f:QuantumTest)(z:physicalChart)(word:Occupation):
    forwardGenerator f z.val word=(-6:ℂ)*(reciprocalVolume z.val:ℂ)*
      fderiv ℝ (component word f) z.val (euler z.val)-
      (9:ℂ)*(word.card+3:ℂ)*(reciprocalVolume z.val:ℂ)*f z.val word:=by
  change (-9*Complex.I)*((reciprocalVolume z.val:ℂ)*dilation f z.val word)+
    9*((reciprocalVolume z.val:ℂ)*f z.val word)=_
  rw [dilation_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring
private theorem input_forward_drift(t:ℝ)(ht:0<t)(ξ:ℝ):
    forwardGenerator*heatInput t ht ξ=
      heatInput t ht ξ*(forwardGenerator-(3:ℂ) • (deltaAction t ht ξ*combinedGenerator)):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · apply PiLp.ext;intro word
    let hp:physicalChart:=⟨z,hz⟩
    let hm:physicalChart:=⟨inputMap t ξ z,inputMap_chart t ξ hp⟩
    change forwardGenerator (heatInput t ht ξ f) z word=
      heatInput t ht ξ (forwardGenerator f-(3:ℂ) • deltaAction t ht ξ (combinedGenerator f)) z word
    rw [forward_component _ hp,input_euler_derivative _ _ _ _ hp,heatInput_point,heatInput_point]
    change (-6:ℂ)*(reciprocalVolume z:ℂ)*
      ((Real.exp ((25/2:ℝ)*heatCoefficient t ξ z):ℂ)*
        (fderiv ℝ (component word f) (inputMap t ξ z) (euler z)+
          ((GaussNativeEnergy.volume z/2)*heatDelta t ξ z:ℝ)*combinedGenerator f (inputMap t ξ z) word))-
      (9:ℂ)*(word.card+3:ℂ)*(reciprocalVolume z:ℂ)*
        ((Real.exp ((25/2:ℝ)*heatCoefficient t ξ z):ℂ)*f (inputMap t ξ z) word)=
      (Real.exp ((25/2:ℝ)*heatCoefficient t ξ z):ℂ)*
        (forwardGenerator f (inputMap t ξ z) word-
          3*((heatDelta t ξ (inputMap t ξ z):ℂ)*combinedGenerator f (inputMap t ξ z) word))
    rw [forward_component f hm]
    have he:euler (inputMap t ξ z)=euler z:=rfl
    have hu:reciprocalVolume (inputMap t ξ z)=reciprocalVolume z:=rfl
    have hd:heatDelta t ξ (inputMap t ξ z)=heatDelta t ξ z:=rfl
    rw [he,hu,hd]
    simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
    have hV: (GaussNativeEnergy.volume z:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (volume_pos hp).ne'
    unfold reciprocalVolume
    push_cast
    field_simp [hV]
    ring
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]

open SourceClockPhiMatchedDiffusionSource SourceClockPhiNativeMatchedSource
private theorem drift_forward_split:
    driftClock=inverseVolumeAction*combinedGenerator-(1/3:ℂ) • forwardGenerator:=by
  rw [forwardGenerator_original]
  unfold driftClock matchedColumn
  module
private theorem forward_delta(t:ℝ)(ht:0<t)(ξ:ℝ):
    forwardUAction t ht.le+deltaAction t ht ξ=inverseVolumeAction-(ξ:ℂ) • kappaAction t ht:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (forwardU t z:ℂ) • f z+(heatDelta t ξ z:ℂ) • f z=
    (reciprocalVolume z:ℂ) • f z-(ξ:ℂ) • ((heatKappa t z:ℂ) • f z)
  unfold heatDelta
  simp only [Complex.ofReal_sub,Complex.ofReal_mul]
  module
private theorem actual_heat_B3(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    driftClock (sourceHeatCore t ht ξ f)=
      sourceHeatCore t ht ξ (driftClock f-(ξ:ℂ) • kappaAction t ht (combinedGenerator f)):=by
  have hK(q:QuantumTest):sourceForwardCore t ht.le (heatInput t ht ξ q)=sourceHeatCore t ht ξ q:=
    LinearMap.congr_fun (heatInput_source t ht ξ) q
  have hJ:=LinearMap.congr_fun
    (SourceClockPhiForwardDriftTransport.actual_forward_drift_commute t ht.le).eq (heatInput t ht ξ f)
  have hN:=LinearMap.congr_fun (input_forward_drift t ht ξ) f
  simp only [Module.End.mul_apply] at hJ hN
  have hLV:forwardGenerator (sourceHeatCore t ht ξ f)=
      sourceHeatCore t ht ξ (forwardGenerator f-(3:ℂ) • deltaAction t ht ξ (combinedGenerator f)):=by
    rw [←hK,hJ,hN]
    exact hK _
  have hB(q:QuantumTest):driftClock q=inverseVolumeAction (combinedGenerator q)-(1/3:ℂ) • forwardGenerator q:=
    LinearMap.congr_fun drift_forward_split q
  have hF:=LinearMap.congr_fun (forward_delta t ht ξ) (combinedGenerator f)
  change forwardUAction t ht.le (combinedGenerator f)+deltaAction t ht ξ (combinedGenerator f)=
    inverseVolumeAction (combinedGenerator f)-(ξ:ℂ) • kappaAction t ht (combinedGenerator f) at hF
  have he:=congrArg (sourceHeatCore t ht ξ) hF
  simp only [map_add,map_sub,map_smul] at he
  rw [hB]
  change (inverseVolumeAction*combinedGenerator) (sourceHeatCore t ht ξ f)-
    (1/3:ℂ) • forwardGenerator (sourceHeatCore t ht ξ f)=_
  rw [heat_UD,hLV,hB]
  simp only [map_sub,map_smul]
  linear_combination (norm:=module) he

open SourceClockPhiComparisonNativeClosedGraph SourceClockPhiWholeSignedWorkIntegrable
private theorem heat_mean_on_core(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatOperator t ht (embed f)=heatMeanCore t ht f:=by
  calc
    _=heatMeanCore t ht (coreEquiv.symm (coreEquiv f)):=by
      unfold heatOperator
      exact ContinuousLinearMap.extend_eq _ GaussBoundedMultiplier.core_dense
        isometry_subtype_coe.isUniformInducing (coreEquiv f)
    _=_:=by rw [coreEquiv.symm_apply_apply]
def heatDriftMean(t:ℝ)(ht:0<t):QuantumTest→ₗ[ℂ]H:=
  (heatMeanCore t ht).comp driftClock-(weightedHeatMeanCore t ht).comp (kappaAction t ht*combinedGenerator)
def heatComparisonEnergy(t:ℝ)(ht:0<t)(f:QuantumTest):ℝ:=
  ‖heatDriftMean t ht f‖^2+(1/2:ℝ)*‖heatUDReader t ht (embed f)‖^2
private theorem comparison_graph(t:ℝ)(ht:0<t)(f:QuantumTest):
    (heatOperator t ht (embed f),heatDriftMean t ht f)∈SymmetricGraphClosure.closedGraph (realize driftClock):=by
  have he(ξ:ℝ):embed (driftClock (sourceHeatCore t ht ξ f))=
      embed (sourceHeatCore t ht ξ (driftClock f))-
        (ξ:ℂ) • embed (sourceHeatCore t ht ξ (kappaAction t ht (combinedGenerator f))):=by
    rw [actual_heat_B3]
    simp only [map_sub,map_smul]
  have hi:Integrable (fun ξ=>embed (driftClock (sourceHeatCore t ht ξ f))) γ:=by
    simp only [he]
    exact (sourceHeat_integrable t ht (driftClock f)).sub
      (weighted_heat_integrable t ht (kappaAction t ht (combinedGenerator f)))
  have hg:=integral_core_graph driftClock (fun ξ=>sourceHeatCore t ht ξ f)
    (sourceHeat_integrable t ht f) hi
  have heI:(∫ξ,embed (driftClock (sourceHeatCore t ht ξ f)) ∂γ)=heatDriftMean t ht f:=by
    simp only [he]
    exact integral_sub (sourceHeat_integrable t ht (driftClock f))
      (weighted_heat_integrable t ht (kappaAction t ht (combinedGenerator f)))
  change (heatMeanCore t ht f,(∫ξ,embed (driftClock (sourceHeatCore t ht ξ f)) ∂γ))∈
    SymmetricGraphClosure.closedGraph (realize driftClock) at hg
  rw [heI] at hg
  rw [heat_mean_on_core]
  exact hg
private theorem weighted_drift_mean(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatMeanCore t ht (forwardUAction t ht.le (combinedGenerator f))=heatUDReader t ht (embed f):=by
  have hp(ξ:ℝ):embed ((inverseVolumeAction*combinedGenerator) (sourceHeatCore t ht ξ f))=
      embed (sourceHeatCore t ht ξ (forwardUAction t ht.le (combinedGenerator f))):=by rw [heat_UD]
  have hi:Integrable (fun ξ=>embed ((inverseVolumeAction*combinedGenerator) (sourceHeatCore t ht ξ f))) γ:=by
    simp only [hp]
    exact sourceHeat_integrable t ht _
  have hg:=integral_core_graph (inverseVolumeAction*combinedGenerator) (fun ξ=>sourceHeatCore t ht ξ f)
    (sourceHeat_integrable t ht f) hi
  simp only [hp] at hg
  change (heatMeanCore t ht f,heatMeanCore t ht (forwardUAction t ht.le (combinedGenerator f)))∈
    SymmetricGraphClosure.closedGraph (realize (inverseVolumeAction*combinedGenerator)) at hg
  rw [←heat_mean_on_core] at hg
  exact (((actual_heat_native_smoothing t ht).2.2.2.2 (embed f)).2.2).2 _ hg
private def rawComparisonEnergy(t:ℝ)(ht:0<t)(f:QuantumTest):ℝ:=
  (∫ξ:ℝ,‖embed (sourceHeatCore t ht ξ (driftClock f-(ξ:ℂ) • kappaAction t ht (combinedGenerator f)))‖^2 ∂γ)+
    (1/2:ℝ)*(∫ξ:ℝ,‖embed (sourceHeatCore t ht ξ (forwardUAction t ht.le (combinedGenerator f)))‖^2 ∂γ)
def heatComparisonDeficit(t:ℝ)(ht:0<t)(f:QuantumTest):ℝ:=rawComparisonEnergy t ht f-heatComparisonEnergy t ht f
private theorem raw_comparison_source(t:ℝ)(ht:0<t)(f:QuantumTest):
    rawComparisonEnergy t ht f=‖embed (driftClock f)‖^2+
      ‖embed (kappaAction t ht (combinedGenerator f))‖^2+
        (1/2:ℝ)*‖embed (forwardUAction t ht.le (combinedGenerator f))‖^2:=by
  unfold rawComparisonEnergy
  simp_rw [sourceHeat_norm,map_sub,map_smul]
  rw [(gaussian_shift_square (embed (driftClock f))
    (embed (kappaAction t ht (combinedGenerator f)))).2]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
private theorem mean_comparison_source(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatComparisonEnergy t ht f≤rawComparisonEnergy t ht f:=by
  let K:ℝ→QuantumTest→ₗ[ℂ]H:=fun ξ=>embed.comp (sourceHeatCore t ht ξ)
  have h:=gaussian_source_columns K (sourceHeat_norm t ht) (sourceHeat_integrable t ht)
    (weighted_heat_integrable t ht) (driftClock f) (kappaAction t ht (combinedGenerator f))
    (forwardUAction t ht.le (combinedGenerator f))
  change ‖heatDriftMean t ht f‖^2+(1/2:ℝ)*
    ‖heatMeanCore t ht (forwardUAction t ht.le (combinedGenerator f))‖^2≤_ at h
  rw [weighted_drift_mean,←raw_comparison_source] at h
  exact h
/-- The actual coframe drift retains one coherent Gaussian correction column. -/
theorem actual_heat_comparison_source(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    driftClock (sourceHeatCore t ht ξ f)=
      sourceHeatCore t ht ξ (driftClock f-(ξ:ℂ) • kappaAction t ht (combinedGenerator f)):=actual_heat_B3 t ht ξ f
/-- The finite source mean pays the original comparison form and preserves its Jensen deficit. -/
theorem actual_heat_comparison_payment(t:ℝ)(ht:0<t)(f:QuantumTest):
    ((heatOperator t ht (embed f),heatDriftMean t ht f)∈SymmetricGraphClosure.closedGraph (realize driftClock) ∧
      ∀y:H,(heatOperator t ht (embed f),y)∈SymmetricGraphClosure.closedGraph (realize driftClock)→y=heatDriftMean t ht f) ∧
    heatComparisonEnergy t ht f≤comparisonEnergy f ∧
    0≤heatComparisonDeficit t ht f ∧
    heatComparisonDeficit t ht f≤comparisonEnergy f-heatComparisonEnergy t ht f:=by
  have hG:=comparison_graph t ht f
  have hJ:=mean_comparison_source t ht f
  have hR:rawComparisonEnergy t ht f≤comparisonEnergy f:=by
    rw [raw_comparison_source]
    have h:=actual_coefficient_columns t ht (combinedGenerator f)
    dsimp only [comparisonEnergy]
    linarith
  refine ⟨⟨hG,fun _ hy=>actual_B3_closed_graph_singlevalued hy hG⟩,hJ.trans hR,?_,?_⟩
  · exact sub_nonneg.mpr hJ
  · exact sub_le_sub_right hR _

end LowEnergy.ClockPhiHeatComparisonWork
