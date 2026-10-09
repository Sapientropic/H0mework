import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedWorkComposition
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiComposedCoframeGaussianWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiTwoStepGaussianMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileCoframeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileLocalNativeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileNativeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileCoframeRemainingWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatRadialCovariancePair
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedHamiltonianSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiCorrectedHamiltonianWorkEvolution
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy GaussNativeForm
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource
open ClockPhiHeatCorrectedCovarianceSource ClockPhiCorrectedWorkComposition ClockPhiHeatCovariancePhase
open SourcePhysicalKineticSquare SourceCoframeVolume SourceClockPhiForwardNativeReturn
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev Quad:=(ℝ×ℝ)×(ℝ×ℝ)
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ4:=(γ.prod γ).prod (γ.prod γ)
private theorem coefficient_point(t ξ η:ℝ)(z:physicalChart):
    correctedCoefficient t ξ η z.val=
      -Real.log ((volume z.val+18*t)/volume z.val)/6+
      Real.sqrt (Real.log ((volume z.val+18*t)/volume z.val)/9)*
        (ξ*Real.cos (clockPhase (Real.log ((volume z.val+18*t)/volume z.val)))+
         η*Real.sin (clockPhase (Real.log ((volume z.val+18*t)/volume z.val)))):=by
  have he:heatLog t z.val=Real.log ((volume z.val+18*t)/volume z.val):=by
    unfold heatLog reciprocalVolume
    congr 1
    field_simp [(volume_pos z).ne']
  change -heatLog t z.val/6+Real.sqrt (heatLog t z.val/9)*
    (ξ*Real.cos (clockPhase (heatLog t z.val))+η*Real.sin (clockPhase (heatLog t z.val)))=_
  rw [he]
private theorem composed_smooth(s t:ℝ)(hs:0<s)(ht:0<t)(x:Quad)(z:physicalChart):
    ContDiffAt ℝ ∞ (composedCoefficient s t x) z.val:=by
  simpa only [composedCoefficient,Function.comp_def] using!
    ((coefficient_smooth s hs x.2.1 x.2.2 ⟨forwardPoint t z.val,forward_chart t ht.le z⟩).comp z.val
      (forward_smooth t ht.le z)).add (coefficient_smooth t ht x.1.1 x.1.2 z)
private theorem composed_first(s t:ℝ)(x:Quad)(z w:SourceCoordinateSlice)(h:z.1=w.1):
    composedCoefficient s t x z=composedCoefficient s t x w:=by
  rcases z with ⟨z1,z2⟩
  rcases w with ⟨w1,w2⟩
  dsimp at h
  subst w1
  rfl
private theorem composed_exponential_moment(s t q:ℝ)(hs:0<s)(ht:0<t)(z:physicalChart):
    Integrable (fun x:Quad=>Real.exp (q*composedCoefficient s t x z.val)) γ4 ∧
    (∫x:Quad,Real.exp (q*composedCoefficient s t x z.val) ∂γ4)=
      Real.rpow (forwardRatio (s+t) z.val) (q*(q-3)/18):=by
  let V:=volume z.val
  let W:=V+18*t
  let θ:=clockPhase (Real.log ((V+18*t)/V))
  let φ:=clockPhase (Real.log ((W+18*s)/W))
  let E:Quad→ℝ:=fun x=>Real.exp (q*((-Real.log ((V+18*t)/V)/6+
    Real.sqrt (Real.log ((V+18*t)/V)/9)*(x.1.1*Real.cos θ+x.1.2*Real.sin θ))+
    (-Real.log ((W+18*s)/W)/6+Real.sqrt (Real.log ((W+18*s)/W)/9)*
      (x.2.1*Real.cos φ+x.2.2*Real.sin φ))))
  have h:Integrable E γ4 ∧ (∫x:Quad,E x ∂γ4)=Real.rpow ((V+18*(s+t))/V) (q*(q-3)/18):=
    SourceClockPhiTwoStepGaussianMoment.actual_two_step_exponential_moment V t s q θ φ (volume_pos z) ht hs
  have he(x:Quad):Real.exp (q*composedCoefficient s t x z.val)=E x:=by
    unfold composedCoefficient
    rw [coefficient_point s x.2.1 x.2.2 ⟨forwardPoint t z.val,forward_chart t ht.le z⟩,
      coefficient_point t x.1.1 x.1.2 z,forward_volume t ht.le z]
    dsimp only [E,V,W,θ,φ]
    congr 1
    ring
  constructor
  · exact h.1.congr (Eventually.of_forall (fun x=>(he x).symm))
  · simp_rw [he]
    exact h.2
private theorem inverse_forward(t:ℝ)(ht:0<t)(z:physicalChart):
    reciprocalVolume (forwardPoint t z.val)=forwardU t z.val:=by
  unfold reciprocalVolume forwardU
  rw [forward_volume t ht.le z]
private theorem second_inverse_forward(s t:ℝ)(ht:0<t)(z:physicalChart):
    forwardU s (forwardPoint t z.val)=forwardU (s+t) z.val:=by
  unfold forwardU
  rw [forward_volume t ht.le z]
  congr 1
  ring
private theorem noise_zero(t:ℝ)(z:SourceCoordinateSlice):covarianceNoise t 0 0 z=0:=by
  rw [actual_covariance_noise_affine t 0 0 z]
  ring
private def noiseColumn(s t:ℝ)(j:Fin 4)(z:SourceCoordinateSlice):ℝ:=
  ![covarianceNoise t 1 0 z,covarianceNoise t 0 1 z,
    covarianceNoise s 1 0 (forwardPoint t z),covarianceNoise s 0 1 (forwardPoint t z)] j
private theorem composed_noise_columns(s t:ℝ)(x:Quad)(z:SourceCoordinateSlice):
    composedNoise s t x z=x.1.1*noiseColumn s t 0 z+x.1.2*noiseColumn s t 1 z+
      x.2.1*noiseColumn s t 2 z+x.2.2*noiseColumn s t 3 z:=by
  unfold composedNoise
  rw [actual_covariance_noise_affine s x.2.1 x.2.2,actual_covariance_noise_affine t x.1.1 x.1.2]
  change _ = x.1.1*covarianceNoise t 1 0 z+x.1.2*covarianceNoise t 0 1 z+
    x.2.1*covarianceNoise s 1 0 (forwardPoint t z)+x.2.2*covarianceNoise s 0 1 (forwardPoint t z)
  ring
private theorem composed_noise_square(s t:ℝ)(hs:0<s)(ht:0<t)(z:physicalChart):
    (∑j:Fin 4,noiseColumn s t j z.val^2)=
      covarianceNoise (s+t) 1 0 z.val^2+covarianceNoise (s+t) 0 1 z.val^2:=by
  have hT:=actual_covariance_noise_square t ht z
  have hS:=actual_covariance_noise_square s hs ⟨forwardPoint t z.val,forward_chart t ht.le z⟩
  have hST:=actual_covariance_noise_square (s+t) (by linarith) z
  rw [inverse_forward t ht z,second_inverse_forward s t ht z] at hS
  simp only [noiseColumn,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  linarith
private theorem coefficient_affine(t ξ η:ℝ)(z:SourceCoordinateSlice):
    correctedCoefficient t ξ η z=correctedCoefficient t 0 0 z+
      ξ*(correctedCoefficient t 1 0 z-correctedCoefficient t 0 0 z)+
      η*(correctedCoefficient t 0 1 z-correctedCoefficient t 0 0 z):=by
  let a:=heatMean t z
  let b:=Real.sqrt (heatVariance t z)
  let c:=Real.cos (clockPhase (heatLog t z))
  let d:=Real.sin (clockPhase (heatLog t z))
  change a+b*(ξ*c+η*d)=(a+b*(0*c+0*d))+ξ*((a+b*(1*c+0*d))-(a+b*(0*c+0*d)))+
    η*((a+b*(0*c+1*d))-(a+b*(0*c+0*d)))
  ring
private theorem composed_affine(s t:ℝ)(x:Quad)(z:SourceCoordinateSlice):
    composedCoefficient s t x z=
      correctedCoefficient s 0 0 (forwardPoint t z)+correctedCoefficient t 0 0 z+
      x.1.1*(correctedCoefficient t 1 0 z-correctedCoefficient t 0 0 z)+
      x.1.2*(correctedCoefficient t 0 1 z-correctedCoefficient t 0 0 z)+
      x.2.1*(correctedCoefficient s 1 0 (forwardPoint t z)-correctedCoefficient s 0 0 (forwardPoint t z))+
      x.2.2*(correctedCoefficient s 0 1 (forwardPoint t z)-correctedCoefficient s 0 0 (forwardPoint t z)):=by
  unfold composedCoefficient
  rw [coefficient_affine s x.2.1 x.2.2,coefficient_affine t x.1.1 x.1.2]
  ring
private theorem composed_joint_continuous(s t:ℝ)(hs:0<s)(ht:0<t)(y:SourceCoordinateSlice×Quad)
    (hy:y.1∈physicalChart):ContinuousAt (fun x:SourceCoordinateSlice×Quad=>composedCoefficient s t x.2 x.1) y:=by
  have hT(a b:ℝ):ContinuousAt (fun x:SourceCoordinateSlice×Quad=>correctedCoefficient t a b x.1) y:=by
    have h0:ContinuousAt (correctedCoefficient t a b) y.1:=
      (coefficient_smooth t ht a b ⟨y.1,hy⟩).continuousAt
    exact h0.comp_of_eq continuousAt_fst rfl
  have hS(a b:ℝ):ContinuousAt (fun x:SourceCoordinateSlice×Quad=>correctedCoefficient s a b (forwardPoint t x.1)) y:=by
    have h0:ContDiffAt ℝ ∞ (fun z:SourceCoordinateSlice=>correctedCoefficient s a b (forwardPoint t z)) y.1:=by
      simpa only [Function.comp_def] using!
        (coefficient_smooth s hs a b ⟨forwardPoint t y.1,forward_chart t ht.le ⟨y.1,hy⟩⟩).comp y.1
          (forward_smooth t ht.le ⟨y.1,hy⟩)
    exact h0.continuousAt.comp continuousAt_fst
  have h1:ContinuousAt (fun x:SourceCoordinateSlice×Quad=>x.2.1.1) y:=by fun_prop
  have h2:ContinuousAt (fun x:SourceCoordinateSlice×Quad=>x.2.1.2) y:=by fun_prop
  have h3:ContinuousAt (fun x:SourceCoordinateSlice×Quad=>x.2.2.1) y:=by fun_prop
  have h4:ContinuousAt (fun x:SourceCoordinateSlice×Quad=>x.2.2.2) y:=by fun_prop
  have he:(fun x:SourceCoordinateSlice×Quad=>composedCoefficient s t x.2 x.1)=
      fun x=>correctedCoefficient s 0 0 (forwardPoint t x.1)+correctedCoefficient t 0 0 x.1+
      x.2.1.1*(correctedCoefficient t 1 0 x.1-correctedCoefficient t 0 0 x.1)+
      x.2.1.2*(correctedCoefficient t 0 1 x.1-correctedCoefficient t 0 0 x.1)+
      x.2.2.1*(correctedCoefficient s 1 0 (forwardPoint t x.1)-correctedCoefficient s 0 0 (forwardPoint t x.1))+
      x.2.2.2*(correctedCoefficient s 0 1 (forwardPoint t x.1)-correctedCoefficient s 0 0 (forwardPoint t x.1)):=by
    funext x
    exact composed_affine s t x.2 x.1
  rw [he]
  exact ((((hS 0 0).add (hT 0 0)).add (h1.mul ((hT 1 0).sub (hT 0 0)))).add
    (h2.mul ((hT 0 1).sub (hT 0 0)))).add (h3.mul ((hS 1 0).sub (hS 0 0))) |>.add
    (h4.mul ((hS 0 1).sub (hS 0 0)))
private def rawProfile(s t p q:ℝ)(x:SourceCoordinateSlice×Quad):ℝ:=
  (forwardRatio (s+t) x.1)^p*Real.exp (q*composedCoefficient s t x.2 x.1)
private def goodProfile(s t p q:ℝ)(x:SourceCoordinateSlice×Quad):ℝ:=by
  classical
  exact if x.1∈physicalChart then rawProfile s t p q x else 0
private theorem goodProfile_measurable(s t p q:ℝ)(hs:0<s)(ht:0<t):Measurable (goodProfile s t p q):=by
  classical
  have hO:IsOpen {x:SourceCoordinateSlice×Quad | x.1∈physicalChart}:=physicalChart.isOpen.preimage continuous_fst
  have hc:ContinuousOn (rawProfile s t p q) {x:SourceCoordinateSlice×Quad | x.1∈physicalChart}:=by
    intro x hx
    have hV:ContinuousAt (fun y:SourceCoordinateSlice×Quad=>volume y.1) x:=volume_smooth.continuous.continuousAt.comp continuousAt_fst
    have hR:ContinuousAt (fun y:SourceCoordinateSlice×Quad=>forwardRatio (s+t) y.1) x:=
      (hV.add_const (18*(s+t))).div hV (volume_pos ⟨x.1,hx⟩).ne'
    have he:ContinuousAt (fun y:SourceCoordinateSlice×Quad=>q*composedCoefficient s t y.2 y.1) x:=
      continuousAt_const.mul (composed_joint_continuous s t hs ht x hx)
    have hp:ContinuousAt (rawProfile s t p q) x:=
      (hR.rpow_const (Or.inl (forward_ratio_pos (s+t) (by linarith) ⟨x.1,hx⟩).ne')).mul
        (Real.continuous_exp.continuousAt.comp he)
    exact hp.continuousWithinAt
  exact hc.measurable_piecewise continuousOn_const hO.measurableSet
private theorem goodProfile_chart(s t p q:ℝ)(x:Quad)(z:physicalChart):
    goodProfile s t p q (z.val,x)=(forwardRatio (s+t) z.val)^p*Real.exp (q*composedCoefficient s t x z.val):=by
  simp only [goodProfile,if_pos z.property,rawProfile]
abbrev composedProfileWeight(s t:ℝ)(hs:0<s)(ht:0<t)(p q:ℝ)(x:Quad):End:=
  SourceClockPhiProfileLocalNativeReturn.actualProfileWeight (s+t) (by linarith)
    (composedCoefficient s t x) (composed_smooth s t hs ht x) p q
private theorem density_multiply(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (f h:QuantumTest)(z:SourceCoordinateSlice):densityPair f (multiply b hb h) z=(b z:ℂ)*densityPair f h z:=by
  rw [densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star (f z word)*((b z:ℂ)*h z word)=_
  ring
private theorem density_offchart(f h:QuantumTest)(z:SourceCoordinateSlice)(hz:z∉physicalChart):densityPair f h z=0:=by
  have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun hx=>hz (f.tsupport_subset hx))
  simp only [densityPair,hf,map_zero,inner_zero_left]
private abbrev config:=GaussHistoryHilbert.configurationMeasure
private def kernel(s t p q:ℝ)(f h:QuantumTest)(x:SourceCoordinateSlice×Quad):ℂ:=
  (goodProfile s t p q x:ℂ)*densityPair f h x.1
private theorem kernel_section(s t p q:ℝ)(hs:0<s)(ht:0<t)(f h:QuantumTest)(z:SourceCoordinateSlice):
    Integrable (fun x:Quad=>kernel s t p q f h (z,x)) γ4:=by
  by_cases hz:z∈physicalChart
  · have hi:=((composed_exponential_moment s t q hs ht ⟨z,hz⟩).1.const_mul ((forwardRatio (s+t) z)^p)).ofReal.mul_const (densityPair f h z)
    exact hi.congr (Eventually.of_forall (fun x=>by
      simp only [kernel,goodProfile,if_pos hz,rawProfile]
      rfl))
  · simp only [kernel,density_offchart f h z hz,mul_zero]
    exact integrable_const (0:ℂ)
private theorem kernel_integral(s t p q:ℝ)(hs:0<s)(ht:0<t)(f h:QuantumTest)(z:SourceCoordinateSlice):
    (∫x:Quad,kernel s t p q f h (z,x) ∂γ4)=
      densityPair f (SourceClockPhiHeatLocalNativeGaussian.gaussianProfileWeight (s+t) (by linarith) (p+q*(q-3)/18) h) z:=by
  rw [SourceClockPhiHeatLocalNativeGaussian.gaussianProfileWeight,density_multiply]
  by_cases hz:z∈physicalChart
  · have hm:=(composed_exponential_moment s t q hs ht ⟨z,hz⟩).2
    simp only [kernel,goodProfile,if_pos hz,rawProfile,Complex.ofReal_mul]
    rw [integral_mul_const,integral_const_mul,integral_complex_ofReal,hm,
      ←Complex.ofReal_mul]
    congr 2
    exact (Real.rpow_add (forward_ratio_pos (s+t) (by linarith) ⟨z,hz⟩) p (q*(q-3)/18)).symm
  · simp only [kernel,density_offchart f h z hz,mul_zero,integral_zero]
private theorem kernel_norm_integral(s t p q:ℝ)(hs:0<s)(ht:0<t)(f h:QuantumTest)(z:SourceCoordinateSlice):
    (∫x:Quad,‖kernel s t p q f h (z,x)‖ ∂γ4)=
      ‖densityPair f (SourceClockPhiHeatLocalNativeGaussian.gaussianProfileWeight (s+t) (by linarith) (p+q*(q-3)/18) h) z‖:=by
  rw [SourceClockPhiHeatLocalNativeGaussian.gaussianProfileWeight,density_multiply]
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos (s+t) (by linarith) ⟨z,hz⟩
    have hp(x:Quad):0 ≤ (forwardRatio (s+t) z)^p*Real.exp (q*composedCoefficient s t x z):=
      mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
    have hm:=(composed_exponential_moment s t q hs ht ⟨z,hz⟩).2
    have hk(x:Quad):‖kernel s t p q f h (z,x)‖=
        ((forwardRatio (s+t) z)^p*Real.exp (q*composedCoefficient s t x z))*‖densityPair f h z‖:=by
      unfold kernel
      rw [goodProfile_chart s t p q x ⟨z,hz⟩,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp x)]
    simp_rw [hk]
    rw [integral_mul_const,integral_const_mul,hm]
    change ((forwardRatio (s+t) z)^p*(forwardRatio (s+t) z)^(q*(q-3)/18))*_= _
    rw [←Real.rpow_add hr,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.le _)]
  · simp only [kernel,density_offchart f h z hz,mul_zero,norm_zero,integral_zero]
private theorem composed_weighted_pair(s t p q:ℝ)(hs:0<s)(ht:0<t)(f h:QuantumTest):
    Integrable (fun x:Quad=>sourcePair f (composedProfileWeight s t hs ht p q x h)) γ4 ∧
    (∫x:Quad,sourcePair f (composedProfileWeight s t hs ht p q x h) ∂γ4)=
      sourcePair f (SourceClockPhiHeatLocalNativeGaussian.gaussianProfileWeight (s+t) (by linarith) (p+q*(q-3)/18) h):=by
  have hm:AEStronglyMeasurable (kernel s t p q f h) (config.prod γ4):=
    (Complex.continuous_ofReal.measurable.comp (goodProfile_measurable s t p q hs ht)).aestronglyMeasurable.mul
      (densityPair_integrable f h).aestronglyMeasurable.comp_fst
  have hp:Integrable (kernel s t p q f h) (config.prod γ4):=by
    apply (integrable_prod_iff hm).mpr
    exact ⟨Eventually.of_forall (kernel_section s t p q hs ht f h),
      (densityPair_integrable f (SourceClockPhiHeatLocalNativeGaussian.gaussianProfileWeight (s+t) (by linarith) (p+q*(q-3)/18) h)).norm.congr
        (Eventually.of_forall (fun z=>(kernel_norm_integral s t p q hs ht f h z).symm))⟩
  have he(x:Quad):sourcePair f (composedProfileWeight s t hs ht p q x h)=∫z,kernel s t p q f h (z,x) ∂config:=by
    rw [sourcePair_integral]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z=>by
      change densityPair f (multiply (fun y=>(forwardRatio (s+t) y)^p*Real.exp (q*composedCoefficient s t x y)) _ h) z=kernel s t p q f h (z,x)
      rw [density_multiply]
      by_cases hz:z∈physicalChart
      · simp only [kernel,goodProfile_chart s t p q x ⟨z,hz⟩]
      · simp only [kernel,density_offchart f h z hz,mul_zero])
  refine ⟨hp.integral_prod_right.congr (Eventually.of_forall (fun x=>(he x).symm)),?_⟩
  simp_rw [he]
  have hi:Integrable (Function.uncurry (fun z x=>kernel s t p q f h (z,x))) (config.prod γ4):=hp
  rw [←integral_integral_swap hi]
  simp_rw [kernel_integral s t p q hs ht f h]
  exact (sourcePair_integral _ _).symm

open SourceClockPhiProfileCoframeReturn SourceClockPhiProfileCoframeRemainingWork
open SourceClockPhiProfileLocalNativeReturn SourceClockPhiProfileNativeReturn
open SourceClockPhiCorrectedGaussianPair SourceScalarVirialBulk GaussNativePotential
private def Evolves(s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest)(X:End):Prop:=
  Integrable (fun x:Quad=>sourcePair (composedCompleteCore s t hs ht x f)
    (X (composedCompleteCore s t hs ht x g))) γ4 ∧
  Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore (s+t) (by linarith) x.1 x.2 f)
    (X (correctedCompleteCore (s+t) (by linarith) x.1 x.2 g))) (γ.prod γ) ∧
  (∫x:Quad,sourcePair (composedCompleteCore s t hs ht x f)
    (X (composedCompleteCore s t hs ht x g)) ∂γ4)=
  (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore (s+t) (by linarith) x.1 x.2 f)
    (X (correctedCompleteCore (s+t) (by linarith) x.1 x.2 g)) ∂γ.prod γ)
private theorem coefficient_first(t ξ η:ℝ)(x y:SourceCoordinateSlice)(h:x.1=y.1):
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  rcases x with ⟨x1,x2⟩
  rcases y with ⟨y1,y2⟩
  dsimp at h
  subst y1
  rfl
private theorem sector_evolves(s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest)(X:End)(p q:ℝ)
    (hsource:∀ (c:SourceCoordinateSlice→ℝ) (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
      (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y),
      sourcePair (profileCompleteCore (s+t) (by linarith) c hc (profileFirstInvariant c hfirst) f)
        (X (profileCompleteCore (s+t) (by linarith) c hc (profileFirstInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight (s+t) (by linarith) c hc p q (X g))):
    Evolves s t hs ht f g X:=by
  have hC(x:Quad):sourcePair (composedCompleteCore s t hs ht x f) (X (composedCompleteCore s t hs ht x g))=
      sourcePair f (composedProfileWeight s t hs ht p q x (X g)):=
    hsource (composedCoefficient s t x) (composed_smooth s t hs ht x) (composed_first s t x)
  have hO(x:ℝ×ℝ):sourcePair (correctedCompleteCore (s+t) (by linarith) x.1 x.2 f)
      (X (correctedCompleteCore (s+t) (by linarith) x.1 x.2 g))=
      sourcePair f (correctedProfileWeight (s+t) (by linarith) p q x.1 x.2 (X g)):=
    hsource (correctedCoefficient (s+t) x.1 x.2) (coefficient_smooth (s+t) (by linarith) x.1 x.2)
      (coefficient_first (s+t) x.1 x.2)
  have h4:=composed_weighted_pair s t p q hs ht f (X g)
  have h2:=actual_corrected_gaussian_weighted_source_pair (s+t) (by linarith) p q f (X g)
  refine ⟨h4.1.congr (Eventually.of_forall (fun x=>(hC x).symm)),
    h2.1.congr (Eventually.of_forall (fun x=>(hO x).symm)),?_⟩
  simp_rw [hC,hO]
  exact h4.2.trans h2.2.symm
private theorem evolves_add(s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest)(X Y:End)
    (hX:Evolves s t hs ht f g X)(hY:Evolves s t hs ht f g Y):
    Evolves s t hs ht f g (X+Y):=by
  have he(p q:QuantumTest):sourcePair p ((X+Y) q)=sourcePair p (X q)+sourcePair p (Y q):=by
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
  refine ⟨(hX.1.add hY.1).congr (Eventually.of_forall (fun x=>(he _ _).symm)),
    (hX.2.1.add hY.2.1).congr (Eventually.of_forall (fun x=>(he _ _).symm)),?_⟩
  simp_rw [he]
  rw [integral_add hX.1 hY.1,integral_add hX.2.1 hY.2.1,hX.2.2,hY.2.2]
private theorem evolves_smul(s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest)(a:ℂ)(X:End)
    (hX:Evolves s t hs ht f g X):Evolves s t hs ht f g (a • X):=by
  have he(p q:QuantumTest):sourcePair p ((a • X) q)=a*sourcePair p (X q):=by
    simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]
  refine ⟨(hX.1.const_mul a).congr (Eventually.of_forall (fun x=>(he _ _).symm)),
    (hX.2.1.const_mul a).congr (Eventually.of_forall (fun x=>(he _ _).symm)),?_⟩
  simp_rw [he]
  rw [integral_const_mul,integral_const_mul,hX.2.2]

private abbrev centerValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*‖scalarField z‖^2
private abbrev vacLinValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*inner ℝ vacuum (scalarField z)
private abbrev vacConstValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*‖vacuum‖^2
private abbrev spatialValue(z:SourceCoordinateSlice):ℝ:=
  -(sourceTime 0*GaussNativeEnergy.volume z/2*∑i:Fin 3,∑j:Fin 3,inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j))
private theorem potential_decompose(z:SourceCoordinateSlice):
    potential z=centerValue z-2*vacLinValue z+vacConstValue z+spatialValue z+magneticPotential z:=by
  have hsub:scalarField z-vacuum=(z.2.1:Scalar):=by unfold scalarField;abel
  have hn:=norm_sub_sq_real (scalarField z) vacuum
  rw [hsub,real_inner_comm vacuum (scalarField z)] at hn
  unfold potential scalarPotential centerValue vacLinValue vacConstValue spatialValue
  rw [real_inner_self_eq_norm_sq,hn]
  ring
private theorem potential_action_decompose:
    multiply potential potential_smooth=centeredAction-(2:ℂ) • vacuumLinearAction+
      vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (potential z:ℂ) • f z=(centerValue z:ℂ) • f z-
    (2:ℂ) • ((vacLinValue z:ℂ) • f z)+(vacConstValue z:ℂ) • f z+
      (spatialValue z:ℂ) • f z+(magneticPotential z:ℂ) • f z
  rw [potential_decompose]
  push_cast
  simp only [add_smul,sub_smul,mul_smul]
private theorem native_split:GaussNativeForm.nativeAction+GaussMatterCore.matterAction=
    scalarKinetic+gaugeKinetic+GaussMatterCore.matterAction+centeredAction-(2:ℂ) • vacuumLinearAction+
      vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  unfold GaussNativeForm.nativeAction
  rw [potential_action_decompose]
  abel

theorem actual_composed_native_gaussian(s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:Quad=>sourcePair (composedCompleteCore s t hs ht x f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (composedCompleteCore s t hs ht x g))) γ4 ∧
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore (s+t) (by linarith) x.1 x.2 f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (correctedCompleteCore (s+t) (by linarith) x.1 x.2 g))) (γ.prod γ) ∧
    (∫x:Quad,sourcePair (composedCompleteCore s t hs ht x f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (composedCompleteCore s t hs ht x g)) ∂γ4)=
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore (s+t) (by linarith) x.1 x.2 f)
      ((GaussNativeForm.nativeAction+GaussMatterCore.matterAction) (correctedCompleteCore (s+t) (by linarith) x.1 x.2 g)) ∂γ.prod γ):=by
  have h1:Evolves s t hs ht f g scalarKinetic:=sector_evolves s t hs ht f g scalarKinetic (-2/3) 2
    (fun c hc hf=>actual_complete_profile_scalar_source (s+t) (by linarith) c hc hf f g)
  have h2:Evolves s t hs ht f g gaugeKinetic:=sector_evolves s t hs ht f g gaugeKinetic (2/3) (-2)
    (fun c hc hf=>actual_complete_profile_gauge_source (s+t) (by linarith) c hc hf f g)
  have h3:Evolves s t hs ht f g GaussMatterCore.matterAction:=sector_evolves s t hs ht f g GaussMatterCore.matterAction 0 1
    (fun c hc hf=>actual_profile_complete_matter_pair (s+t) (by linarith) c hc hf f g)
  have h4:Evolves s t hs ht f g centeredAction:=sector_evolves s t hs ht f g centeredAction (4/3) (-2)
    (fun c hc hf=>actual_profile_complete_centered_pair (s+t) (by linarith) c hc hf f g)
  have h5:Evolves s t hs ht f g vacuumLinearAction:=sector_evolves s t hs ht f g vacuumLinearAction (4/3) (-1)
    (fun c hc hf=>actual_profile_complete_vacuum_linear_pair (s+t) (by linarith) c hc hf f g)
  have h6:Evolves s t hs ht f g vacuumConstantAction:=sector_evolves s t hs ht f g vacuumConstantAction (4/3) 0
    (fun c hc hf=>actual_profile_complete_vacuum_constant_pair (s+t) (by linarith) c hc hf f g)
  have h7:Evolves s t hs ht f g scalarSpatialAction:=sector_evolves s t hs ht f g scalarSpatialAction (2/3) 0
    (fun c hc hf=>actual_profile_complete_signed_spatial_pair (s+t) (by linarith) c hc hf f g)
  have h8:Evolves s t hs ht f g magneticAction:=sector_evolves s t hs ht f g magneticAction (2/3) 4
    (fun c hc hf=>actual_profile_complete_magnetic_pair (s+t) (by linarith) c hc hf f g)
  have h5n:=evolves_smul s t hs ht f g (-2) _ h5
  have h12:=evolves_add s t hs ht f g _ _ h1 h2
  have h123:=evolves_add s t hs ht f g _ _ h12 h3
  have h1234:=evolves_add s t hs ht f g _ _ h123 h4
  have h12345:=evolves_add s t hs ht f g _ _ h1234 h5n
  have h123456:=evolves_add s t hs ht f g _ _ h12345 h6
  have h1234567:=evolves_add s t hs ht f g _ _ h123456 h7
  have hh:=evolves_add s t hs ht f g _ _ h1234567 h8
  change Evolves s t hs ht f g (GaussNativeForm.nativeAction+GaussMatterCore.matterAction)
  rw [native_split]
  simpa only [neg_smul,sub_eq_add_neg] using hh


theorem actual_composed_hamiltonian_gaussian(s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:Quad=>sourcePair (composedCompleteCore s t hs ht x f)
      (GaussDiagonalHistory.diagonalAction (composedCompleteCore s t hs ht x g))) γ4 ∧
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore (s+t) (by linarith) x.1 x.2 f)
      (GaussDiagonalHistory.diagonalAction (correctedCompleteCore (s+t) (by linarith) x.1 x.2 g))) (γ.prod γ) ∧
    (∫x:Quad,sourcePair (composedCompleteCore s t hs ht x f)
      (GaussDiagonalHistory.diagonalAction (composedCompleteCore s t hs ht x g)) ∂γ4)=
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore (s+t) (by linarith) x.1 x.2 f)
      (GaussDiagonalHistory.diagonalAction (correctedCompleteCore (s+t) (by linarith) x.1 x.2 g)) ∂γ.prod γ):=by
  have hN:=actual_composed_native_gaussian s t hs ht f g
  have hC:=ClockPhiComposedCoframeGaussianWork.actual_composed_coframe_gaussian s t hs ht f g
  have hO:=ClockPhiHeatCorrectedCoframeWork.actual_corrected_coframe_gaussian (s+t) (add_pos hs ht) f g
  have hCF:Evolves s t hs ht f g GaussCoframeForm.coframeAction:=⟨hC.1,hO.1,hC.2⟩
  have hTotal:=evolves_add s t hs ht f g _ _ hN hCF
  change Evolves s t hs ht f g GaussDiagonalHistory.diagonalAction
  have he:GaussDiagonalHistory.diagonalAction=
      (GaussNativeForm.nativeAction+GaussMatterCore.matterAction)+GaussCoframeForm.coframeAction:=by
    unfold GaussDiagonalHistory.diagonalAction
    abel
  rw [he]
  exact hTotal

theorem actual_corrected_hamiltonian_work_composition(s t:ℝ)(hs:0<s)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:Quad=>sourcePair
      (correctedCompleteCore s hs x.2.1 x.2.2 (correctedCompleteCore t ht x.1.1 x.1.2 f))
      (GaussDiagonalHistory.diagonalAction
        (correctedCompleteCore s hs x.2.1 x.2.2 (correctedCompleteCore t ht x.1.1 x.1.2 g)))) γ4 ∧
    (∫x:Quad,sourcePair
      (correctedCompleteCore s hs x.2.1 x.2.2 (correctedCompleteCore t ht x.1.1 x.1.2 f))
      (GaussDiagonalHistory.diagonalAction
        (correctedCompleteCore s hs x.2.1 x.2.2 (correctedCompleteCore t ht x.1.1 x.1.2 g))) ∂γ4)=
      SourceClockPhiCompleteHeatHamiltonianSource.wholeGaussianHeatHamiltonianPair (s+t) (add_pos hs ht) f g+
        sourcePair (SourceClockPhiCombinedScalePressure.combinedGenerator f)
          (ClockPhiHeatCorrectedCoframeWork.correctedCoframeCovariance (s+t) (add_pos hs ht)
            (SourceClockPhiCombinedScalePressure.combinedGenerator g)):=by
  have h:=actual_composed_hamiltonian_gaussian s t hs ht f g
  have he(x:Quad)(p:QuantumTest):
      correctedCompleteCore s hs x.2.1 x.2.2 (correctedCompleteCore t ht x.1.1 x.1.2 p)=
        composedCompleteCore s t hs ht x p:=
    LinearMap.congr_fun (actual_corrected_complete_composition s t hs ht x) p
  simp_rw [he]
  exact ⟨h.1,h.2.2.trans
    (ClockPhiHeatCorrectedHamiltonianSource.actual_corrected_hamiltonian_gaussian (s+t) (add_pos hs ht) f g).2⟩

end LowEnergy.ClockPhiCorrectedHamiltonianWorkEvolution
