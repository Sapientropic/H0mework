import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatHamiltonianWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiConservativeHeatSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiProfileCoframeReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent GaussCoframeCore
open GaussLiveMomentum ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource
open SourceClockPhiCoframeForwardCore SourceClockPhiCombinedScalePressure
open scoped ContDiff Topology Distributions InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private def forwardScale(t:ℝ)(z:SourceCoordinateSlice):ℝ:=(forwardRatio t z)^(1/3:ℝ)
private theorem scale_pos(t:ℝ)(ht:0≤t)(z:physicalChart):0<forwardScale t z.val:=
  Real.rpow_pos_of_pos (forward_ratio_pos t ht z) _
private abbrev input(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):End:=clockProfileAction c hc hinv 1
private def inputMap(c:SourceCoordinateSlice→ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=combinedMap (c z) z
private theorem volume_euler(z:SourceCoordinateSlice):
    fderiv ℝ GaussNativeEnergy.volume z (euler z)=3*GaussNativeEnergy.volume z:=by
  rw [volume_derivative]
  change z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5=_
  unfold GaussNativeEnergy.volume
  ring
private theorem momentum_component(i:Fin 6)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    momentum i f z word=(-Complex.I)*fderiv ℝ (component word f) z (coframeDirection i):=by
  have h:=congrArg (fun q:GaussDensityCore.ScalarTest=>q z) (component_derivative (coframeDirection i) f word)
  change (-Complex.I)*(GaussCoframeCore.derivative (coframeDirection i) f z word)=_
  exact congrArg (fun x:ℂ=>(-Complex.I)*x) (h.trans (GaussDensityCore.derivative_apply _ _ _))
private theorem forwardGenerator_component(f:QuantumTest)(z:physicalChart)(word:Occupation):
    forwardGenerator f z.val word=(-6:ℂ)*(reciprocalVolume z.val:ℂ)*
      fderiv ℝ (component word f) z.val (euler z.val)-9*(word.card+3:ℂ)*(reciprocalVolume z.val:ℂ)*f z.val word:=by
  change (-9*Complex.I)*((reciprocalVolume z.val:ℂ)*dilation f z.val word)+9*((reciprocalVolume z.val:ℂ)*f z.val word)=_
  rw [dilation_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem input_point(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (f:QuantumTest)(z:SourceCoordinateSlice):
    input c hc hinv f z=(Real.exp ((25/2:ℝ)*c z):ℂ) • f (inputMap c z):=by
  change (Real.exp ((25/2:ℝ)*(1*c z)):ℂ) • f (combinedMap (1*c z) z)=_
  simp only [one_mul,inputMap]
private theorem coefficient_line(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(z:physicalChart)(v:SourceCoordinateSlice):
    HasDerivAt (fun s:ℝ=>c (z.val+s • v)) (fderiv ℝ c z.val v) 0:=by
  have hx:HasDerivAt (fun s:ℝ=>z.val+s • v) v 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val
  exact ((hc z).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
private theorem inputMap_line_jet(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(z:physicalChart)
    (v:SourceCoordinateSlice)(hv:v.2=0):
    HasDerivAt (fun s:ℝ=>inputMap c (z.val+s • v))
      (v+(fderiv ℝ c z.val v) •
        (SourceScalarVirialBulk.phiEuler (inputMap c z.val)-SourceGaugeRadialCurrent.gaugeEuler (inputMap c z.val))) 0:=by
  let value:=c z.val
  let dc:=fderiv ℝ c z.val v
  have hline:=coefficient_line c hc z v
  have he:=hline.exp
  have hn:=hline.neg.exp
  have hco:HasDerivAt (fun s:ℝ=>z.val.1+s • v.1) v.1 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v.1).const_add z.val.1
  have h:=hco.prodMk (((he.smul_const (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)).sub_const
    SourceScalarVirialBulk.vacuumSlice).prodMk (hn.smul_const z.val.2.2))
  have hp:c (z.val+(0:ℝ) • v)=value:=by simp [value]
  simp only [Pi.neg_apply,hp] at h
  have hd:(v.1,(Real.exp value*dc) • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice),(Real.exp (-value)*(-dc)) • z.val.2.2)=
      v+dc • (SourceScalarVirialBulk.phiEuler (inputMap c z.val)-SourceGaugeRadialCurrent.gaugeEuler (inputMap c z.val)):=by
    simp only [inputMap,combinedMap_apply,SourceScalarVirialBulk.phiEuler,SourceGaugeRadialCurrent.gaugeEuler]
    apply Prod.ext
    · simp
    rw [Prod.snd_add,hv,zero_add]
    apply Prod.ext
    · change (Real.exp value*dc) • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)=
        dc • (SourceScalarVirialBulk.vacuumSlice+(Real.exp value • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)-SourceScalarVirialBulk.vacuumSlice)-0)
      module
    · change (Real.exp (-value)*(-dc)) • z.val.2.2=dc • (0-Real.exp (-value) • z.val.2.2)
      module
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  have hsv(s:ℝ):s • v=(s • v.1,(0:Slice)):=by
    apply Prod.ext
    · rfl
    · change s • v.2=0
      rw [hv,smul_zero]
  exact Filter.Eventually.of_forall (fun s=>by
    simp only [inputMap,combinedMap_apply,hsv,Prod.fst_add,Prod.snd_add,add_zero])
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
private theorem input_coframe_derivative(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(f:QuantumTest)(z:physicalChart)
    (v:SourceCoordinateSlice)(hv:v.2=0)(word:Occupation):
    fderiv ℝ (component word (input c hc hinv f)) z.val v=
      (Real.exp ((25/2:ℝ)*c z.val):ℂ)*
        (fderiv ℝ (component word f) (inputMap c z.val) v+
          (fderiv ℝ c z.val v:ℝ)*
            combinedGenerator f (inputMap c z.val) word):=by
  have hline:=coefficient_line c hc z v
  have hx:=inputMap_line_jet c hc z v hv
  have hz:HasDerivAt (fun s:ℝ=>z.val+s • v) v 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val
  have hf:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=inputMap c z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hl:=(((component word (input c hc hinv f)).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hz (by simp)
  have he:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hline.const_mul (25/2:ℝ)).exp)
  have hh:=he.mul hf
  have heq:(fun s:ℝ=>(Real.exp ((25/2:ℝ)*c (z.val+s • v)):ℂ)*
      f (inputMap c (z.val+s • v)) word)=
      fun s:ℝ=>input c hc hinv f (z.val+s • v) word:=by
    funext s
    rw [input_point]
    rfl
  have hcomp(q:QuantumTest)(x:SourceCoordinateSlice):(component word q) x=q x word:=rfl
  dsimp only [Function.comp_def,Complex.ofRealCLM_apply,Pi.mul_apply] at hh hl
  simp only [hcomp] at hh hl
  change HasDerivAt (fun s:ℝ=>(Real.exp ((25/2:ℝ)*c (z.val+s • v)):ℂ)*
    f (inputMap c (z.val+s • v)) word) _ 0 at hh
  rw [heq] at hh
  have h:=hl.unique hh
  rw [h,combined_component]
  simp only [zero_smul,add_zero,map_add,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ),
    RCLike.ofReal_eq_complex_ofReal,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

private theorem inputMap_chart(c:SourceCoordinateSlice→ℝ)(z:physicalChart):inputMap c z.val∈physicalChart:=by
  have hg:=SourceGaugeScaleTransport.scale_chart_iff (Real.exp (-c z.val))
    (Real.exp_pos _) (SourceScalarAffineScaleTransport.scaleEquiv (c z.val) z.val)
  have hp:=SourceScalarAffineScaleTransport.scale_chart_iff (c z.val) z.val
  exact (hg.trans hp).mpr z.property
private theorem input_momentum(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (f:QuantumTest)(z:physicalChart)(i:Fin 6)(word:Occupation):
    momentum i (input c hc hinv f) z.val word=
      (Real.exp ((25/2:ℝ)*c z.val):ℂ)*
        (momentum i f (inputMap c z.val) word-
          Complex.I*(fderiv ℝ c z.val (coframeDirection i):ℝ)*combinedGenerator f (inputMap c z.val) word):=by
  rw [momentum_component,input_coframe_derivative c hc hinv f z (coframeDirection i) rfl,momentum_component]
  push_cast
  ring
private theorem input_forwardGenerator(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (f:QuantumTest)(z:physicalChart)(word:Occupation):
    forwardGenerator (input c hc hinv f) z.val word=
      (Real.exp ((25/2:ℝ)*c z.val):ℂ)*
        (forwardGenerator f (inputMap c z.val) word-
          6*(reciprocalVolume z.val:ℂ)*(fderiv ℝ c z.val (euler z.val):ℝ)*
            combinedGenerator f (inputMap c z.val) word):=by
  let zi:physicalChart:=⟨inputMap c z.val,inputMap_chart c z⟩
  have hu:reciprocalVolume zi.val=reciprocalVolume z.val:=rfl
  have he:euler zi.val=euler z.val:=rfl
  rw [forwardGenerator_component,input_coframe_derivative c hc hinv f z (euler z.val) rfl,input_point]
  rw [forwardGenerator_component f zi,hu,he]
  simp only [PiLp.smul_apply,smul_eq_mul]
  push_cast
  ring
private theorem driftClock_component(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    SourceClockPhiMatchedDiffusionSource.driftClock f z word=
      (reciprocalVolume z:ℂ)*combinedGenerator f z word-(1/3:ℂ)*forwardGenerator f z word:=by
  have h:SourceClockPhiMatchedDiffusionSource.driftClock=
      inverseVolumeAction*combinedGenerator-(1/3:ℂ) • forwardGenerator:=by
    rw [forwardGenerator_original]
    unfold SourceClockPhiMatchedDiffusionSource.driftClock SourceClockPhiNativeMatchedSource.matchedColumn
    module
  rw [h]
  rfl
private theorem gain_line(t:ℝ)(ht:0<t)(z:physicalChart)(v:SourceCoordinateSlice):
    HasDerivAt (fun s:ℝ=>SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) (z.val+s • v))
      (-3*t*reciprocalVolume z.val*SourceClockPhiForwardNativeReturn.forwardU t z.val*
        SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val*
          fderiv ℝ GaussNativeEnergy.volume z.val v) 0:=by
  have hx:HasDerivAt (fun s:ℝ=>z.val+s • v) v 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val
  have hv:HasDerivAt (fun s:ℝ=>GaussNativeEnergy.volume (z.val+s • v))
      (fderiv ℝ GaussNativeEnergy.volume z.val v) 0:=
    ((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
      (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hr:HasDerivAt (fun s:ℝ=>forwardRatio t (z.val+s • v))
      (-18*t/GaussNativeEnergy.volume z.val^2*fderiv ℝ GaussNativeEnergy.volume z.val v) 0:=by
    have h:=(hv.add_const (18*t)).div hv (by simpa using (volume_pos z).ne')
    apply h.congr_deriv
    simp only [zero_smul,add_zero]
    field_simp [(volume_pos z).ne']
    ring
  have h:=hr.rpow_const (p:=(1/6:ℝ)) (Or.inl (by simpa using (forward_ratio_pos t ht.le z).ne'))
  change HasDerivAt (fun s:ℝ=>forwardRatio ((Real.sqrt t)^2) (z.val+s • v)^(1/6:ℝ)) _ 0
  rw [Real.sq_sqrt ht.le]
  apply h.congr_deriv
  simp only [zero_smul,add_zero]
  rw [Real.rpow_sub (forward_ratio_pos t ht.le z),Real.rpow_one]
  unfold SourceClockPhiActualCovarianceStep.gainProfile
  rw [Real.sq_sqrt ht.le]
  unfold reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU forwardRatio
  field_simp [(volume_pos z).ne',show GaussNativeEnergy.volume z.val+18*t≠0 by linarith [volume_pos z]]
  ring
private theorem gain_component_derivative(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart)
    (v:SourceCoordinateSlice)(word:Occupation):
    fderiv ℝ (component word (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)) z.val v=
      (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*
        (fderiv ℝ (component word f) z.val v-
          (3*t*reciprocalVolume z.val*SourceClockPhiForwardNativeReturn.forwardU t z.val*
            fderiv ℝ GaussNativeEnergy.volume z.val v:ℝ)*f z.val word):=by
  have hx:HasDerivAt (fun s:ℝ=>z.val+s • v) v 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val
  have hf:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hl:=(((component word (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hg:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (gain_line t ht z v)
  have hh:=hg.mul hf
  change HasDerivAt (fun s:ℝ=>SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f (z.val+s • v) word) _ 0 at hh
  have he:=hl.unique hh
  rw [he]
  simp only [Function.comp_def,zero_smul,add_zero,Complex.ofRealCLM_apply,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  rw [show (component word f) z.val=f z.val word from rfl]
  ring
private theorem gain_momentum(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart)(i:Fin 6)(word:Occupation):
    GaussCoframeCore.momentum i (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f) z.val word=
      (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*
        (GaussCoframeCore.momentum i f z.val word+
          (3*Complex.I*t*(reciprocalVolume z.val:ℂ)*(SourceClockPhiForwardNativeReturn.forwardU t z.val:ℂ)*
            (volumeGradient z.val i:ℂ))*f z.val word):=by
  rw [momentum_component,gain_component_derivative t ht,volume_coordinate_derivative,momentum_component]
  push_cast
  ring
private theorem gain_combined(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    combinedGenerator (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f) z.val word=
      (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*combinedGenerator f z.val word:=by
  rw [combined_component,gain_component_derivative t ht,combined_component]
  have hv:fderiv ℝ GaussNativeEnergy.volume z.val
      (SourceScalarVirialBulk.phiEuler z.val-SourceGaugeRadialCurrent.gaugeEuler z.val)=0:=by
    rw [volume_derivative]
    simp only [SourceScalarVirialBulk.phiEuler,SourceGaugeRadialCurrent.gaugeEuler,Prod.fst_sub,sub_self,PiLp.zero_apply,zero_mul,mul_zero,add_zero]
  rw [hv]
  change _+(25/2:ℂ)*((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*f z.val word)=_
  push_cast
  ring
private theorem gain_driftClock(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    SourceClockPhiMatchedDiffusionSource.driftClock (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f) z.val word=
      (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*
        (SourceClockPhiMatchedDiffusionSource.driftClock f z.val word-
          ((reciprocalVolume z.val-SourceClockPhiForwardNativeReturn.forwardU t z.val:ℝ):ℂ)*f z.val word):=by
  rw [driftClock_component,gain_combined t ht,forwardGenerator_component,gain_component_derivative t ht,
    volume_euler,driftClock_component,forwardGenerator_component]
  change (reciprocalVolume z.val:ℂ)*_-(1/3:ℂ)*((-6:ℂ)*(reciprocalVolume z.val:ℂ)*_-
      9*(word.card+3:ℂ)*(reciprocalVolume z.val:ℂ)*
        ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*f z.val word))=_
  unfold reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU
  push_cast
  have hv:(GaussNativeEnergy.volume z.val:ℂ)≠0:=by exact_mod_cast (volume_pos z).ne'
  have hw:(GaussNativeEnergy.volume z.val+18*t:ℂ)≠0:=by exact_mod_cast (show GaussNativeEnergy.volume z.val+18*t≠0 by linarith [volume_pos z])
  have hw':(t:ℂ)*18+GaussNativeEnergy.volume z.val≠0:=by
    convert hw using 1
    ring
  ring_nf
  field_simp [hv,hw,hw']
  have hi:((t:ℂ)*18+GaussNativeEnergy.volume z.val)*((t:ℂ)*18+GaussNativeEnergy.volume z.val)⁻¹=1:=mul_inv_cancel₀ hw'
  linear_combination (norm:=ring) -(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*(f z.val word)*hi
private theorem matchedTester_component(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    SourceClockPhiNativeMatchedSource.matchedTester f z word=
      SourceClockPhiMatchedDiffusionSource.driftClock f z word-(reciprocalVolume z:ℂ)*f z word:=by
  change SourceClockPhiNativeMatchedSource.matchedColumn f z word+(2:ℂ)*((reciprocalVolume z:ℂ)*f z word)=
    (SourceClockPhiNativeMatchedSource.matchedColumn f z word+(3:ℂ)*((reciprocalVolume z:ℂ)*f z word))-(reciprocalVolume z:ℂ)*f z word
  ring

def profileCompleteCore(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z):End:=
  sourceForwardCore t ht.le*clockProfileAction c hc hinv 1*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
def profileNoiseColumn(t:ℝ)(c:SourceCoordinateSlice→ℝ)(i:Fin 6)(z:SourceCoordinateSlice):ℝ:=
  3*t*reciprocalVolume z^2*volumeGradient z i-fderiv ℝ c z (coframeDirection i)-
    6*t*reciprocalVolume z^2*volumeGradient z i*fderiv ℝ c z (euler z)
private theorem complete_point(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (f:QuantumTest)(z:physicalChart)(word:Occupation):
    profileCompleteCore t ht c hc hinv f (forwardPoint t z.val) word=
      (Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*
        ((Real.exp ((25/2:ℝ)*c z.val):ℂ)*
          ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) (inputMap c z.val):ℂ)*f (inputMap c z.val) word)):=by
  change sourceForwardCore t ht.le (input c hc hinv (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)) _ _=_
  rw [forwardCore_apply,input_point]
  rfl
private theorem gain_forwardGenerator(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    forwardGenerator (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f) z.val word=
      (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*
        (forwardGenerator f z.val word+3*((reciprocalVolume z.val-SourceClockPhiForwardNativeReturn.forwardU t z.val:ℝ):ℂ)*f z.val word):=by
  have h:=gain_driftClock t ht f z word
  rw [driftClock_component,gain_combined t ht,driftClock_component] at h
  linear_combination (norm:=ring) -(3:ℂ)*h

theorem actual_profile_complete_momentum_point(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (i:Fin 6)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    momentum i (profileCompleteCore t ht c hc hinv f) (forwardPoint t z.val) word=
      (((forwardScale t z.val)⁻¹:ℝ):ℂ)*
        (profileCompleteCore t ht c hc hinv (momentum i f) (forwardPoint t z.val) word-
          (3*Complex.I*t*(reciprocalVolume z.val:ℂ)*(volumeGradient z.val i:ℂ))*
            profileCompleteCore t ht c hc hinv (SourceClockPhiNativeMatchedSource.matchedTester f) (forwardPoint t z.val) word+
          (Complex.I*(profileNoiseColumn t c i z.val:ℂ))*
            profileCompleteCore t ht c hc hinv (combinedGenerator f) (forwardPoint t z.val) word):=by
  let zi:physicalChart:=⟨inputMap c z.val,inputMap_chart c z⟩
  have h:=ClockPhiHeatHamiltonianWork.actual_forward_momentum_point t ht.le i
    (input c hc hinv (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)) z word
  change momentum i (profileCompleteCore t ht c hc hinv f) (forwardPoint t z.val) word=
    (((forwardRatio t z.val)^(-((word.card+3:ℝ)/2)):ℝ):ℂ)*(((forwardScale t z.val)⁻¹:ℝ):ℂ)*
      (momentum i (input c hc hinv (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)) z.val word+
        Complex.I*t*(reciprocalVolume z.val:ℂ)*(volumeGradient z.val i:ℂ)*
          forwardGenerator (input c hc hinv (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)) z.val word) at h
  rw [input_momentum,input_forwardGenerator] at h
  rw [h,gain_momentum t ht f zi,gain_forwardGenerator t ht f zi,gain_combined t ht f zi]
  rw [complete_point,complete_point,complete_point,matchedTester_component,driftClock_component]
  have hu:reciprocalVolume zi.val=reciprocalVolume z.val:=rfl
  have hv:volumeGradient zi.val i=volumeGradient z.val i:=rfl
  rw [hu,hv]
  simp only [Real.rpow_eq_pow]
  unfold forwardScale at *
  unfold profileNoiseColumn
  push_cast
  ring

private theorem gradient_same(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (x y:physicalChart)(hxy:x.val.1=y.val.1)(v:SourceCoordinateSlice):
    fderiv ℝ c x.val v=fderiv ℝ c y.val v:=by
  have hx:=coefficient_line c hc x v
  have hy:=coefficient_line c hc y v
  have he:(fun a:ℝ=>c (x.val+a • v))=(fun a:ℝ=>c (y.val+a • v)):=by
    funext a
    apply hfirst
    simp only [Prod.fst_add,hxy]
  rw [he] at hx
  exact hx.unique hy
private theorem noiseColumn_smooth(t:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(i:Fin 6)(z:physicalChart):
    ContDiffAt ℝ ∞ (profileNoiseColumn t c i) z.val:=by
  have hd:ContDiffAt ℝ ∞ (fderiv ℝ c) z.val:=(hc z).fderiv_right (by simp)
  have he:ContDiff ℝ ∞ euler:=by unfold euler;fun_prop
  have hv:ContDiff ℝ ∞ (fun x=>volumeGradient x i):=by
    fin_cases i <;> dsimp [volumeGradient] <;> fun_prop
  exact (((contDiffAt_const.mul contDiffAt_const).mul ((reciprocal_volume_smooth z).pow 2)).mul hv.contDiffAt).sub
    (hd.clm_apply contDiffAt_const) |>.sub
      (((((contDiffAt_const.mul contDiffAt_const).mul ((reciprocal_volume_smooth z).pow 2)).mul hv.contDiffAt)).mul
        (hd.clm_apply he.contDiffAt))
private theorem radialRate_smooth(t:ℝ)(ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(forwardScale t x)⁻¹) z.val:=by
  have hr:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact (hr.rpow_const_of_ne (p:=(1/3:ℝ)) (forward_ratio_pos t ht.le z).ne').inv (scale_pos t ht.le z).ne'
private theorem volumeGradient_smooth(i:Fin 6):ContDiff ℝ ∞ (fun z=>volumeGradient z i):=by
  fin_cases i <;> dsimp [volumeGradient] <;> fun_prop
private def radialRateAction(t:ℝ)(ht:0<t):End:=multiply (fun z=>(forwardScale t z)⁻¹) (radialRate_smooth t ht)
private def currentColumnAction(i:Fin 6):End:=multiply (fun z=>reciprocalVolume z*volumeGradient z i)
  (fun z=>(reciprocal_volume_smooth z).mul (volumeGradient_smooth i).contDiffAt)
private def profileNoiseColumnAction(t:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(i:Fin 6):End:=
  multiply (profileNoiseColumn t c i) (noiseColumn_smooth t c hc i)
def profileCoframeRow(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(i:Fin 6):End:=
  radialRateAction t ht*(momentum i-(3*Complex.I*t:ℂ) •
    (currentColumnAction i*SourceClockPhiNativeMatchedSource.matchedTester)+
    Complex.I • (profileNoiseColumnAction t c hc i*combinedGenerator))
private theorem row_point(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(i:Fin 6)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    profileCoframeRow t ht c hc i f z word=(((forwardScale t z)⁻¹:ℝ):ℂ)*
      (momentum i f z word-(3*Complex.I*t:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*
        SourceClockPhiNativeMatchedSource.matchedTester f z word)+
      Complex.I*((profileNoiseColumn t c i z:ℂ)*combinedGenerator f z word)):=rfl
private theorem complete_above(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (f:QuantumTest)(z:SourceCoordinateSlice)(hz:z∈tsupport (profileCompleteCore t ht c hc hinv f)):
    18*t<GaussNativeEnergy.volume z:=by
  change z∈tsupport (sourceForwardCore t ht.le (input c hc hinv
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f))) at hz
  obtain ⟨x,hx,rfl⟩:=forward_support t ht.le _ hz
  exact forward_above t ht.le ⟨x,(input c hc hinv
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)).tsupport_subset hx⟩
private theorem momentum_below(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (f:QuantumTest)(z:SourceCoordinateSlice)(hz:¬18*t<GaussNativeEnergy.volume z)(i:Fin 6):
    momentum i (profileCompleteCore t ht c hc hinv f) z=0:=by
  have hn:z∉tsupport (profileCompleteCore t ht c hc hinv f):=fun h=>hz (complete_above t ht c hc hinv f z h)
  change (-Complex.I) • GaussCoframeCore.derivative (coframeDirection i) (profileCompleteCore t ht c hc hinv f) z=0
  rw [GaussCoframeCore.derivative_apply,fderiv_of_notMem_tsupport ℝ hn]
  simp only [zero_apply,smul_zero]

theorem actual_profile_complete_coframe_return(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(i:Fin 6):
    momentum i*profileCompleteCore t ht c hc hinv=
      profileCompleteCore t ht c hc hinv*profileCoframeRow t ht c hc i:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  by_cases hx:x∈physicalChart
  · by_cases ha:18*t<GaussNativeEnergy.volume x
    · let z:physicalChart:=⟨backwardPoint t x,backward_chart t ht.le ⟨x,hx⟩ ha⟩
      have hz:forwardPoint t z.val=x:=forward_backward t ht.le x ha
      rw [←hz]
      apply PiLp.ext
      intro word
      change momentum i (profileCompleteCore t ht c hc hinv f) (forwardPoint t z.val) word=
        profileCompleteCore t ht c hc hinv (profileCoframeRow t ht c hc i f) (forwardPoint t z.val) word
      rw [actual_profile_complete_momentum_point,complete_point,complete_point,complete_point,complete_point,row_point]
      let zi:physicalChart:=⟨inputMap c z.val,inputMap_chart c z⟩
      have hs:forwardScale t (inputMap c z.val)=forwardScale t z.val:=rfl
      have hu:reciprocalVolume (inputMap c z.val)=reciprocalVolume z.val:=rfl
      have hv:volumeGradient (inputMap c z.val) i=volumeGradient z.val i:=rfl
      have he:euler (inputMap c z.val)=euler z.val:=rfl
      have hi:=gradient_same c hc hfirst zi z rfl (coframeDirection i)
      have hE:=gradient_same c hc hfirst zi z rfl (euler z.val)
      have hb:profileNoiseColumn t c i (inputMap c z.val)=profileNoiseColumn t c i z.val:=by
        unfold profileNoiseColumn
        rw [hu,hv,he,hi,hE]
      rw [hs,hu,hv,hb]
      push_cast
      ring
    · change momentum i (profileCompleteCore t ht c hc hinv f) x=_
      rw [momentum_below t ht c hc hinv f x ha i]
      exact (image_eq_zero_of_notMem_tsupport (fun h=>ha
        (complete_above t ht c hc hinv (profileCoframeRow t ht c hc i f) x h))).symm
  · have h0(q:QuantumTest):q x=0:=image_eq_zero_of_notMem_tsupport (fun h=>hx (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private def forwardMetricAction(t:ℝ)(ht:0<t)(i j:Fin 6):End:=
  multiply (fun x=>GaussCoframeKinetic.coefficient i j (forwardPoint t x))
    (fun z=>by
      simpa only [Function.comp_def] using! (GaussCoframeKinetic.coefficient_smooth i j
        ⟨forwardPoint t z.val,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))
private theorem input_metric(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(i j:Fin 6):
    Commute (input c hc hinv) (forwardMetricAction t ht i j):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change input c hc hinv (forwardMetricAction t ht i j f) z word=
    (GaussCoframeKinetic.coefficient i j (forwardPoint t z):ℂ)*input c hc hinv f z word
  rw [input_point,input_point]
  change (Real.exp ((25/2:ℝ)*c z):ℂ)*
      ((GaussCoframeKinetic.coefficient i j (forwardPoint t (inputMap c z)):ℂ)*f (inputMap c z) word)=_
  have hc:GaussCoframeKinetic.coefficient i j (forwardPoint t (inputMap c z))=
      GaussCoframeKinetic.coefficient i j (forwardPoint t z):=rfl
  rw [hc]
  simp only [PiLp.smul_apply,smul_eq_mul]
  ring
private theorem gain_metric(t:ℝ)(ht:0<t)(i j:Fin 6):
    Commute (forwardMetricAction t ht i j) (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (_:ℂ) • ((_ :ℂ) • f z)=(_ :ℂ) • ((_ :ℂ) • f z)
  exact smul_comm _ _ _
private theorem metric_complete_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(i j:Fin 6):
    SourceCoframeCovariantAction.metricAction i j*profileCompleteCore t ht c hc hinv=
      profileCompleteCore t ht c hc hinv*forwardMetricAction t ht i j:=by
  have hJ:=SourceClockPhiForwardGeneratorTransport.actual_forward_multiplier_transport t ht.le
    (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)
  change SourceCoframeCovariantAction.metricAction i j*sourceForwardCore t ht.le=
    sourceForwardCore t ht.le*forwardMetricAction t ht i j at hJ
  rw [profileCompleteCore]
  calc
    _=(SourceCoframeCovariantAction.metricAction i j*sourceForwardCore t ht.le)*
        input c hc hinv*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by noncomm_ring
    _=(sourceForwardCore t ht.le*forwardMetricAction t ht i j)*
        input c hc hinv*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by rw [hJ]
    _=(sourceForwardCore t ht.le*input c hc hinv*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t))*
        forwardMetricAction t ht i j:=by
      have hN:forwardMetricAction t ht i j*input c hc hinv=input c hc hinv*forwardMetricAction t ht i j:=
        (input_metric t ht c hc hinv i j).eq.symm
      have hG:forwardMetricAction t ht i j*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)=
        SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)*forwardMetricAction t ht i j:=(gain_metric t ht i j).eq
      calc
        _=sourceForwardCore t ht.le*(forwardMetricAction t ht i j*input c hc hinv)*
          SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by noncomm_ring
        _=sourceForwardCore t ht.le*(input c hc hinv*forwardMetricAction t ht i j)*
          SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by rw [hN]
        _=(sourceForwardCore t ht.le*input c hc hinv)*
          (forwardMetricAction t ht i j*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by noncomm_ring
        _=(sourceForwardCore t ht.le*input c hc hinv)*
          (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)*forwardMetricAction t ht i j):=by rw [hG]
        _=_:=by noncomm_ring
private theorem gain_squared_metric(t:ℝ)(ht:0<t)(i j:Fin 6):
    SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)*
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)*forwardMetricAction t ht i j)=
        SourceCoframeCovariantAction.metricAction i j:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hr:0<forwardRatio t z:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hs:0<forwardScale t z:=scale_pos t ht.le ⟨z,hz⟩
    have hg:SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z^2=forwardScale t z:=by
      unfold SourceClockPhiActualCovarianceStep.gainProfile forwardScale
      rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
      congr 1
      norm_num
    have hc:GaussCoframeKinetic.coefficient i j (forwardPoint t z)=
        (forwardScale t z)⁻¹*GaussCoframeKinetic.coefficient i j z:=
      SourceKineticScale.coframe_coefficient_scale _ hs.ne' z i j
    apply PiLp.ext
    intro word
    change (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ)*
      ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ)*
        ((GaussCoframeKinetic.coefficient i j (forwardPoint t z):ℂ)*f z word))=
      (GaussCoframeKinetic.coefficient i j z:ℂ)*f z word
    rw [hc]
    have hg':(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ)^2=(forwardScale t z:ℂ):=by exact_mod_cast hg
    have hs':(forwardScale t z:ℂ)≠0:=by exact_mod_cast hs.ne'
    push_cast
    field_simp [hs']
    linear_combination (norm:=ring) (GaussCoframeKinetic.coefficient i j z:ℂ)*(f z word)*hg'
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

theorem actual_profile_complete_metric_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)(i j:Fin 6)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc hinv f)
      (SourceCoframeCovariantAction.metricAction i j (profileCompleteCore t ht c hc hinv g))=
        sourcePair f (SourceCoframeCovariantAction.metricAction i j g):=by
  have h:=LinearMap.congr_fun (metric_complete_transport t ht c hc hinv i j) g
  change SourceCoframeCovariantAction.metricAction i j (profileCompleteCore t ht c hc hinv g)=
    profileCompleteCore t ht c hc hinv (forwardMetricAction t ht i j g) at h
  rw [h]
  change sourcePair (sourceForwardCore t ht.le (input c hc hinv (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)))
    (sourceForwardCore t ht.le (input c hc hinv (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (forwardMetricAction t ht i j g))))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair,clockProfileAction_pair]
  have hG(p q:QuantumTest):sourcePair p (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) q)=
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) p) q:=multiply_pair _ _ p q
  rw [←hG]
  have he:=LinearMap.congr_fun (gain_squared_metric t ht i j) g
  exact congrArg (sourcePair f) he

theorem actual_profile_complete_kinetic_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hinv:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc hinv f)
      (GaussCoframeKinetic.kinetic (profileCompleteCore t ht c hc hinv g))=
      ∑i:Fin 6,∑j:Fin 6,sourcePair (profileCoframeRow t ht c hc i f)
        (SourceCoframeCovariantAction.metricAction i j (profileCoframeRow t ht c hc j g)):=by
  simp only [GaussCoframeKinetic.kinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change sourcePair _ (GaussCoframeCore.adjoint i (SourceCoframeCovariantAction.metricAction i j
    (GaussCoframeCore.momentum j (profileCompleteCore t ht c hc hinv g))))=_
  rw [GaussCoframeKinetic.adjoint_pair]
  have hi:=LinearMap.congr_fun (actual_profile_complete_coframe_return t ht c hc hinv hfirst i) f
  have hj:=LinearMap.congr_fun (actual_profile_complete_coframe_return t ht c hc hinv hfirst j) g
  change GaussCoframeCore.momentum i (profileCompleteCore t ht c hc hinv f)=
    profileCompleteCore t ht c hc hinv (profileCoframeRow t ht c hc i f) at hi
  change GaussCoframeCore.momentum j (profileCompleteCore t ht c hc hinv g)=
    profileCompleteCore t ht c hc hinv (profileCoframeRow t ht c hc j g) at hj
  rw [hi,hj]
  exact actual_profile_complete_metric_pair t ht c hc hinv i j _ _

end LowEnergy.SourceClockPhiProfileCoframeReturn
