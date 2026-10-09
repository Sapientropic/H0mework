import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatComparisonWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseHamiltonian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatGainPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiHeatHamiltonianWork
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent GaussCoframeCore
open GaussLiveMomentum
open ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource ClockPhiHeatComparisonWork SourceClockPhiCombinedScalePressure
open SourceClockPhiCoframeForwardCore
open scoped ContDiff Topology Distributions InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private def forwardScale(t:ℝ)(z:SourceCoordinateSlice):ℝ:=(forwardRatio t z)^(1/3:ℝ)
private def inverseColumn(t:ℝ)(z:SourceCoordinateSlice)(i:Fin 6):SourceCoordinateSlice:=
  (forwardScale t z)⁻¹ • (coframeDirection i+
    (6*t/(GaussNativeEnergy.volume z)^2*volumeGradient z i) • euler z)
private theorem volume_euler(z:SourceCoordinateSlice):
    fderiv ℝ GaussNativeEnergy.volume z (euler z)=3*GaussNativeEnergy.volume z:=by
  rw [volume_derivative]
  change z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5=_
  unfold GaussNativeEnergy.volume
  ring
private theorem scale_pos(t:ℝ)(ht:0≤t)(z:physicalChart):0<forwardScale t z.val:=
  Real.rpow_pos_of_pos (forward_ratio_pos t ht z) _
private theorem scale_cube(t:ℝ)(ht:0≤t)(z:physicalChart):
    forwardScale t z.val^3=forwardRatio t z.val:=cube_root_cube _ (forward_ratio_pos t ht z).le
private theorem inverseColumn_volume(t:ℝ)(_ht:0≤t)(z:physicalChart)(i:Fin 6):
    fderiv ℝ GaussNativeEnergy.volume z.val (inverseColumn t z.val i)=
      (forwardScale t z.val)⁻¹*forwardRatio t z.val*volumeGradient z.val i:=by
  simp only [inverseColumn,map_smul,map_add,volume_coordinate_derivative,volume_euler,smul_eq_mul]
  unfold forwardRatio
  field_simp [(volume_pos z).ne']
  ring
private theorem forward_inverseColumn(t:ℝ)(ht:0≤t)(z:physicalChart)(i:Fin 6):
    forwardPointDerivative t z.val (inverseColumn t z.val i)=coframeDirection i:=by
  have ha:forwardScale t z.val≠0:=(scale_pos t ht z).ne'
  have he:forwardScale t z.val*(forwardScale t z.val)⁻¹=1:=mul_inv_cancel₀ ha
  have hc:6*t/GaussNativeEnergy.volume z.val^2*volumeGradient z.val i+
      (-6*t/(GaussNativeEnergy.volume z.val^2*(forwardScale t z.val)^2))*
        ((forwardScale t z.val)⁻¹*forwardRatio t z.val*volumeGradient z.val i)=0:=by
    rw [←scale_cube t ht z]
    field_simp [ha,(volume_pos z).ne']
    ring
  simp only [forwardPointDerivative,ContinuousLinearMap.prod_apply,
    add_apply,smul_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',ContinuousLinearMap.smulRight_apply,
    inverseColumn_volume t ht z i]
  change (forwardScale t z.val • (inverseColumn t z.val i).1+
      ((-6*t/(GaussNativeEnergy.volume z.val^2*(forwardScale t z.val)^2))*
        ((forwardScale t z.val)⁻¹*forwardRatio t z.val*volumeGradient z.val i)) • z.val.1,
      (inverseColumn t z.val i).2)=coframeDirection i
  have hf:(inverseColumn t z.val i).1=(forwardScale t z.val)⁻¹ •
      (EuclideanSpace.single i 1+(6*t/GaussNativeEnergy.volume z.val^2*volumeGradient z.val i) • z.val.1):=rfl
  have hs:(inverseColumn t z.val i).2=0:=by
    change (forwardScale t z.val)⁻¹ • ((0:Slice)+(6*t/GaussNativeEnergy.volume z.val^2*volumeGradient z.val i) • 0)=0
    simp only [smul_zero,add_zero]
  rw [hf,hs,smul_smul,he,one_smul]
  change ((EuclideanSpace.single i 1+_ • z.val.1)+_ • z.val.1,(0:Slice))=(EuclideanSpace.single i 1,0)
  rw [add_assoc,←add_smul,hc,zero_smul,add_zero]
private theorem forward_ratio_line(t:ℝ)(ht:0≤t)(z:physicalChart)(i:Fin 6):
    HasDerivAt (fun s:ℝ=>forwardRatio t (z.val+s • inverseColumn t z.val i))
      ((-18*t/GaussNativeEnergy.volume z.val^2)*
        ((forwardScale t z.val)⁻¹*forwardRatio t z.val*volumeGradient z.val i)) 0:=by
  have hx:HasDerivAt (fun s:ℝ=>z.val+s • inverseColumn t z.val i) (inverseColumn t z.val i) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (inverseColumn t z.val i)).const_add z.val
  have hv:=((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  rw [inverseColumn_volume t ht z i] at hv
  have h:=(hv.add_const (18*t)).div hv (by simpa using (volume_pos z).ne')
  apply h.congr_deriv
  simp only [Function.comp_def,zero_smul,add_zero]
  field_simp [(volume_pos z).ne']
  ring
private theorem amplitude_line(t:ℝ)(ht:0≤t)(z:physicalChart)(i:Fin 6)(word:Occupation):
    HasDerivAt (fun s:ℝ=>(forwardRatio t (z.val+s • inverseColumn t z.val i))^(-((word.card+3:ℝ)/2)))
      ((forwardRatio t z.val)^(-((word.card+3:ℝ)/2))*
        (9*t*(word.card+3:ℝ)/GaussNativeEnergy.volume z.val^2*
          (forwardScale t z.val)⁻¹*volumeGradient z.val i)) 0:=by
  have h:=(forward_ratio_line t ht z i).rpow_const
    (Or.inl (by simpa using (forward_ratio_pos t ht z).ne')) (p:=-((word.card+3:ℝ)/2))
  apply h.congr_deriv
  simp only [zero_smul,add_zero]
  rw [Real.rpow_sub (forward_ratio_pos t ht z),Real.rpow_one]
  field_simp [(forward_ratio_pos t ht z).ne']
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

theorem actual_forward_momentum_point(t:ℝ)(ht:0≤t)(i:Fin 6)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    momentum i (sourceForwardCore t ht f) (forwardPoint t z.val) word=
      (((forwardRatio t z.val)^(-((word.card+3:ℝ)/2)):ℝ):ℂ)*
        ((forwardScale t z.val)⁻¹:ℝ)*
        (momentum i f z.val word+Complex.I*t*(reciprocalVolume z.val:ℂ)*
          (volumeGradient z.val i:ℂ)*forwardGenerator f z.val word):=by
  let path:ℝ→SourceCoordinateSlice:=fun s=>z.val+s • inverseColumn t z.val i
  have hx:HasDerivAt path (inverseColumn t z.val i) 0:=by
    simpa [path] using ((hasDerivAt_id (0:ℝ)).smul_const (inverseColumn t z.val i)).const_add z.val
  have hF:HasDerivAt (fun s=>forwardPoint t (path s)) (coframeDirection i) 0:=by
    have h:=(actual_forwardPoint_derivative t ht z).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp [path])
    simpa only [Function.comp_def,forward_inverseColumn t ht z i] using! h
  have hl:=(((component word (sourceForwardCore t ht f)).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=forwardPoint t z.val)).comp_hasDerivAt_of_eq (0:ℝ) hF (by simp [path])
  have hr:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp [path])
  have ha:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (amplitude_line t ht z i word)
  have hh:=ha.mul hr
  have he:(fun s:ℝ=>(Real.rpow (forwardRatio t (path s)) (-((word.card+3:ℝ)/2)):ℂ)*f (path s) word)
      =ᶠ[𝓝 (0:ℝ)] (fun s=>sourceForwardCore t ht f (forwardPoint t (path s)) word):=by
    have hp:∀ᶠ s in 𝓝 (0:ℝ),path s∈physicalChart:=
      hx.continuousAt.eventually (physicalChart.isOpen.mem_nhds (by simp [path]))
    filter_upwards [hp] with s hs
    exact (forwardCore_apply t ht f ⟨path s,hs⟩ word).symm
  have hc(q:QuantumTest)(x:SourceCoordinateSlice):(component word q) x=q x word:=rfl
  simp only [hc,Function.comp_def,Complex.ofRealCLM_apply] at hl hh
  change HasDerivAt (fun s:ℝ=>(Real.rpow (forwardRatio t (path s)) (-((word.card+3:ℝ)/2)):ℂ)*f (path s) word) _ 0 at hh
  have heq:=hl.unique (hh.congr_of_eventuallyEq he.symm)
  rw [momentum_component,heq,momentum_component,forwardGenerator_component]
  simp only [path,zero_smul,add_zero,inverseColumn,map_smul,map_add,
    RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.ofReal_eq_complex_ofReal,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_add,Complex.ofReal_natCast]
  unfold reciprocalVolume
  push_cast
  ring
private def heatInput(t:ℝ)(ht:0<t)(ξ:ℝ):End:=
  (show {N:End // sourceForwardCore t ht.le*N=sourceHeatCore t ht ξ} from ⟨_,rfl⟩).val
private theorem heatInput_source(t:ℝ)(ht:0<t)(ξ:ℝ):
    sourceForwardCore t ht.le*heatInput t ht ξ=sourceHeatCore t ht ξ:=rfl
private def heatCoefficient(t ξ:ℝ)(z:SourceCoordinateSlice):ℝ:=
  heatMean t z+Real.sqrt (heatVariance t z)*ξ
private def heatDelta(t ξ:ℝ)(z:SourceCoordinateSlice):ℝ:=
  reciprocalVolume z-SourceClockPhiForwardNativeReturn.forwardU t z-heatKappa t z*ξ
private def inputMap(t ξ:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  combinedMap (heatCoefficient t ξ z) z
private theorem heatInput_point(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    heatInput t ht ξ f z=(Real.exp ((25/2:ℝ)*heatCoefficient t ξ z):ℂ) • f (inputMap t ξ z):=by
  change (Real.exp ((25/2:ℝ)*(1*heatCoefficient t ξ z)):ℂ) •
    f (combinedMap (1*heatCoefficient t ξ z) z)=_
  simp only [one_mul,inputMap]
private theorem coefficient_line_jet(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart)(v:SourceCoordinateSlice):
    HasDerivAt (fun s:ℝ=>heatCoefficient t ξ (z.val+s • v))
      ((heatDelta t ξ z.val/6)*fderiv ℝ GaussNativeEnergy.volume z.val v) 0:=by
  have hx:HasDerivAt (fun s:ℝ=>z.val+s • v) v 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val
  have hv:HasDerivAt (fun s:ℝ=>GaussNativeEnergy.volume (z.val+s • v))
      (fderiv ℝ GaussNativeEnergy.volume z.val v) 0:=
    ((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
      (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have h:= (SourceClockPhiHeatComparisonJet.clock_noise_parameter_derivative
    (GaussNativeEnergy.volume z.val) t ξ (volume_pos z) ht).comp_of_eq (0:ℝ) hv (by simp)
  have he(x:SourceCoordinateSlice):
      ξ*Real.sqrt (Real.log (1+18*t/GaussNativeEnergy.volume x)/9)-Real.log (1+18*t/GaussNativeEnergy.volume x)/6=
        heatCoefficient t ξ x:=by
    unfold heatCoefficient heatMean heatVariance heatLog reciprocalVolume
    rw [div_eq_mul_inv (18*t)]
    ring
  have hd:(((1/GaussNativeEnergy.volume z.val-1/(GaussNativeEnergy.volume z.val+18*t))-
      ((1/GaussNativeEnergy.volume z.val-1/(GaussNativeEnergy.volume z.val+18*t))/
        Real.sqrt (Real.log (1+18*t/GaussNativeEnergy.volume z.val)))*ξ)/6)=
      (heatDelta t ξ z.val/6):=by
    unfold heatDelta heatKappa heatLog SourceClockPhiForwardNativeReturn.forwardU reciprocalVolume
    rw [div_eq_mul_inv (18*t)]
    ring
  simpa only [Function.comp_def,zero_smul,add_zero,he,hd] using h
private theorem inputMap_line_jet(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart)
    (v:SourceCoordinateSlice)(hv:v.2=0):
    HasDerivAt (fun s:ℝ=>inputMap t ξ (z.val+s • v))
      (v+((heatDelta t ξ z.val/6)*fderiv ℝ GaussNativeEnergy.volume z.val v) •
        (SourceScalarVirialBulk.phiEuler (inputMap t ξ z.val)-SourceGaugeRadialCurrent.gaugeEuler (inputMap t ξ z.val))) 0:=by
  let c:=heatCoefficient t ξ z.val
  let dc:=(heatDelta t ξ z.val/6)*fderiv ℝ GaussNativeEnergy.volume z.val v
  have hc:=coefficient_line_jet t ht ξ z v
  have he:=hc.exp
  have hn:=hc.neg.exp
  have hco:HasDerivAt (fun s:ℝ=>z.val.1+s • v.1) v.1 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v.1).const_add z.val.1
  have h:=hco.prodMk (((he.smul_const (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)).sub_const
    SourceScalarVirialBulk.vacuumSlice).prodMk (hn.smul_const z.val.2.2))
  have hp:heatCoefficient t ξ (z.val+(0:ℝ) • v)=c:=by simp [c]
  simp only [Pi.neg_apply,hp] at h
  have hd:(v.1,(Real.exp c*dc) • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice),(Real.exp (-c)*(-dc)) • z.val.2.2)=
      v+dc • (SourceScalarVirialBulk.phiEuler (inputMap t ξ z.val)-SourceGaugeRadialCurrent.gaugeEuler (inputMap t ξ z.val)):=by
    simp only [inputMap,combinedMap_apply,SourceScalarVirialBulk.phiEuler,SourceGaugeRadialCurrent.gaugeEuler]
    apply Prod.ext
    · simp
    rw [Prod.snd_add,hv,zero_add]
    apply Prod.ext
    · change (Real.exp c*dc) • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)=
        dc • (SourceScalarVirialBulk.vacuumSlice+(Real.exp c • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)-SourceScalarVirialBulk.vacuumSlice)-0)
      module
    · change (Real.exp (-c)*(-dc)) • z.val.2.2=dc • (0-Real.exp (-c) • z.val.2.2)
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
private theorem input_coframe_derivative(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:physicalChart)
    (v:SourceCoordinateSlice)(hv:v.2=0)(word:Occupation):
    fderiv ℝ (component word (heatInput t ht ξ f)) z.val v=
      (Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*
        (fderiv ℝ (component word f) (inputMap t ξ z.val) v+
          ((heatDelta t ξ z.val/6)*fderiv ℝ GaussNativeEnergy.volume z.val v:ℝ)*
            combinedGenerator f (inputMap t ξ z.val) word):=by
  have hc:=coefficient_line_jet t ht ξ z v
  have hx:=inputMap_line_jet t ht ξ z v hv
  have hz:HasDerivAt (fun s:ℝ=>z.val+s • v) v 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val
  have hf:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=inputMap t ξ z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hl:=(((component word (heatInput t ht ξ f)).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hz (by simp)
  have he:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hc.const_mul (25/2:ℝ)).exp)
  have hh:=he.mul hf
  have heq:(fun s:ℝ=>(Real.exp ((25/2:ℝ)*heatCoefficient t ξ (z.val+s • v)):ℂ)*
      f (inputMap t ξ (z.val+s • v)) word)=
      fun s:ℝ=>heatInput t ht ξ f (z.val+s • v) word:=by
    funext s
    rw [heatInput_point]
    rfl
  have hcomp(q:QuantumTest)(x:SourceCoordinateSlice):(component word q) x=q x word:=rfl
  dsimp only [Function.comp_def,Complex.ofRealCLM_apply,Pi.mul_apply] at hh hl
  simp only [hcomp] at hh hl
  change HasDerivAt (fun s:ℝ=>(Real.exp ((25/2:ℝ)*heatCoefficient t ξ (z.val+s • v)):ℂ)*
    f (inputMap t ξ (z.val+s • v)) word) _ 0 at hh
  rw [heq] at hh
  have h:=hl.unique hh
  rw [h,combined_component]
  simp only [zero_smul,add_zero,map_add,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ),
    RCLike.ofReal_eq_complex_ofReal,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

private theorem inputMap_chart(t ξ:ℝ)(z:physicalChart):inputMap t ξ z.val∈physicalChart:=by
  have hg:=SourceGaugeScaleTransport.scale_chart_iff (Real.exp (-heatCoefficient t ξ z.val))
    (Real.exp_pos _) (SourceScalarAffineScaleTransport.scaleEquiv (heatCoefficient t ξ z.val) z.val)
  have hp:=SourceScalarAffineScaleTransport.scale_chart_iff (heatCoefficient t ξ z.val) z.val
  exact (hg.trans hp).mpr z.property
private theorem input_momentum(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:physicalChart)(i:Fin 6)(word:Occupation):
    GaussCoframeCore.momentum i (heatInput t ht ξ f) z.val word=
      (Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*
        (GaussCoframeCore.momentum i f (inputMap t ξ z.val) word-
          Complex.I*(heatDelta t ξ z.val/6:ℝ)*(volumeGradient z.val i:ℂ)*
            combinedGenerator f (inputMap t ξ z.val) word):=by
  rw [momentum_component,input_coframe_derivative t ht ξ f z (coframeDirection i) rfl,
    volume_coordinate_derivative,momentum_component]
  push_cast
  ring
private theorem input_forwardGenerator(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    forwardGenerator (heatInput t ht ξ f) z.val word=
      (Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*
        (forwardGenerator f (inputMap t ξ z.val) word-
          3*(heatDelta t ξ z.val:ℂ)*combinedGenerator f (inputMap t ξ z.val) word):=by
  let zi:physicalChart:=⟨inputMap t ξ z.val,inputMap_chart t ξ z⟩
  have hu:reciprocalVolume zi.val=reciprocalVolume z.val:=rfl
  have he:euler zi.val=euler z.val:=rfl
  rw [forwardGenerator_component,input_coframe_derivative t ht ξ f z (euler z.val) rfl,
    volume_euler,heatInput_point]
  rw [forwardGenerator_component f zi,hu,he]
  simp only [PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  unfold reciprocalVolume
  push_cast
  field_simp [(show (GaussNativeEnergy.volume z.val:ℂ)≠0 by exact_mod_cast (volume_pos z).ne')]
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
private theorem sourceHeat_forward_point(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    sourceHeatCore t ht ξ f (forwardPoint t z.val) word=
      (Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*
        ((Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*f (inputMap t ξ z.val) word):=by
  rw [←heatInput_source]
  rw [Module.End.mul_apply,forwardCore_apply,heatInput_point]
  rfl

theorem actual_heat_momentum_point(t:ℝ)(ht:0<t)(ξ:ℝ)(i:Fin 6)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    GaussCoframeCore.momentum i (sourceHeatCore t ht ξ f) (forwardPoint t z.val) word=
      ((forwardScale t z.val)⁻¹:ℂ)*
        (sourceHeatCore t ht ξ (GaussCoframeCore.momentum i f) (forwardPoint t z.val) word-
          (3*Complex.I*t*(reciprocalVolume z.val:ℂ)*(volumeGradient z.val i:ℂ))*
            sourceHeatCore t ht ξ (SourceClockPhiMatchedDiffusionSource.driftClock f) (forwardPoint t z.val) word+
          (Complex.I*ξ*(forwardRatio t z.val*heatKappa t z.val/6:ℝ)*(volumeGradient z.val i:ℂ))*
            sourceHeatCore t ht ξ (combinedGenerator f) (forwardPoint t z.val) word):=by
  have h:=actual_forward_momentum_point t ht.le i (heatInput t ht ξ f) z word
  change GaussCoframeCore.momentum i ((sourceForwardCore t ht.le*heatInput t ht ξ) f) _ _=_ at h
  rw [heatInput_source,input_momentum,input_forwardGenerator] at h
  rw [h,sourceHeat_forward_point,sourceHeat_forward_point,sourceHeat_forward_point,driftClock_component]
  simp only [Real.rpow_eq_pow]
  have hu:reciprocalVolume (inputMap t ξ z.val)=reciprocalVolume z.val:=rfl
  rw [hu]
  unfold heatDelta SourceClockPhiForwardNativeReturn.forwardU forwardRatio reciprocalVolume
  push_cast
  have hv:(GaussNativeEnergy.volume z.val:ℂ)≠0:=by exact_mod_cast (volume_pos z).ne'
  have hw:(GaussNativeEnergy.volume z.val+18*t:ℂ)≠0:=by exact_mod_cast (show GaussNativeEnergy.volume z.val+18*t≠0 by linarith [volume_pos z])
  field_simp [hv,hw]
  ring

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

theorem actual_complete_heat_momentum_point(t:ℝ)(ht:0<t)(ξ:ℝ)(i:Fin 6)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    GaussCoframeCore.momentum i (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f) (forwardPoint t z.val) word=
      ((forwardScale t z.val)⁻¹:ℂ)*
        (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (GaussCoframeCore.momentum i f) (forwardPoint t z.val) word-
          (3*Complex.I*t*(reciprocalVolume z.val:ℂ)*(volumeGradient z.val i:ℂ))*
            SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (SourceClockPhiNativeMatchedSource.matchedTester f) (forwardPoint t z.val) word+
          (Complex.I*ξ*(forwardRatio t z.val*heatKappa t z.val/6:ℝ)*(volumeGradient z.val i:ℂ))*
            SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (combinedGenerator f) (forwardPoint t z.val) word):=by
  let zi:physicalChart:=⟨inputMap t ξ z.val,inputMap_chart t ξ z⟩
  change GaussCoframeCore.momentum i (sourceHeatCore t ht ξ (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)) _ _=_
  rw [actual_heat_momentum_point]
  simp only [SourceClockPhiCompleteHeatGainPayment.completeHeatCore,Module.End.mul_apply,sourceHeat_forward_point]
  rw [gain_momentum t ht f zi,gain_driftClock t ht f zi,gain_combined t ht f zi]
  simp only [SourceClockPhiActualCovarianceStep.sourceGain,multiply_apply,PiLp.smul_apply,smul_eq_mul]
  rw [matchedTester_component]
  have hu:reciprocalVolume zi.val=reciprocalVolume z.val:=rfl
  have huu:SourceClockPhiForwardNativeReturn.forwardU t zi.val=SourceClockPhiForwardNativeReturn.forwardU t z.val:=rfl
  have hv:volumeGradient zi.val i=volumeGradient z.val i:=rfl
  rw [hu,huu,hv]
  change _=((forwardScale t z.val)⁻¹:ℂ)*
    (((Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*
        ((Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*
          ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) zi.val:ℂ)*GaussCoframeCore.momentum i f zi.val word)))-
      (3*Complex.I*t*(reciprocalVolume z.val:ℂ)*(volumeGradient z.val i:ℂ))*
        ((Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*
        ((Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*
          ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) zi.val:ℂ)*
            (SourceClockPhiMatchedDiffusionSource.driftClock f zi.val word-(reciprocalVolume z.val:ℂ)*f zi.val word))))+
      (Complex.I*ξ*(forwardRatio t z.val*heatKappa t z.val/6:ℝ)*(volumeGradient z.val i:ℂ))*
        ((Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*
        ((Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*
          ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) zi.val:ℂ)*combinedGenerator f zi.val word))))
  push_cast
  ring

private theorem heatKappa_smooth(t:ℝ)(ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (heatKappa t) z.val:=by
  have hlog:0<heatLog t z.val:=by
    apply Real.log_pos
    have hU:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
    change 1<1+18*t*reciprocalVolume z.val
    have hp:0<18*t*reciprocalVolume z.val:=by positivity
    linarith
  have hs:ContDiffAt ℝ ∞ (heatLog t) z.val:=by
    apply (contDiffAt_const.add ((contDiffAt_const.mul contDiffAt_const).mul (reciprocal_volume_smooth z))).log
    have hU:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
    positivity
  exact ((reciprocal_volume_smooth z).sub (SourceClockPhiForwardNativeReturn.forwardU_smooth t ht.le z)).div
    (hs.sqrt hlog.ne') (Real.sqrt_pos.mpr hlog).ne'
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
private def noiseColumnAction(t:ℝ)(ht:0<t)(i:Fin 6):End:=
  multiply (fun z=>forwardRatio t z*heatKappa t z/6*volumeGradient z i) (fun z=>by
    have hr:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact ((hr.mul (heatKappa_smooth t ht z)).div_const 6).mul (volumeGradient_smooth i).contDiffAt)
def heatCoframeRow(t:ℝ)(ht:0<t)(ξ:ℝ)(i:Fin 6):End:=
  radialRateAction t ht*(GaussCoframeCore.momentum i-
    (3*Complex.I*t:ℂ) • (currentColumnAction i*SourceClockPhiNativeMatchedSource.matchedTester)+
    (Complex.I*ξ:ℂ) • (noiseColumnAction t ht i*combinedGenerator))
private theorem heatCoframeRow_point(t:ℝ)(ht:0<t)(ξ:ℝ)(i:Fin 6)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    heatCoframeRow t ht ξ i f z word=(((forwardScale t z)⁻¹:ℝ):ℂ)*
      (GaussCoframeCore.momentum i f z word-
        (3*Complex.I*t:ℂ)*(((reciprocalVolume z*volumeGradient z i:ℝ):ℂ)*SourceClockPhiNativeMatchedSource.matchedTester f z word)+
        (Complex.I*ξ:ℂ)*(((forwardRatio t z*heatKappa t z/6*volumeGradient z i:ℝ):ℂ)*combinedGenerator f z word)):=rfl
private theorem completeHeat_point(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f (forwardPoint t z.val) word=
      (Real.rpow (forwardRatio t z.val) (-((word.card+3:ℝ)/2)):ℂ)*
        ((Real.exp ((25/2:ℝ)*heatCoefficient t ξ z.val):ℂ)*
          ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*f (inputMap t ξ z.val) word)):=by
  change sourceHeatCore t ht ξ (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f) _ _=_
  rw [sourceHeat_forward_point]
  rfl
private theorem completeHeat_above(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)
    (hz:z∈tsupport (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)):
    18*t<GaussNativeEnergy.volume z:=by
  change z∈tsupport (sourceForwardCore t ht.le (heatInput t ht ξ
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f))) at hz
  obtain ⟨x,hx,rfl⟩:=forward_support t ht.le _ hz
  exact forward_above t ht.le ⟨x,(heatInput t ht ξ
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)).tsupport_subset hx⟩
private theorem complete_momentum_below(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)
    (hz:¬18*t<GaussNativeEnergy.volume z)(i:Fin 6):
    GaussCoframeCore.momentum i (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f) z=0:=by
  have hn:z∉tsupport (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f):=
    fun h=>hz (completeHeat_above t ht ξ f z h)
  change (-Complex.I) • GaussCoframeCore.derivative (coframeDirection i)
    (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f) z=0
  rw [GaussCoframeCore.derivative_apply,fderiv_of_notMem_tsupport ℝ hn]
  simp only [zero_apply,smul_zero]

theorem actual_complete_heat_coframe_return(t:ℝ)(ht:0<t)(ξ:ℝ)(i:Fin 6):
    GaussCoframeCore.momentum i*SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ=
      SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ*heatCoframeRow t ht ξ i:=by
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
      change GaussCoframeCore.momentum i (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f) (forwardPoint t z.val) word=
        SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (heatCoframeRow t ht ξ i f) (forwardPoint t z.val) word
      rw [actual_complete_heat_momentum_point,completeHeat_point,completeHeat_point,completeHeat_point,completeHeat_point]
      rw [heatCoframeRow_point]
      have hs:forwardScale t (inputMap t ξ z.val)=forwardScale t z.val:=rfl
      have hu:reciprocalVolume (inputMap t ξ z.val)=reciprocalVolume z.val:=rfl
      have hv:volumeGradient (inputMap t ξ z.val) i=volumeGradient z.val i:=rfl
      have hr:forwardRatio t (inputMap t ξ z.val)=forwardRatio t z.val:=rfl
      have hk:heatKappa t (inputMap t ξ z.val)=heatKappa t z.val:=rfl
      rw [hs,hu,hv,hr,hk]
      push_cast
      ring
    · change GaussCoframeCore.momentum i (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f) x=_
      rw [complete_momentum_below t ht ξ f x ha i]
      exact (image_eq_zero_of_notMem_tsupport (fun h=>ha
        (completeHeat_above t ht ξ (heatCoframeRow t ht ξ i f) x h))).symm
  · have h0(q:QuantumTest):q x=0:=image_eq_zero_of_notMem_tsupport (fun h=>hx (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem heat_pair(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (sourceHeatCore t ht ξ f) (sourceHeatCore t ht ξ g)=sourcePair f g:=by
  have hn(c:ℂ):‖embed (sourceHeatCore t ht ξ f)+c • embed (sourceHeatCore t ht ξ g)‖=
      ‖embed f+c • embed g‖:=by
    calc _=‖embed (sourceHeatCore t ht ξ (f+c • g))‖:=by simp only [map_add,map_smul]
         _=‖embed (f+c • g)‖:=sourceHeat_norm t ht ξ _
         _=_:=by simp only [map_add,map_smul]
  have hp:‖embed (sourceHeatCore t ht ξ f)+embed (sourceHeatCore t ht ξ g)‖=‖embed f+embed g‖:=by simpa only [one_smul] using hn 1
  have hm:‖embed (sourceHeatCore t ht ξ f)-embed (sourceHeatCore t ht ξ g)‖=‖embed f-embed g‖:=by simpa only [neg_one_smul,sub_eq_add_neg] using hn (-1)
  have hmi:‖embed (sourceHeatCore t ht ξ f)-(RCLike.I:ℂ) • embed (sourceHeatCore t ht ξ g)‖=‖embed f-(RCLike.I:ℂ) • embed g‖:=by simpa only [neg_smul,sub_eq_add_neg] using hn (-(RCLike.I:ℂ))
  unfold sourcePair
  simp only [inner_eq_sum_norm_sq_div_four,hn,hp,hm,hmi]
private def forwardMetricAction(t:ℝ)(ht:0<t)(i j:Fin 6):End:=
  multiply (fun x=>GaussCoframeKinetic.coefficient i j (forwardPoint t x))
    (fun z=>by
      simpa only [Function.comp_def] using! (GaussCoframeKinetic.coefficient_smooth i j
        ⟨forwardPoint t z.val,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))
private theorem input_metric(t:ℝ)(ht:0<t)(ξ:ℝ)(i j:Fin 6):
    Commute (heatInput t ht ξ) (forwardMetricAction t ht i j):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change heatInput t ht ξ (forwardMetricAction t ht i j f) z word=
    (GaussCoframeKinetic.coefficient i j (forwardPoint t z):ℂ)*heatInput t ht ξ f z word
  rw [heatInput_point,heatInput_point]
  change (Real.exp ((25/2:ℝ)*heatCoefficient t ξ z):ℂ)*
      ((GaussCoframeKinetic.coefficient i j (forwardPoint t (inputMap t ξ z)):ℂ)*f (inputMap t ξ z) word)=_
  have hc:GaussCoframeKinetic.coefficient i j (forwardPoint t (inputMap t ξ z))=
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
private theorem metric_complete_transport(t:ℝ)(ht:0<t)(ξ:ℝ)(i j:Fin 6):
    SourceCoframeCovariantAction.metricAction i j*SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ=
      SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ*forwardMetricAction t ht i j:=by
  have hJ:=SourceClockPhiForwardGeneratorTransport.actual_forward_multiplier_transport t ht.le
    (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)
  change SourceCoframeCovariantAction.metricAction i j*sourceForwardCore t ht.le=
    sourceForwardCore t ht.le*forwardMetricAction t ht i j at hJ
  rw [SourceClockPhiCompleteHeatGainPayment.completeHeatCore,←heatInput_source]
  calc
    _=(SourceCoframeCovariantAction.metricAction i j*sourceForwardCore t ht.le)*
        heatInput t ht ξ*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by noncomm_ring
    _=(sourceForwardCore t ht.le*forwardMetricAction t ht i j)*
        heatInput t ht ξ*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by rw [hJ]
    _=(sourceForwardCore t ht.le*heatInput t ht ξ*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t))*
        forwardMetricAction t ht i j:=by
      have hN:forwardMetricAction t ht i j*heatInput t ht ξ=heatInput t ht ξ*forwardMetricAction t ht i j:=
        (input_metric t ht ξ i j).eq.symm
      have hG:forwardMetricAction t ht i j*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)=
        SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)*forwardMetricAction t ht i j:=(gain_metric t ht i j).eq
      calc
        _=sourceForwardCore t ht.le*(forwardMetricAction t ht i j*heatInput t ht ξ)*
          SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by noncomm_ring
        _=sourceForwardCore t ht.le*(heatInput t ht ξ*forwardMetricAction t ht i j)*
          SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by rw [hN]
        _=(sourceForwardCore t ht.le*heatInput t ht ξ)*
          (forwardMetricAction t ht i j*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by noncomm_ring
        _=(sourceForwardCore t ht.le*heatInput t ht ξ)*
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

theorem actual_complete_heat_metric_pair(t:ℝ)(ht:0<t)(ξ:ℝ)(i j:Fin 6)(f g:QuantumTest):
    sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (SourceCoframeCovariantAction.metricAction i j (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))=
        sourcePair f (SourceCoframeCovariantAction.metricAction i j g):=by
  have h:=LinearMap.congr_fun (metric_complete_transport t ht ξ i j) g
  change SourceCoframeCovariantAction.metricAction i j (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)=
    SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (forwardMetricAction t ht i j g) at h
  rw [h]
  change sourcePair (sourceHeatCore t ht ξ (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f))
    (sourceHeatCore t ht ξ (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (forwardMetricAction t ht i j g)))=_
  rw [heat_pair]
  have hG(p q:QuantumTest):sourcePair p (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) q)=
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) p) q:=multiply_pair _ _ p q
  rw [←hG]
  have he:=LinearMap.congr_fun (gain_squared_metric t ht i j) g
  exact congrArg (sourcePair f) he

theorem actual_complete_heat_kinetic_pair(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)
      (GaussCoframeKinetic.kinetic (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))=
      ∑i:Fin 6,∑j:Fin 6,sourcePair (heatCoframeRow t ht ξ i f)
        (SourceCoframeCovariantAction.metricAction i j (heatCoframeRow t ht ξ j g)):=by
  simp only [GaussCoframeKinetic.kinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change sourcePair _ (GaussCoframeCore.adjoint i (SourceCoframeCovariantAction.metricAction i j
    (GaussCoframeCore.momentum j (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g))))=_
  rw [GaussCoframeKinetic.adjoint_pair]
  have hi:=LinearMap.congr_fun (actual_complete_heat_coframe_return t ht ξ i) f
  have hj:=LinearMap.congr_fun (actual_complete_heat_coframe_return t ht ξ j) g
  change GaussCoframeCore.momentum i (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ f)=
    SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (heatCoframeRow t ht ξ i f) at hi
  change GaussCoframeCore.momentum j (SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ g)=
    SourceClockPhiCompleteHeatGainPayment.completeHeatCore t ht ξ (heatCoframeRow t ht ξ j g) at hj
  rw [hi,hj]
  exact actual_complete_heat_metric_pair t ht ξ i j _ _

end LowEnergy.ClockPhiHeatHamiltonianWork
