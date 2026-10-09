import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardPair
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiActualCovarianceStep
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussLiveMomentum SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiCoframeForwardCore SourceClockPhiCoframeForwardPair ClockPhiMatchedNoiseCore
open SourcePhysicalKineticSquare
open MeasureTheory Filter Set
open scoped Topology
open scoped ContDiff
private abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest

def branchRate (branch : Bool) : ℝ := if branch then -Real.sqrt 2 else Real.sqrt 2
def conservativeStep (branch : Bool) (ε : ℝ) : End :=
  sourceForwardCore (ε^2) (sq_nonneg _)*noiseCore (branchRate branch*ε) (-3*ε^2)
def gainProfile (ε : ℝ) (z : SourceCoordinateSlice) : ℝ :=
  (forwardRatio (ε^2) z)^(1/6 : ℝ)
private theorem gain_smooth (ε : ℝ) (z : physicalChart) :
    ContDiffAt ℝ ∞ (gainProfile ε) z.val := by
  have hr:ContDiffAt ℝ ∞ (forwardRatio (ε^2)) z.val :=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact hr.rpow_const_of_ne (p:=(1/6 : ℝ)) (forward_ratio_pos (ε^2) (sq_nonneg _) z).ne'
def sourceGain (ε : ℝ) : End := multiply (gainProfile ε) (gain_smooth ε)
def completeStep (branch : Bool) (ε : ℝ) : End :=
  sourceForwardCore (ε^2) (sq_nonneg _)*sourceGain ε*
    noiseCore (branchRate branch*ε) (-3*ε^2)

theorem actual_conservative_step_pair (branch : Bool) (ε : ℝ) (f g : QuantumTest) :
    sourcePair (conservativeStep branch ε f) (conservativeStep branch ε g)=sourcePair f g := by
  simp only [conservativeStep,Module.End.mul_apply]
  rw [actual_forward_core_pair,noiseCore_pair]

private theorem gain_noise_commute (ε r s : ℝ) : Commute (noiseCore r s) (sourceGain ε) := by
  apply noise_real_multiplier r s (gainProfile ε) (gain_smooth ε)
  intro z
  rfl

theorem actual_complete_step_pair (branch : Bool) (ε : ℝ) (f g : QuantumTest) :
    sourcePair (completeStep branch ε f) (completeStep branch ε g)=
      sourcePair f (sourceGain ε (sourceGain ε g)) := by
  let r:=branchRate branch*ε
  let s:ℝ:= -3*ε^2
  have h (p : QuantumTest):sourceGain ε (noiseCore r s p)=noiseCore r s (sourceGain ε p) :=
    (LinearMap.congr_fun (gain_noise_commute ε r s).eq p).symm
  simp only [completeStep,Module.End.mul_apply]
  rw [actual_forward_core_pair,h,h,noiseCore_pair]
  exact (multiply_pair (gainProfile ε) (gain_smooth ε) f (sourceGain ε g)).symm

def covariancePair (ε : ℝ) (X : End) (f g : QuantumTest) : ℂ :=
  (sourcePair (conservativeStep false ε f) (X (conservativeStep false ε g))+
    sourcePair (conservativeStep true ε f) (X (conservativeStep true ε g)))/2
def completeCovariancePair (ε : ℝ) (X : End) (f g : QuantumTest) : ℂ :=
  (sourcePair (completeStep false ε f) (X (completeStep false ε g))+
    sourcePair (completeStep true ε f) (X (completeStep true ε g)))/2

theorem actual_covariance_identity (ε : ℝ) (f g : QuantumTest) :
    covariancePair ε 1 f g=sourcePair f g ∧
    completeCovariancePair ε 1 f g=sourcePair f (sourceGain ε (sourceGain ε g)) := by
  simp only [covariancePair,completeCovariancePair,Module.End.one_apply,
    actual_conservative_step_pair,actual_complete_step_pair]
  constructor <;> ring



private theorem gain_square_point (ε : ℝ) (f : QuantumTest) (z : physicalChart) (word : Occupation) :
    sourceGain ε (sourceGain ε f) z.val word=
      (((forwardRatio (ε^2) z.val)^(1/3 : ℝ) : ℝ) : ℂ)*f z.val word := by
  change (gainProfile ε z.val : ℂ)*((gainProfile ε z.val : ℂ)*f z.val word)=_
  have hp:((forwardRatio (ε^2) z.val)^(1/6 : ℝ))^2=(forwardRatio (ε^2) z.val)^(1/3 : ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (forward_ratio_pos (ε^2) (sq_nonneg _) z).le]
    norm_num
  have hc:=congrArg Complex.ofReal hp
  simp only [Complex.ofReal_pow] at hc
  unfold gainProfile
  rw [←mul_assoc,←pow_two,hc]

private theorem square_second_jet (g : ℝ → ℂ) (v : ℂ)
    (hg : ContDiffAt ℝ ∞ g 0) (hd : HasDerivAt g v 0) :
    HasDerivAt (deriv (fun e : ℝ=>g (e^2))) (2*v) 0 := by
  have hgd:ContDiffAt ℝ 1 (deriv g) 0:=hg.derivWithin (m:=1)
    (by norm_num;exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hs:HasDerivAt (fun e : ℝ=>e^2) 0 0:=by simpa using hasDerivAt_pow 2 (0 : ℝ)
  have hh:=hgd.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hs (by simp)
  have hh':HasDerivAt (fun e : ℝ=>deriv g (e^2)) 0 0 := by
    simpa only [Function.comp_def,map_zero] using hh
  have hl:HasDerivAt (fun e : ℝ=>((2*e : ℝ) : ℂ)) 2 0 := by
    simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,mul_one,
      Complex.ofReal_ofNat,Complex.ofReal_mul] using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_mul 2)
  have hp:=hl.mul hh'
  simp at hp
  rw [hd.deriv] at hp
  apply hp.congr_of_eventuallyEq
  have hc:∀ᶠ x : ℝ in 𝓝 0,DifferentiableAt ℝ g x :=
    ((hg.of_le (show (1 : ℕ∞ω)≤∞ by norm_num)).eventually (by norm_num)).mono
      (fun x hx=>hx.differentiableAt (by norm_num))
  have hst:Filter.Tendsto (fun e : ℝ=>e^2) (𝓝 0) (𝓝 0):=by simpa using hs.continuousAt.tendsto
  filter_upwards [hst.eventually hc] with e he
  have hm:=he.hasDerivAt.scomp (h:=fun u : ℝ=>u^2) e (hasDerivAt_pow 2 e)
  simpa [Function.comp_def,Complex.real_smul] using hm.deriv

private theorem gain_mass_point_second (z : physicalChart) :
    HasDerivAt (deriv (fun ε : ℝ=>
      (((forwardRatio (ε^2) z.val)^(1/3 : ℝ) : ℝ) : ℂ)))
      (12*(reciprocalVolume z.val : ℂ)) 0 := by
  let q:ℝ→ℂ:=fun t=>(((forwardRatio t z.val)^(1/3 : ℝ) : ℝ) : ℂ)
  have hR:forwardRatio 0 z.val=1 := by unfold forwardRatio;simp [(volume_pos z).ne']
  have hs:ContDiffAt ℝ ∞ q 0 := by
    have hr:ContDiffAt ℝ ∞ (fun t : ℝ=>forwardRatio t z.val) 0 := by
      unfold forwardRatio
      fun_prop
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0
      (hr.rpow_const_of_ne (p:=(1/3 : ℝ)) (by rw [hR];norm_num))
  have hd:HasDerivAt q (6*(reciprocalVolume z.val : ℂ)) 0 := by
    have hr:HasDerivAt (fun t : ℝ=>forwardRatio t z.val) (18/GaussNativeEnergy.volume z.val) 0 := by
      unfold forwardRatio
      simpa only [Function.comp_def,id_eq,mul_one] using! (((hasDerivAt_id (0 : ℝ)).const_mul 18).const_add
        (GaussNativeEnergy.volume z.val)).div_const (GaussNativeEnergy.volume z.val)
    have h:=hr.rpow_const (p:=(1/3 : ℝ)) (Or.inl (by rw [hR];norm_num))
    rw [hR] at h
    have hc:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    convert! hc using 1
    simp only [Real.one_rpow,Complex.ofRealCLM_apply,reciprocalVolume,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one,Complex.ofReal_inv]
    ring
  have h:=square_second_jet q (6*(reciprocalVolume z.val : ℂ)) hs hd
  convert h using 1
  ring

private def massComponent (f : QuantumTest) (word : Occupation) (p : ℝ×SourceCoordinateSlice) : ℂ :=
  sourceGain p.1 (sourceGain p.1 f) p.2 word
private theorem massComponent_smooth (f : QuantumTest) (word : Occupation) :
    ContDiff ℝ ∞ (massComponent f word) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp:p.2∈tsupport f
  · have hz:p.2∈physicalChart:=f.tsupport_subset hp
    have hv:ContDiffAt ℝ ∞ (fun q : ℝ×SourceCoordinateSlice=>GaussNativeEnergy.volume q.2) p :=
      volume_smooth.contDiffAt.comp p contDiffAt_snd
    have he:ContDiffAt ℝ ∞ (fun q : ℝ×SourceCoordinateSlice=>q.1^2) p:=by fun_prop
    have hr:ContDiffAt ℝ ∞ (fun q : ℝ×SourceCoordinateSlice=>forwardRatio (q.1^2) q.2) p :=
      (hv.add (contDiffAt_const.mul he)).div hv (volume_pos ⟨p.2,hz⟩).ne'
    have ha:ContDiffAt ℝ ∞ (fun q : ℝ×SourceCoordinateSlice=>
        (((forwardRatio (q.1^2) q.2)^(1/3 : ℝ) : ℝ) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (hr.rpow_const_of_ne (p:=(1/3 : ℝ))
          (forward_ratio_pos (p.1^2) (sq_nonneg _) ⟨p.2,hz⟩).ne')
    have hf:ContDiffAt ℝ ∞ (fun q : ℝ×SourceCoordinateSlice=>f q.2 word) p :=
      (component word f).contDiff.contDiffAt.comp p contDiffAt_snd
    apply (ha.mul hf).congr_of_eventuallyEq
    filter_upwards [(physicalChart.isOpen.preimage continuous_snd).mem_nhds hz] with q hq
    exact gain_square_point q.1 f ⟨q.2,hq⟩ word
  · apply (contDiffAt_const (c:=(0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [((isClosed_tsupport f).isOpen_compl.preimage continuous_snd).mem_nhds hp] with q hq
    have hf:f q.2=0:=image_eq_zero_of_notMem_tsupport hq
    simp only [massComponent,sourceGain,multiply_apply,hf,PiLp.zero_apply,smul_zero]

private def massFirst (f : QuantumTest) (word : Occupation) := parameterJet (massComponent f word)
private def massSecond (f : QuantumTest) (word : Occupation) := parameterJet (massFirst f word)
private theorem massFirst_smooth (f : QuantumTest) (word : Occupation) :
    ContDiff ℝ ∞ (massFirst f word) := parameterJet_smooth _ (massComponent_smooth f word)
private theorem massSecond_smooth (f : QuantumTest) (word : Occupation) :
    ContDiff ℝ ∞ (massSecond f word) := parameterJet_smooth _ (massFirst_smooth f word)

private theorem mass_second_zero (f : QuantumTest) (word : Occupation) (z : physicalChart) :
    massSecond f word (0,z.val)=12*(inverseVolumeAction f z.val word) := by
  have hcomp:(fun ε : ℝ=>massComponent f word (ε,z.val))=
      fun ε : ℝ=>(((forwardRatio (ε^2) z.val)^(1/3 : ℝ) : ℝ) : ℂ)*f z.val word :=
    funext (fun ε=>gain_square_point ε f z word)
  have hpoint:HasDerivAt (deriv (fun ε : ℝ=>massComponent f word (ε,z.val)))
      (12*(inverseVolumeAction f z.val word)) 0 := by
    rw [hcomp]
    have h:= (gain_mass_point_second z).mul_const (f z.val word)
    have hfirst:(deriv (fun ε : ℝ=>
        (((forwardRatio (ε^2) z.val)^(1/3 : ℝ) : ℝ) : ℂ)*f z.val word))=
      fun ε : ℝ=>deriv (fun u : ℝ=>
        (((forwardRatio (u^2) z.val)^(1/3 : ℝ) : ℝ) : ℂ)) ε*f z.val word := by
      funext ε
      apply deriv_mul_const
      apply (show ContDiffAt ℝ ∞ (fun ε : ℝ=>
        (((forwardRatio (ε^2) z.val)^(1/3 : ℝ) : ℝ) : ℂ)) ε from ?_).differentiableAt (by norm_num)
      have hr:ContDiffAt ℝ ∞ (fun u : ℝ=>forwardRatio (u^2) z.val) ε := by
        unfold forwardRatio
        fun_prop
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp ε
        (hr.rpow_const_of_ne (p:=(1/3 : ℝ))
          (forward_ratio_pos (ε^2) (sq_nonneg _) z).ne')
    rw [←hfirst] at h
    convert! h using 1
    change 12*((reciprocalVolume z.val : ℂ)*f z.val word)=
      (12*(reciprocalVolume z.val : ℂ))*f z.val word
    ring
  have hfirst:(fun ε : ℝ=>massFirst f word (ε,z.val))=
      deriv (fun ε : ℝ=>massComponent f word (ε,z.val)) := by
    funext ε
    exact (parameterJet_derivative _ (massComponent_smooth f word) ε z.val).deriv.symm
  have hsecond:=parameterJet_derivative _ (massFirst_smooth f word) 0 z.val
  rw [hfirst] at hsecond
  exact hsecond.unique hpoint

/-- The original gain produces the actual weak epsilon-squared identity jet, twice Q(1)=6U. -/
theorem actual_complete_identity_second_jet (p f : QuantumTest) :
    HasDerivAt (deriv (fun ε : ℝ=>completeCovariancePair ε 1 p f))
      (12*sourcePair p (inverseVolumeAction f)) 0 := by
  have h0(ε : ℝ):=fixedKernel_integral_derivative p (massComponent f) (massFirst f)
    (fun word=>(massComponent_smooth f word).continuous) (fun word=>(massFirst_smooth f word).continuous)
    (fun word u z=>parameterJet_derivative _ (massComponent_smooth f word) u z) ε
  have h1:=fixedKernel_integral_derivative p (massFirst f) (massSecond f)
    (fun word=>(massFirst_smooth f word).continuous) (fun word=>(massSecond_smooth f word).continuous)
    (fun word u z=>parameterJet_derivative _ (massFirst_smooth f word) u z) 0
  have hk (ε : ℝ) (z : SourceCoordinateSlice):fixedKernel p (massComponent f) (ε,z)=
      densityPair p (sourceGain ε (sourceGain ε f)) z := by
    simpa only [fixedKernel,massComponent] using!
      (densityPair_sum p (sourceGain ε (sourceGain ε f)) z).symm
  have he:(fun ε : ℝ=>∫z,fixedKernel p (massFirst f) (ε,z)
      ∂GaussHistoryHilbert.configurationMeasure)=
      deriv (fun ε : ℝ=>completeCovariancePair ε 1 p f) := by
    funext ε
    have h:=h0 ε
    simp_rw [hk,←sourcePair_integral,←(actual_covariance_identity _ _ _).2] at h
    exact h.deriv.symm
  rw [he] at h1
  have hz(z : SourceCoordinateSlice):fixedKernel p (massSecond f) (0,z)=
      12*densityPair p (inverseVolumeAction f) z := by
    by_cases hc:z∈physicalChart
    · change (∑word : Occupation,GaussDensityCore.complexDensity word.card z*
        star (p z word)*massSecond f word (0,z))=_
      rw [densityPair_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      rw [mass_second_zero f word ⟨z,hc⟩]
      ring
    · have hp:p z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hc (p.tsupport_subset h))
      simp [fixedKernel,densityPair_sum,hp]
  simp_rw [hz] at h1
  rw [integral_const_mul,←sourcePair_integral] at h1
  exact h1


end LowEnergy.SourceClockPhiActualCovarianceStep
