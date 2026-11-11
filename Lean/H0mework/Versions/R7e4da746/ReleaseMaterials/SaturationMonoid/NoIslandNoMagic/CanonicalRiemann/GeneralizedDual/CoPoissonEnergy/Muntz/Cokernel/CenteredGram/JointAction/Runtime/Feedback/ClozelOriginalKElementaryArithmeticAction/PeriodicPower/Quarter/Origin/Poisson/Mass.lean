import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Mass
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalKCoefficientBFiniteAction OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszSource.Translator
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
open scoped Topology FourierTransform
local notation "q"=>(1/4:ℝ)
local notation "Cq"=>ConstantDual.seed

def boxRaw (r x:ℝ):ℂ:=(Icc (-r) r).indicator (fun _=>1) x
def boxWave (c:BurnolCompletedMellinCoordinate) (h:ℝ):BurnolL2:=
  burnolMultiplicativeDilation (-h) Cq-waveCharacter c h • Cq
def boxWaveRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ):ℂ:=
  (Real.exp (-h/2):ℂ)*boxRaw (waveRadius h) x-waveCharacter c h*boxRaw q x

private theorem box_integrable (r:ℝ):Integrable (boxRaw r):=by
  exact (integrableOn_const (C:=(1:ℂ)) (s:=Icc (-r) r)
    (by exact measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc

private theorem box_integral (r:ℝ) (nonnegative:0≤r):
    (∫x:ℝ,boxRaw r x)=(2*r:ℝ):=by
  unfold boxRaw
  rw [integral_indicator measurableSet_Icc,integral_const]
  simp [nonnegative,real_smul]
  ring

private theorem box_wave_raw (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    (boxWave c h:ℝ→ℂ)=ᵐ[volume]boxWaveRaw c h:=by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp (-h)*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp (-h)) (Real.exp_ne_zero (-h)))
  filter_upwards [Lp.coeFn_sub (burnolMultiplicativeDilation (-h) Cq) (waveCharacter c h • Cq),
    burnolMultiplicativeDilation_coeFn (-h) Cq,Lp.coeFn_smul (waveCharacter c h) Cq,
    ConstantDual.seed_coeFn,scale.ae ConstantDual.seed_coeFn]
    with x difference dilation scalar direct moved
  change (burnolMultiplicativeDilation (-h) Cq-waveCharacter c h • Cq:BurnolL2) x=_
  rw [difference,Pi.sub_apply,dilation,scalar,Pi.smul_apply,smul_eq_mul,direct]
  change (Real.exp (-h/2):ℂ)*Cq (Real.exp (-h)*x)-waveCharacter c h*ConstantDual.seedRaw x=_
  rw [moved]
  have inside:|Real.exp (-h)*x|≤q ↔ |x|≤waveRadius h:=by
    rw [abs_mul,abs_of_pos (Real.exp_pos (-h)),Real.exp_neg]
    change (Real.exp h)⁻¹*|x|≤q ↔ |x|≤q*Real.exp h
    rw [←div_eq_inv_mul,div_le_iff₀ (Real.exp_pos h)]
  simp only [ConstantDual.seedRaw,boxWaveRaw,boxRaw,Set.indicator_apply,mem_Icc,←abs_le,inside]

def gapWindow (c:BurnolCompletedMellinCoordinate) (h:ℝ):ℝ→ℂ:=
  burnolEvenRaw (burnolGapTailFiniteWindowRaw q (waveRadius h) c)

private theorem gap_window_integrable (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h):
    Integrable (gapWindow c h):=by
  have ordered:q≤waveRadius h:=by
    unfold waveRadius
    nlinarith [Real.one_le_exp_iff.mpr nn]
  have source:=burnolGapTailFiniteWindow_integrable (by norm_num:(0:ℝ)<q) ordered c
  exact (source.add (source.comp_neg)).const_mul _

private theorem gap_window_integral (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h):
    (∫x:ℝ,gapWindow c h x)=0:=by
  have ordered:q≤waveRadius h:=by
    unfold waveRadius
    nlinarith [Real.one_le_exp_iff.mpr nn]
  have source:=burnolGapTailFiniteWindow_integrable (by norm_num:(0:ℝ)<q) ordered c
  unfold gapWindow burnolEvenRaw
  rw [integral_const_mul,integral_add source source.comp_neg,
    integral_neg_eq_self,burnolGapTailFiniteWindow_integral_zero (by norm_num:(0:ℝ)<q) ordered c]
  simp

private theorem complete_wave_raw (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h):
    compactRaw c h=ᵐ[volume]fun x=>
      -waveCharacter c h*gapWindow c h x-jumpCoefficient c*boxWaveRaw c h x:=by
  have positive:0<waveRadius h:=mul_pos (by norm_num) (Real.exp_pos h)
  have ordered:q≤waveRadius h:=by unfold waveRadius;nlinarith[Real.one_le_exp_iff.mpr nn]
  let kq:=burnolAmbientCompletedMellinKernelFormula c
  let kr:=burnolRadiusAmbientCompletedMellinKernelFormula (waveRadius h) positive c
  have action:burnolMultiplicativeDilation (-h) kq=waveCharacter c h • kr:=by
    simpa only [kq,kr,waveCharacter,waveRadius,neg_neg,
      burnolAmbientCompletedMellinKernelFormula_eq_radiusSpecialization] using
      burnolRadiusAmbientKernel_dilation (by norm_num:(0:ℝ)<q) c (-h)
  have evenAction:burnolMultiplicativeDilation (-h) (burnolAmbientEvenPart kq)=
      waveCharacter c h • burnolAmbientEvenPart kr:=by
    unfold burnolAmbientEvenPart
    rw [map_smul,map_add,←reflectL2_burnolMultiplicativeDilation,action,map_smul]
    module
  have decomposition:compactWave c h=
      -waveCharacter c h • burnolAmbientEvenPart (kq-kr)-jumpCoefficient c • boxWave c h:=by
    unfold compactWave resolvedSource elementarySource boxWave
    change burnolMultiplicativeDilation (-h) (burnolAmbientEvenPart kq-jumpCoefficient c • Cq)-
      waveCharacter c h • (burnolAmbientEvenPart kq-jumpCoefficient c • Cq)=_
    rw [map_sub,map_smul,evenAction]
    unfold burnolAmbientEvenPart
    rw [map_sub]
    module
  have gapRaw:(burnolAmbientEvenPart (kq-kr):ℝ→ℂ)=ᵐ[volume]gapWindow c h:=
    by
    apply burnolEvenRaw_ae
    simpa only [kq,kr,burnolAmbientCompletedMellinKernelFormula_eq_radiusSpecialization] using
      burnolGapTailFiniteWindow_ae_source (by norm_num:(0:ℝ)<q) ordered c
  have source:=actual_compact_raw c h
  rw [decomposition] at source
  filter_upwards [source,Lp.coeFn_sub (-waveCharacter c h • burnolAmbientEvenPart (kq-kr))
    (jumpCoefficient c • boxWave c h),Lp.coeFn_smul (-waveCharacter c h) (burnolAmbientEvenPart (kq-kr)),
    Lp.coeFn_smul (jumpCoefficient c) (boxWave c h),gapRaw,box_wave_raw c h]
    with x compact difference scalar boxScalar gap box
  rw [difference,Pi.sub_apply,scalar,boxScalar,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,
    smul_eq_mul,gap,box] at compact
  exact compact.symm

theorem actual_compact_mass (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h):
    (∫x:ℝ,compactRaw c h x)=
      -jumpCoefficient c/2*((Real.exp (h/2):ℂ)-waveCharacter c h):=by
  have boxInt:Integrable (boxWaveRaw c h):=
    ((box_integrable _).const_mul _).sub ((box_integrable _).const_mul _)
  rw [integral_congr_ae (complete_wave_raw c h nn),integral_sub
      ((gap_window_integrable c h nn).const_mul _) (boxInt.const_mul _),
    integral_const_mul,gap_window_integral c h nn,mul_zero,zero_sub,
    integral_const_mul]
  unfold boxWaveRaw
  rw [integral_sub ((box_integrable _).const_mul _) ((box_integrable _).const_mul _),
    integral_const_mul,integral_const_mul,box_integral _ (by unfold waveRadius;positivity),
    box_integral q (by norm_num)]
  have phase:(Real.exp (-h/2):ℂ)*(2*waveRadius h:ℝ)=(Real.exp (h/2):ℂ)/2:=by
    have realPhase:Real.exp (-h/2)*(2*waveRadius h)=Real.exp (h/2)/2:=by
      calc
        _=(Real.exp (-h/2)*Real.exp h)/2:=by unfold waveRadius;ring
        _=_:=by rw [←Real.exp_add];congr 2;ring
    exact_mod_cast realPhase
  rw [phase]
  norm_num
  ring

theorem actual_compact_fourier_zero (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h):
    𝓕 (compactRaw c h) 0=
      -jumpCoefficient c/2*((Real.exp (h/2):ℂ)-waveCharacter c h):=by
  rw [Real.fourier_eq]
  simpa [VectorFourier.fourierIntegral] using actual_compact_mass c h nn

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Poisson.Mass
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
