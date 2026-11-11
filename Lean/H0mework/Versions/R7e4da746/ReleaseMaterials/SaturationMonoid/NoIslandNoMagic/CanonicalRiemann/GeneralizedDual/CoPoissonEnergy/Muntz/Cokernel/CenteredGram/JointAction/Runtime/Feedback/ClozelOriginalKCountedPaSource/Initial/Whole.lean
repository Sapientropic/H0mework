import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.Mixed
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.Tail
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.HarmonicRealization
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContinuousChannels
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial
open Complex Filter MeasureTheory Set
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped BigOperators Topology InnerProductSpace
local notation "q" => (1/4:ℝ)

/-- The two original parity fields stay independent; no Fourier-fixed averaging is used. -/
def testRaw (parity:Fin 2) (l u x:ℝ) : ℂ :=
  if parity=0 then burnolReciprocalStepWaveRaw l u x else burnolHarmonicStepWaveRaw l u x

def testField (parity:Fin 2) (l u:ℝ) : BurnolL2 :=
  if parity=0 then burnolReciprocalStepNativeWave l u else fourierL2 (burnolReciprocalStepNativeWave l u)

def pairRaw (parity:Fin 2) (l u b x:ℝ) : ℂ :=
  star (testRaw parity l u x)*burnolHarmonicStepWaveRaw 1 (3/2) (b*x)

/-- Arithmetic values use only interval incidences and their complete finite mean bill. -/
def windowBill (parity:Fin 2) (l u b L:ℝ) : ℂ :=
  if parity=0 then
    mixedIncidence L (Finset.Icc 1 ⌈u*L⌉₊) (Finset.Icc 1 ⌊L/(1/b)⌋₊)
      (fun _=>1) (fun n:ℕ=>(n:ℝ)/u) (fun n:ℕ=>(n:ℝ)/l) (u-l)
      (fun n:ℕ=>(n:ℂ)⁻¹) (fun n=>(n:ℝ)*(1/b)) (fun n=>(n:ℝ)*((3/2)/b)) (Real.log (((3/2)/b)/(1/b)))
  else
    incidence L (Finset.Icc 1 ⌊L/l⌋₊) (Finset.Icc 1 ⌊L/(1/b)⌋₊)
      (fun n:ℕ=>(n:ℂ)⁻¹) (fun n=>(n:ℝ)*l) (fun n=>(n:ℝ)*u) (Real.log (u/l))
      (fun n:ℕ=>(n:ℂ)⁻¹) (fun n=>(n:ℝ)*(1/b)) (fun n=>(n:ℝ)*((3/2)/b)) (Real.log (((3/2)/b)/(1/b)))

def arithmeticApprox (parity:Fin 2) (l u b:ℝ) (M:ℕ) : ℂ :=
  2*windowBill parity l u b (wholeCutoff ((M:ℝ)+8) b)

def arithmeticKernel (parity:Fin 2) (l u b:ℝ) : ℂ :=
  limUnder atTop (arithmeticApprox parity l u b)

private theorem harmonic_scale (l u b x:ℝ) (hl:0<l) (hu:0<u) (hb:0<b) :
    burnolHarmonicStepWaveRaw l u (b*x)=burnolHarmonicStepWaveRaw (l/b) (u/b) x := by
  have low:|b*x|/l=|x|/(l/b) := by rw [abs_mul,abs_of_pos hb];field_simp
  have high:|b*x|/u=|x|/(u/b) := by rw [abs_mul,abs_of_pos hb];field_simp
  have ratio:(u/b)/(l/b)=u/l := by field_simp
  simp only [burnolHarmonicStepWaveRaw,burnolHarmonicStepChannels,low,high,ratio]

theorem windowBill_read (parity:Fin 2) (l u b L:ℝ) (hl:0<l) (hu:0<u) (hb:0<b) :
    windowBill parity l u b L=∫ x:ℝ in Ico 0 L,pairRaw parity l u b x := by
  simp_rw [pairRaw,harmonic_scale 1 (3/2) b _ (by norm_num) (by norm_num) hb]
  by_cases p:parity=0
  · simp only [windowBill,testRaw,if_pos p]
    exact (mixed_window_incidence l u (1/b) ((3/2)/b) L hl hu (by positivity) (by positivity)).symm
  · simp only [windowBill,testRaw,if_neg p]
    exact (harmonic_window_incidence l u (1/b) ((3/2)/b) L hl hu (by positivity) (by positivity)).symm

private theorem testField_read (parity:Fin 2) (l u:ℝ) (hl:q<l) (ordered:l≤u) (upper:u≤4) :
    (testField parity l u:ℝ→ℂ)=ᵐ[volume] testRaw parity l u := by
  change _ =ᵐ[volume] (fun x => testRaw parity l u x)
  by_cases p:parity=0
  · simp only [testField,testRaw,if_pos p]
    rw [burnolReciprocalStepNativeWave_eq l u (by linarith) ordered]
    exact (burnolReciprocalStepWave_memLp l u (by linarith) ordered).coeFn_toLp
  · simp only [testField,testRaw,if_neg p]
    exact burnolReciprocalStepFourier_coeFn l u hl ordered upper

/-- The exact 1/sqrt(a) in channel1 cancels its actual dilation amplitude. -/
theorem channel1_read (value:BurnolL2) (raw:ℝ→ℂ) (same:(value:ℝ→ℂ)=ᵐ[volume] raw)
    (b:ℝ) (hb:0<b) :
    (ContinuousChannels.channel 1 b value:ℝ→ℂ)=ᵐ[volume] fun x => raw (b*x) := by
  have qmp:=Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=b) hb.ne'
  have pulled:∀ᵐ x : ℝ ∂volume,value (b*x)=raw (b*x) := by simpa only [smul_eq_mul] using qmp.ae same
  have amplitude:Real.exp (Real.log b/2)=Real.sqrt b := by rw [Real.exp_half,Real.exp_log hb]
  filter_upwards [Lp.coeFn_smul ((Real.sqrt b:ℂ)⁻¹) (burnolMultiplicativeDilation (Real.log b) value),
    burnolMultiplicativeDilation_coeFn (Real.log b) value,pulled] with x smulRead dilationRead sourceRead
  simp only [ContinuousChannels.channel,one_mul]
  change (((Real.sqrt b:ℂ)⁻¹) • burnolMultiplicativeDilation (Real.log b) value:BurnolL2) x=_
  rw [smulRead]
  change (Real.sqrt b:ℂ)⁻¹*burnolMultiplicativeDilation (Real.log b) value x=_
  rw [dilationRead,burnolL2RawNormalizedDilation,Real.exp_log hb,amplitude,sourceRead]
  have nonzero:(Real.sqrt b:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  rw [←mul_assoc,inv_mul_cancel₀ nonzero,one_mul]

private theorem harmonic_seed_read (b:ℝ) (hb:0<b) :
    (ContinuousChannels.channel 1 b (fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))):ℝ→ℂ)=ᵐ[volume]
      fun x => burnolHarmonicStepWaveRaw 1 (3/2) (b*x) :=
  channel1_read _ _ (burnolReciprocalStepFourier_coeFn 1 (3/2) (by norm_num) (by norm_num) (by norm_num)) b hb

private theorem pair_native (parity:Fin 2) (l u b:ℝ) (hl:q<l) (ordered:l≤u) (upper:u≤4) (hb:0<b) :
    (fun x:ℝ=>inner ℂ (testField parity l u x)
      (ContinuousChannels.channel 1 b (fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) x))=ᵐ[volume]
        pairRaw parity l u b := by
  filter_upwards [testField_read parity l u hl ordered upper,harmonic_seed_read b hb] with x left right
  rw [left,right,RCLike.inner_apply,starRingEnd_apply,mul_comm]
  rfl

private theorem pair_integrable (parity:Fin 2) (l u b:ℝ) (hl:q<l) (ordered:l≤u) (upper:u≤4) (hb:0<b) :
    Integrable (pairRaw parity l u b) :=
  (L2.integrable_inner (𝕜:=ℂ) (testField parity l u)
    (ContinuousChannels.channel 1 b (fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))))).congr
      (pair_native parity l u b hl ordered upper hb)

private theorem pair_even (parity:Fin 2) (l u b x:ℝ) :
    pairRaw parity l u b (-x)=pairRaw parity l u b x := by
  simp [pairRaw,testRaw,burnolHarmonicStepWaveRaw,burnolHarmonicStepChannels,
    burnolReciprocalStepWaveRaw,burnolReciprocalStepWaveReal,burnolReciprocalStepChannels,mul_neg]

private theorem even_integral (f:ℝ→ℂ) (hf:Integrable f) (even:∀x,f (-x)=f x) :
    (∫x:ℝ,f x)=2*(∫x:ℝ in Ioi 0,f x) := by
  have reflected:(fun x:ℝ=>(Iio (0:ℝ)).indicator f x)=
      (fun x:ℝ=>(Ioi (0:ℝ)).indicator f (-x)) := by
    funext x
    by_cases h:x<0
    · have negpos : 0 < -x := by linarith
      simp only [indicator_apply,mem_Iio,mem_Ioi,if_pos h,if_pos negpos,even]
    · have negpos : ¬ 0 < -x := by linarith
      simp only [indicator_apply,mem_Iio,mem_Ioi,if_neg h,if_neg negpos]
  have equal:(∫x:ℝ in Iio 0,f x)=(∫x:ℝ in Ioi 0,f x) := by
    rw [←integral_indicator measurableSet_Iio,reflected,integral_neg_eq_self,
      integral_indicator measurableSet_Ioi]
  have total:=integral_add_compl (s:=Ioi (0:ℝ)) measurableSet_Ioi hf
  rw [compl_Ioi,integral_Iic_eq_integral_Iio,equal] at total
  linear_combination -total

private theorem pair_tail_point (parity:Fin 2) (l u b M x:ℝ) (hl:0<l) (ordered:l≤u) (upper:u≤4)
    (hb:0<b) (hM:8≤M) (outside:wholeCutoff M b≤|x|) :
    ‖pairRaw parity l u b x‖≤96/(b*|x|^2) := by
  have positive:0 < |x| := by
    have cutoff:M≤wholeCutoff M b := by unfold wholeCutoff;have:=one_div_pos.mpr hb;nlinarith
    linarith
  have denominator:0<b*|x|^2:=by positivity
  by_cases p:parity=0
  · simp only [pairRaw,testRaw,if_pos p]
    exact (mixed_product_tail l u b M x hl ordered hb hM outside).trans
      (div_le_div_of_nonneg_right (by norm_num : (6:ℝ)≤96) denominator.le)
  · simp only [pairRaw,testRaw,if_neg p]
    exact (harmonic_product_tail l u b M x hl ordered upper hb hM outside).trans
      (div_le_div_of_nonneg_right (by linarith : 24*u≤96) denominator.le)

private theorem inverse_square_integral (L b:ℝ) (hL:0<L) (hb:0<b) :
    IntegrableOn (fun x:ℝ=>96/(b*x^2)) (Ioi L) ∧
      (∫x:ℝ in Ioi L,96/(b*x^2))=96/(b*L) := by
  have point:∀ᵐ x : ℝ ∂volume.restrict (Ioi L),96/(b*x^2)=(96/b)*x^(-2:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.rpow_neg (hL.trans hx).le,Real.rpow_two]
    field_simp
  have integrable:= (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hL).const_mul (96/b)
  refine ⟨integrable.congr (point.mono (fun _ h=>h.symm)),?_⟩
  rw [integral_congr_ae point,integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hL]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

/-- The entire product tail is integrated; separate global mean integrals are never formed. -/
theorem whole_tail (parity:Fin 2) (l u b M:ℝ) (hl:q<l) (ordered:l≤u) (upper:u≤4) (hb:0<b) (hM:8≤M) :
    ‖∫x:ℝ in Ioi (wholeCutoff M b),pairRaw parity l u b x‖≤96/M := by
  have positiveM:0<M:=by linarith
  have positiveL:0<wholeCutoff M b:=by unfold wholeCutoff;positivity
  have native:=pair_integrable parity l u b hl ordered upper hb
  have bound:=inverse_square_integral (wholeCutoff M b) b positiveL hb
  calc
    _ ≤ ∫x:ℝ in Ioi (wholeCutoff M b),‖pairRaw parity l u b x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫x:ℝ in Ioi (wholeCutoff M b),96/(b*x^2) := by
      apply integral_mono_ae native.norm.integrableOn bound.1
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have xpos:0<x:=positiveL.trans hx
      simpa only [abs_of_pos xpos] using pair_tail_point parity l u b M x
        (by linarith) ordered upper hb hM (by rw [abs_of_pos xpos];exact hx.le)
    _ = 96/(b*wholeCutoff M b) := bound.2
    _ ≤ 96/M := by
      have scale:b*wholeCutoff M b=M*(b+1):=by unfold wholeCutoff;field_simp
      rw [scale]
      exact div_le_div_of_nonneg_left (by norm_num) positiveM (by nlinarith)

private theorem positive_split (f:ℝ→ℂ) (hf:Integrable f) (L:ℝ) (hL:0<L) :
    (∫x:ℝ in Ioi 0,f x)=(∫x:ℝ in Ico 0 L,f x)+(∫x:ℝ in Ioi L,f x) := by
  have disjoint:Disjoint (Ioc (0:ℝ) L) (Ioi L) := by
    apply Set.disjoint_left.mpr
    intro x hx hafter
    exact (not_lt_of_ge hx.2) hafter
  have together:Ioc (0:ℝ) L∪Ioi L=Ioi 0 := by
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h);exact h.1;exact hL.trans h
    · intro h
      by_cases htop:x≤L
      · exact Or.inl ⟨h,htop⟩
      · exact Or.inr (lt_of_not_ge htop)
  have both:=setIntegral_union disjoint measurableSet_Ioi hf.integrableOn hf.integrableOn
  rw [together,←integral_Ico_eq_integral_Ioc] at both
  exact both

/-- Finite arithmetic bills approximate the complete source pairing at an all-scale explicit rate. -/
theorem arithmetic_error (parity:Fin 2) (l u b:ℝ) (hl:q<l) (ordered:l≤u) (upper:u≤4) (hb:0<b) (M:ℕ) :
    ‖arithmeticApprox parity l u b M-∫x:ℝ,pairRaw parity l u b x‖≤192/((M:ℝ)+8) := by
  have hM:(8:ℝ)≤(M:ℝ)+8:=by linarith [Nat.cast_nonneg (α:=ℝ) M]
  have cutoff:0<wholeCutoff ((M:ℝ)+8) b:=by unfold wholeCutoff;positivity
  have native:=pair_integrable parity l u b hl ordered upper hb
  have complete:=even_integral _ native (pair_even parity l u b)
  have split:=positive_split _ native _ cutoff
  rw [arithmeticApprox,windowBill_read parity l u b _ (by linarith) (by linarith) hb,complete,split]
  have algebra (x y:ℂ):2*x-2*(x+y)=-(2*y):=by ring
  rw [algebra,norm_neg,norm_mul]
  norm_num only [norm_ofNat]
  have bound:=whole_tail parity l u b ((M:ℝ)+8) hl ordered upper hb hM
  calc
    2*‖∫x:ℝ in Ioi (wholeCutoff ((M:ℝ)+8) b),pairRaw parity l u b x‖≤2*(96/((M:ℝ)+8)) := by gcongr
    _ = _ := by ring

theorem arithmetic_tendsto (parity:Fin 2) (l u b:ℝ) (hl:q<l) (ordered:l≤u) (upper:u≤4) (hb:0<b) :
    Tendsto (arithmeticApprox parity l u b) atTop (𝓝 (∫x:ℝ,pairRaw parity l u b x)) := by
  have upperLimit:Tendsto (fun M:ℕ=>192/((M:ℝ)+8)) atTop (𝓝 (0:ℝ)) := by
    simp_rw [div_eq_mul_inv]
    have inverse: Tendsto (fun M:ℕ=>((M:ℝ)+8)⁻¹) atTop (𝓝 (0:ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 8 tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using inverse.const_mul 192
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun M=>norm_nonneg _) (arithmetic_error parity l u b hl ordered upper hb) upperLimit)

/-- The independently calculated whole kernel is consumed on the true original source fields. -/
theorem arithmeticKernel_read (parity:Fin 2) (l u b:ℝ) (hl:q<l) (ordered:l≤u) (upper:u≤4) (hb:0<b) :
    arithmeticKernel parity l u b=inner ℂ (testField parity l u)
      (ContinuousChannels.channel 1 b (fourierL2 (burnolReciprocalStepNativeWave 1 (3/2)))) := by
  unfold arithmeticKernel
  rw [(arithmetic_tendsto parity l u b hl ordered upper hb).limUnder_eq,L2.inner_def]
  exact integral_congr_ae (pair_native parity l u b hl ordered upper hb).symm

end CountedPaInitial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
