import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
open scoped Topology InnerProductSpace ENNReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def rawMean (raw:ℝ→ℂ):ℂ:=2*∫x:ℝ,raw x ∂μq

def powerRaw (w:ℂ) (x:ℝ):ℂ:=((|x|:ℝ):ℂ)^(-star w)

theorem actual_power_measurable (w:ℂ):Measurable (powerRaw w):=by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x outside
  have ne:x≠0:=by simpa only [mem_compl_iff,mem_singleton_iff] using outside
  have power:ContinuousAt (fun y:ℝ=>(y:ℂ)^(-star w)) |x|:=
    continuousAt_ofReal_cpow_const |x| (-star w) (Or.inr (abs_ne_zero.mpr ne))
  exact (power.comp continuous_abs.continuousAt).continuousWithinAt

theorem actual_power_integrable (w:ℂ) (below:w.re<1):Integrable (powerRaw w) μq:=by
  have base:IntervalIntegrable (fun x:ℝ=>(x:ℂ)^((-w.re:ℝ):ℂ)) volume (-q) q:=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [ofReal_re];linarith)
  have majorant:Integrable (fun x:ℝ=>|x|^(-w.re)) μq:=by
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-q:ℝ)≤q)).mp base.norm).congr
    filter_upwards with x
    simp only [Complex.norm_cpow_real,Complex.norm_real,Real.norm_eq_abs]
  apply majorant.mono' (actual_power_measurable w).aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x ne
  rw [powerRaw,Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr ne)]
  simp only [neg_re,star_def,conj_re]
  exact le_rfl

def seedRaw (w:ℂ) (x:ℝ):ℂ:=(1/2:ℂ)*(powerRaw w x-rawMean (powerRaw w))

theorem actual_seed_integrable (w:ℂ) (below:w.re<1):Integrable (seedRaw w) μq:=
  ((actual_power_integrable w below).sub (integrable_const _)).const_mul _

theorem actual_seed_mean (w:ℂ) (below:w.re<1): (∫x:ℝ,seedRaw w x ∂μq)=0:=by
  simp only [seedRaw,integral_const_mul]
  rw [integral_sub (actual_power_integrable w below) (integrable_const _),integral_const,
    burnolRadiusInterval_measureReal_univ (by norm_num : (0:ℝ)<q),Complex.real_smul,rawMean]
  norm_num
  ring

theorem actual_seed_even (w:ℂ) (x:ℝ):seedRaw w (-x)=seedRaw w x:=by
  simp only [seedRaw,powerRaw,abs_neg]

def centeredFourierRaw (raw:ℝ→ℂ) (x:ℝ):ℂ:=
  Constructor.fourierRaw raw x-rawMean (Constructor.fourierRaw raw)

theorem actual_fourier_continuous (raw:ℝ→ℂ) (domain:Integrable raw μq):
    Continuous (Constructor.fourierRaw raw):=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner domain

theorem actual_centered_continuous (raw:ℝ→ℂ) (domain:Integrable raw μq):
    Continuous (centeredFourierRaw raw):=
  (actual_fourier_continuous raw domain).sub continuous_const

def smooth (raw:ℝ→ℂ) (domain:Integrable raw μq):M:=
  Constructor.zeroMean (Constructor.compact (Constructor.fourierRaw raw) (actual_fourier_continuous raw domain))

theorem actual_smooth_raw (raw:ℝ→ℂ) (domain:Integrable raw μq):
    (smooth raw domain:ℝ→ℂ)=ᵐ[μq]centeredFourierRaw raw:=by
  rw [smooth,Constructor.zeroMean_read]
  have mean:burnolQuarterMeanCoefficient
      (Constructor.compact (Constructor.fourierRaw raw) (actual_fourier_continuous raw domain))=
      rawMean (Constructor.fourierRaw raw):=by
    rw [Constructor.mean_integral,integral_congr_ae (Constructor.compact_read _ _)]
    rfl
  filter_upwards [Lp.coeFn_sub
    (Constructor.compact (Constructor.fourierRaw raw) (actual_fourier_continuous raw domain))
    (burnolQuarterMeanCoefficient
      (Constructor.compact (Constructor.fourierRaw raw) (actual_fourier_continuous raw domain)) • intervalConstant q),
    Lp.coeFn_smul (burnolQuarterMeanCoefficient
      (Constructor.compact (Constructor.fourierRaw raw) (actual_fourier_continuous raw domain))) (intervalConstant q),
    intervalConstant_coeFn q,Constructor.compact_read (Constructor.fourierRaw raw) (actual_fourier_continuous raw domain)]
    with x subtracted scalar constant source
  rw [subtracted,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one,source,mean]
  rfl

theorem actual_centered_domain (raw:ℝ→ℂ) (domain:Integrable raw μq):
    Integrable (centeredFourierRaw raw) μq:=
  (actual_centered_continuous raw domain).integrableOn_Icc

theorem actual_smooth_congr (f g:ℝ→ℂ) (hf:Integrable f μq) (hg:Integrable g μq)
    (same:f=ᵐ[μq]g):smooth f hf=smooth g hg:=by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [actual_smooth_raw f hf,actual_smooth_raw g hg] with x left right
  rw [left,right,centeredFourierRaw,centeredFourierRaw,Constructor.fourierRaw_congr f g same]

theorem actual_smooth_add (f g:ℝ→ℂ) (hf:Integrable f μq) (hg:Integrable g μq):
    smooth (fun x=>f x+g x) (hf.add hg)=smooth f hf+smooth g hg:=by
  have add:Constructor.fourierRaw (fun x=>f x+g x)=Constructor.fourierRaw f+Constructor.fourierRaw g:=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner hf hg
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [actual_smooth_raw (fun x=>f x+g x) (hf.add hg),
    actual_smooth_raw f hf,actual_smooth_raw g hg,
    Lp.coeFn_add (smooth f hf:Hq) (smooth g hg:Hq)] with x source left right added
  rw [source]
  change centeredFourierRaw (fun x=>f x+g x) x=((smooth f hf:Hq)+(smooth g hg:Hq)) x
  rw [added,Pi.add_apply,left,right]
  simp only [centeredFourierRaw,add,Pi.add_apply,rawMean]
  have fd:Integrable (Constructor.fourierRaw f) μq:=(actual_fourier_continuous f hf).integrableOn_Icc
  have gd:Integrable (Constructor.fourierRaw g) μq:=(actual_fourier_continuous g hg).integrableOn_Icc
  rw [integral_add fd gd]
  ring

theorem actual_smooth_state (state:M):
    smooth (state:ℝ→ℂ) ((Lp.memLp (state:Hq)).integrable (by norm_num))=S state:=by
  apply Subtype.ext
  apply Lp.ext
  have read:=Constructor.truncatedFourier_read (state:Hq)
  have mean:rawMean (Constructor.fourierRaw (state:Hq))=
      burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:Hq)):=by
    rw [Constructor.mean_integral,integral_congr_ae read]
    rfl
  filter_upwards [actual_smooth_raw (state:ℝ→ℂ) ((Lp.memLp (state:Hq)).integrable (by norm_num)),
    burnolMeanZeroFourier_ae_raw state] with x left right
  rw [left,right,centeredFourierRaw,mean]
  rfl

theorem actual_smooth_centered (raw:ℝ→ℂ) (domain:Integrable raw μq):
    smooth (centeredFourierRaw raw) (actual_centered_domain raw domain)=S (smooth raw domain):=by
  rw [←actual_smooth_state (smooth raw domain)]
  exact actual_smooth_congr _ _ _ _ (actual_smooth_raw raw domain).symm

def firstSource (w:ℂ) (below:w.re<1):M:=smooth (seedRaw w) (actual_seed_integrable w below)

def correction (w:ℂ) (below:w.re<1):M:=BI (S (firstSource w below))

theorem actual_correction_equation (w:ℂ) (below:w.re<1):
    correction w below-S (S (correction w below))=S (firstSource w below):=by
  change (burnolMeanZeroOneMinusSquare*BI) (S (firstSource w below))=_
  rw [burnolMeanZeroBlockInverse_right]
  rfl

def correctionRaw (w:ℂ) (below:w.re<1) (x:ℝ):ℂ:=
  burnolMeanZeroFourierRaw (firstSource w below) x+
    burnolMeanZeroFourierRaw (S (correction w below)) x

theorem actual_correction_raw (w:ℂ) (below:w.re<1):
    (correction w below:ℝ→ℂ)=ᵐ[μq]correctionRaw w below:=by
  have split:correction w below=S (firstSource w below)+S (S (correction w below)):=
    sub_eq_iff_eq_add.mp (actual_correction_equation w below)
  have cast:((correction w below):Hq)=(S (firstSource w below):Hq)+(S (S (correction w below)):Hq):=
    congrArg (fun a:M=>(a:Hq)) split
  rw [cast]
  filter_upwards [Lp.coeFn_add (S (firstSource w below):Hq) (S (S (correction w below)):Hq),
    burnolMeanZeroFourier_ae_raw (firstSource w below),burnolMeanZeroFourier_ae_raw (S (correction w below))]
    with x added first second
  rw [added,Pi.add_apply,first,second]
  rfl

theorem actual_correction_continuous (w:ℂ) (below:w.re<1):Continuous (correctionRaw w below):=
  ((burnolRadiusTruncatedFourierRaw_continuous _).sub continuous_const).add
    ((burnolRadiusTruncatedFourierRaw_continuous _).sub continuous_const)

def dualRaw (w:ℂ) (below:w.re<1) (x:ℝ):ℂ:=seedRaw w x+correctionRaw w below x

theorem actual_dual_integrable (w:ℂ) (below:w.re<1):Integrable (dualRaw w below) μq:=
  (actual_seed_integrable w below).add (actual_correction_continuous w below).integrableOn_Icc

theorem actual_dual_mean (w:ℂ) (below:w.re<1):(∫x:ℝ,dualRaw w below x ∂μq)=0:=by
  simp only [dualRaw]
  rw [integral_add (actual_seed_integrable w below)
    (actual_correction_continuous w below).integrableOn_Icc,actual_seed_mean w below,zero_add,
    ←integral_congr_ae (actual_correction_raw w below)]
  have mean:=Constructor.mean_zero (correction w below)
  rw [Constructor.mean_integral] at mean
  exact (mul_eq_zero.mp mean).resolve_left (by norm_num)

theorem actual_dual_action (w:ℂ) (below:w.re<1):
    (fun x:ℝ=>dualRaw w below x-centeredFourierRaw (centeredFourierRaw (dualRaw w below)) x)=ᵐ[μq]seedRaw w:=by
  have bDomain:Integrable (correctionRaw w below) μq:=(actual_correction_continuous w below).integrableOn_Icc
  have first:smooth (dualRaw w below) (actual_dual_integrable w below)=
      firstSource w below+S (correction w below):=by
    change smooth (fun x=>seedRaw w x+correctionRaw w below x)
      ((actual_seed_integrable w below).add bDomain)=_
    rw [actual_smooth_add _ _ (actual_seed_integrable w below) bDomain,
      actual_smooth_congr (correctionRaw w below) (correction w below)
        bDomain ((Lp.memLp (correction w below:Hq)).integrable (by norm_num))
        (actual_correction_raw w below).symm,actual_smooth_state]
    rfl
  have second:smooth (centeredFourierRaw (dualRaw w below))
      (actual_centered_domain _ (actual_dual_integrable w below))=correction w below:=by
    rw [actual_smooth_centered _ (actual_dual_integrable w below),first,map_add]
    exact (sub_eq_iff_eq_add.mp (actual_correction_equation w below)).symm
  have read:=actual_smooth_raw (centeredFourierRaw (dualRaw w below))
    (actual_centered_domain _ (actual_dual_integrable w below))
  rw [second] at read
  filter_upwards [read,actual_correction_raw w below] with x action raw
  rw [←action,raw,dualRaw]
  ring

private theorem weighted_power_memLp (w:ℂ) (below:w.re<1):
    MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*powerRaw w x) 2 μq:=by
  apply MemLp.of_bound
    ((Complex.continuous_ofReal.comp continuous_abs).measurable.mul (actual_power_measurable w)).aestronglyMeasurable
    (q^(1-w.re))
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℝ)),
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x ne inside
  change ‖((|x|:ℝ):ℂ)*powerRaw w x‖≤q^(1-w.re)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_abs,powerRaw,
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr ne)]
  simp only [neg_re,star_def,conj_re]
  nth_rw 1 [←Real.rpow_one (|x|)]
  rw [←Real.rpow_add (abs_pos.mpr ne)]
  exact Real.rpow_le_rpow (abs_nonneg x) (abs_le.mpr inside) (by linarith)

theorem actual_dual_weighted_memLp (w:ℂ) (below:w.re<1):
    MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*dualRaw w below x) 2 μq:=by
  have weight:MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)) 2 μq:=
    Constructor.continuous_memLp _ (Complex.continuous_ofReal.comp continuous_abs)
  have seed:MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*seedRaw w x) 2 μq:=by
    apply (((weighted_power_memLp w below).sub (weight.mul_const (rawMean (powerRaw w)))).const_mul (1/2:ℂ)).ae_eq
    filter_upwards with x
    dsimp only [Pi.sub_apply,seedRaw]
    ring
  have corrected:MemLp (fun x:ℝ=>((|x|:ℝ):ℂ)*correctionRaw w below x) 2 μq:=
    Constructor.continuous_memLp _ ((Complex.continuous_ofReal.comp continuous_abs).mul
      (actual_correction_continuous w below))
  apply (seed.add corrected).ae_eq
  filter_upwards with x
  dsimp only [Pi.add_apply,dualRaw]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
