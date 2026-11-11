import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Recovery

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open scoped Topology ENNReal InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "T" => burnolTateReciprocalL2
local notation "μq" => volume.restrict (symmetricInterval q)
local instance finiteQuarter : IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def quarterRaw (c : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval q).indicator (periodicRaw c)

private theorem resolved_measurable (c : BurnolCompletedMellinCoordinate) :
    Measurable (resolvedFourierRaw c) :=
  measurable_of_continuousOn_compl_singleton 0 (fun _ hx=>(actual_resolved_continuousAt c _ hx).continuousWithinAt)

private theorem periodic_measurable (c : BurnolCompletedMellinCoordinate) : Measurable (periodicRaw c) := by
  have aliasMeasurable : Measurable (aliasRaw c) := by
    apply Measurable.tsum
    intro k
    by_cases zero:k=0
    · subst k
      have same : aliasRawTerm c 0=(fun _:ℝ=>(0:ℂ)):=by funext x;simp [aliasRawTerm]
      rw [same]
      exact measurable_const
    · have same : aliasRawTerm c k=(fun x:ℝ=>resolvedFourierRaw c (x+k)):=by
        funext x;rw [aliasRawTerm,if_neg zero]
      rw [same]
      exact (resolved_measurable c).comp (measurable_id.add_const _)
  exact ((resolved_measurable c).add aliasMeasurable).sub measurable_const

theorem actual_quarter_raw (c : BurnolCompletedMellinCoordinate) :
    (quarterWave c:ℝ→ℂ)=ᵐ[volume]quarterRaw c := by
  have inside:∀ᵐx∂volume,x∈symmetricInterval q→periodicQuarter c x=periodicRaw c x:=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (actual_periodic_quarter_raw c)
  filter_upwards [burnolQuarterZeroExtension_coe (periodicQuarter c),inside] with x extended raw
  change burnolQuarterZeroExtension (periodicQuarter c) x=_
  rw [extended]
  by_cases member:x∈symmetricInterval q
  · rw [indicator_of_mem member,quarterRaw,indicator_of_mem member,raw member]
  · rw [indicator_of_notMem member,quarterRaw,indicator_of_notMem member]

theorem actual_quarter_measurable (c : BurnolCompletedMellinCoordinate) : Measurable (quarterRaw c) :=
  (periodic_measurable c).indicator (measurableSet_symmetricInterval q)

theorem actual_quarter_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    quarterRaw c (-x)=quarterRaw c x := by
  have same : -x∈symmetricInterval q↔x∈symmetricInterval q := by
    simp only [symmetricInterval,mem_Icc]
    constructor <;> rintro ⟨left,right⟩ <;> constructor <;> linarith
  by_cases member:x∈symmetricInterval q
  · unfold quarterRaw
    rw [indicator_of_mem member,indicator_of_mem (same.mpr member),actual_periodic_even]
  · unfold quarterRaw
    rw [indicator_of_notMem member,indicator_of_notMem (fun h=>member (same.mp h))]

theorem actual_quarter_outer_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (x : ℝ) (outside : q≤|x|) : quarterRaw c x=0 := by
  by_cases member:x∈symmetricInterval q
  · have equal : |x|=q:=le_antisymm (abs_le.mpr member) outside
    have alternatives:x=q∨x= -q := by
      rcases le_total 0 x with positive|negative
      · exact Or.inl (by simpa only [abs_of_nonneg positive] using equal)
      · exact Or.inr (by rw [abs_of_nonpos negative] at equal;linarith)
    rcases alternatives with positive|negative
    · rw [positive,quarterRaw,indicator_of_mem (by norm_num [symmetricInterval] : q∈symmetricInterval q),
        actual_original_periodic_zero_quarter c zero]
    · rw [negative,quarterRaw,indicator_of_mem (by norm_num [symmetricInterval] : -q∈symmetricInterval q),
        actual_periodic_even,actual_original_periodic_zero_quarter c zero]
  · exact indicator_of_notMem member _

def differenceRaw (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  (Real.exp (h/2):ℂ)*quarterRaw c (Real.exp h*x)-
    Complex.exp ((star c.value-1/2)*(h:ℂ))*quarterRaw c x

theorem actual_difference_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (waveDifference c h:ℝ→ℂ)=ᵐ[volume]differenceRaw c h := by
  have qmp : Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp h*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
      (r:=Real.exp h) (Real.exp_ne_zero h)
  filter_upwards [Lp.coeFn_sub (burnolMultiplicativeDilation h (quarterWave c))
    (Complex.exp ((star c.value-1/2)*(h:ℂ)) • quarterWave c),
    Lp.coeFn_smul (Complex.exp ((star c.value-1/2)*(h:ℂ))) (quarterWave c),
    burnolMultiplicativeDilation_coeFn h (quarterWave c),actual_quarter_raw c,
    qmp.ae (actual_quarter_raw c)] with x difference scalar dilation raw scaled
  change (burnolMultiplicativeDilation h (quarterWave c)-
    Complex.exp ((star c.value-1/2)*(h:ℂ)) • quarterWave c:BurnolL2) x=_
  rw [difference,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,dilation]
  unfold burnolL2RawNormalizedDilation
  rw [raw,scaled]
  rfl

theorem actual_difference_outer_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (x : ℝ) (outside : q≤|x|) : differenceRaw c h x=0 := by
  have moved : q≤|Real.exp h*x| := by
    rw [abs_mul,abs_of_pos (Real.exp_pos h)]
    exact outside.trans (le_mul_of_one_le_left (abs_nonneg x) (Real.one_le_exp_iff.mpr nonnegative))
  rw [differenceRaw,actual_quarter_outer_zero c zero _ moved,actual_quarter_outer_zero c zero x outside]
  simp

def tateRaw (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℝ→ℂ :=
  burnolTateReciprocalRaw (differenceRaw c h)
def tateSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 := T (waveDifference c h)

theorem actual_tate_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (tateSource c h:ℝ→ℂ)=ᵐ[volume]tateRaw c h := by
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (waveDifference c h))
    ((Lp.memLp (waveDifference c h)).ae_eq (actual_difference_raw c h)) (actual_difference_raw c h)
  exact (burnolTateReciprocalL2_coeFn (waveDifference c h)).trans pulled

theorem actual_tate_measurable (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Measurable (tateRaw c h) := by
  have difference:Measurable (differenceRaw c h):=
    (measurable_const.mul ((actual_quarter_measurable c).comp (measurable_const.mul measurable_id))).sub
      (measurable_const.mul (actual_quarter_measurable c))
  exact (Complex.measurable_ofReal.comp continuous_abs.measurable).inv.mul (difference.comp measurable_inv)

theorem actual_tate_even (c : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    tateRaw c h (-x)=tateRaw c h x := by
  unfold tateRaw burnolTateReciprocalRaw differenceRaw
  rw [abs_neg,inv_neg,mul_neg,actual_quarter_even,actual_quarter_even]

theorem actual_tate_gap (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) {x : ℝ} (inside : |x|≤4) : tateRaw c h x=0 := by
  by_cases atZero:x=0
  · subst x;simp [tateRaw,burnolTateReciprocalRaw]
  · have positive:0 < |x|:=abs_pos.mpr atZero
    have outside:q≤|x⁻¹| := by
      rw [abs_inv]
      exact (le_inv_comm₀ (by norm_num : (0:ℝ)<q) positive).mpr (by simpa using inside)
    rw [tateRaw,burnolTateReciprocalRaw,actual_difference_outer_zero c zero h nonnegative _ outside,mul_zero]

def reciprocalMean (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*tateRaw c h u
def countedRaw (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  burnolInnerGapForward (tateRaw c h) x-reciprocalMean c h

/-- The original comb producer consumes the full actual Tate source, including its own mean. -/
theorem actual_tate_copoisson_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (tateSource c h) test=∫x:ℝ,test x*countedRaw c h x :=
  burnolRemainderSourceRead_innerGap_forward _ _ (actual_tate_measurable c h) (actual_tate_raw c h)
    (fun {_} inside=>actual_tate_gap c zero h nonnegative (inside.trans (by norm_num)))
    (actual_tate_even c h) test

/-- This is the Fourier read of the original H_h source, not a substituted Pa representative. -/
theorem actual_difference_copoisson_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (waveDifference c h) (FourierTransform.fourier test)=
      ∫x:ℝ,test x*countedRaw c h x := by
  rw [←burnolRemainderSourceRead_fourier]
  exact actual_tate_copoisson_read c zero h nonnegative test

theorem actual_counted_gap (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (x : ℝ) (inside : |x|≤4) :
    countedRaw c h x= -reciprocalMean c h := by
  unfold countedRaw burnolInnerGapForward
  have terms:∀n:ℕ+,((n:ℕ):ℂ)⁻¹*tateRaw c h (x/(n:ℕ))=0 := by
    intro n
    have positive:(0:ℝ)<(n:ℕ):=by exact_mod_cast n.pos
    have one:(1:ℝ)≤(n:ℕ):=by exact_mod_cast (show (1:ℕ)≤(n:ℕ) from n.pos)
    have moved:|x/(n:ℕ)|≤4 := by
      rw [abs_div,abs_of_pos positive]
      exact (div_le_iff₀ positive).mpr (by nlinarith)
    rw [actual_tate_gap c zero h nonnegative moved,mul_zero]
  simp_rw [terms]
  simp

private theorem quarter_integrable (c : BurnolCompletedMellinCoordinate) : Integrable (quarterRaw c) := by
  apply (integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr
  exact ((Lp.memLp (periodicQuarter c)).integrable (by norm_num)).congr (actual_periodic_quarter_raw c)

private theorem half_mass (c : BurnolCompletedMellinCoordinate) :
    (∫x:ℝ in Ioi 0,quarterRaw c x)=quarterMean c/4 := by
  have negative:(∫x:ℝ in Iic 0,quarterRaw c x)=(∫x:ℝ in Ioi 0,quarterRaw c x) := by
    calc
      _=∫x:ℝ in Iic 0,quarterRaw c (-x) := setIntegral_congr_fun measurableSet_Iic
        (fun x _=>(actual_quarter_even c x).symm)
      _=_ := by simpa only [neg_zero] using integral_comp_neg_Iic 0 (quarterRaw c)
  have split := setIntegral_union (Iic_disjoint_Ioi (a:=(0:ℝ)) le_rfl) measurableSet_Ioi
    (quarter_integrable c).integrableOn (quarter_integrable c).integrableOn
  rw [Iic_union_Ioi,setIntegral_univ,negative] at split
  have mean:quarterMean c=2*(∫x:ℝ,quarterRaw c x) := by
    rw [quarterMean,Constructor.mean_integral]
    congr 1
    rw [quarterRaw,integral_indicator (measurableSet_symmetricInterval q)]
    exact integral_congr_ae (actual_periodic_quarter_raw c)
  rw [split] at mean
  linear_combination -mean/4

private theorem tate_reciprocal_integral (raw : ℝ→ℂ) :
    (∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*burnolTateReciprocalRaw raw u)=∫u:ℝ in Ioi 0,raw u := by
  calc
    _=∫u:ℝ in Ioi 0,(|(-1:ℝ)| *u^((-1:ℝ)-1)) • raw (u^(-1:ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u positive
      have positiveU : 0<u:=positive
      simp only [burnolTateReciprocalRaw,abs_of_pos positiveU,abs_neg,abs_one,one_mul,
        Real.rpow_neg_one]
      rw [show (-1:ℝ)-1= -2 by norm_num,Real.rpow_neg positiveU.le,Real.rpow_two]
      simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
      field_simp
    _=_ := integral_comp_rpow_Ioi raw (by norm_num)

/-- The single-side gap constant retains the complete original quarter mean and both clocks. -/
theorem actual_reciprocal_mean (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    reciprocalMean c h=((Real.exp (-h/2):ℂ)-Complex.exp ((star c.value-1/2)*(h:ℂ)))*quarterMean c/4 := by
  rw [reciprocalMean,tateRaw,tate_reciprocal_integral]
  have moved:Integrable (fun x:ℝ=>quarterRaw c (Real.exp h*x)) :=
    (quarter_integrable c).comp_mul_left' (Real.exp_ne_zero h)
  simp only [differenceRaw]
  rw [integral_sub (moved.const_mul _).integrableOn
    ((quarter_integrable c).const_mul _).integrableOn,
    integral_const_mul,integral_const_mul,integral_comp_mul_left_Ioi _ 0 (Real.exp_pos h),mul_zero,half_mass]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  have scalar:(Real.exp (h/2):ℂ)*(Real.exp h:ℂ)⁻¹=(Real.exp (-h/2):ℂ) := by
    rw [←Complex.ofReal_inv,←Complex.ofReal_mul,←Real.exp_neg,←Real.exp_add]
    congr 2
    ring
  calc
    _=((Real.exp (h/2):ℂ)*(Real.exp h:ℂ)⁻¹)*quarterMean c/4-
      Complex.exp ((star c.value-1/2)*(h:ℂ))*quarterMean c/4 := by ring
    _=_ := by rw [scalar];ring

private theorem tate_channel (c : BurnolCompletedMellinCoordinate) (h x : ℝ)
    (nonzero : x≠0) (n : ℕ) (positive : 0<n) :
    (n:ℂ)⁻¹*tateRaw c h (x/n)=((|x|:ℝ):ℂ)⁻¹*differenceRaw c h (n/x) := by
  have realPositive:(0:ℝ)<n:=by exact_mod_cast positive
  have natNe:(n:ℂ)≠0:=by exact_mod_cast positive.ne'
  have absNe:((|x|:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)
  rw [tateRaw,burnolTateReciprocalRaw,abs_div,abs_of_pos realPositive,inv_div,
    Complex.ofReal_div]
  push_cast
  field_simp

/-- Every co-sum at x is the complete finite lattice sample of the same H_h; the q endpoint is retained. -/
theorem actual_finite_lattice (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (x : ℝ) (nonzero : x≠0) (N : ℕ)
    (covered : |x|≤4*N) :
    countedRaw c h x=((|x|:ℝ):ℂ)⁻¹*(∑n∈Finset.range N,differenceRaw c h ((n+1)/x))-
      reciprocalMean c h := by
  unfold countedRaw burnolInnerGapForward
  congr 1
  rw [←Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
    (fun n:ℕ+=>((n:ℕ):ℂ)⁻¹*tateRaw c h (x/(n:ℕ)))]
  change (∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*tateRaw c h (x/(n+1:ℕ)))=_
  rw [tsum_eq_sum (s:=Finset.range N) (fun n outside=>by
    have bound:N≤n:=le_of_not_gt (fun member=>outside (Finset.mem_range.mpr member))
    have moved:|x/(n+1:ℕ)|≤4 := by
      have positive:(0:ℝ)<(n+1:ℕ):=by positivity
      rw [abs_div,abs_of_pos positive]
      apply (div_le_iff₀ positive).mpr
      have realBound:(N:ℝ)≤n:=by exact_mod_cast bound
      push_cast
      nlinarith
    rw [actual_tate_gap c zero h nonnegative moved,mul_zero])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [Nat.cast_add,Nat.cast_one] using tate_channel c h x nonzero (n+1) (by omega)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
