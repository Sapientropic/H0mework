import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Completion
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
open scoped Topology ENNReal InnerProductSpace
open private tate_reciprocal_integral from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
open private innerGapWeight_memLp from
  H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Recovery
local notation "q" => (1/4:ℝ)

private theorem counted_even (c : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    countedRaw c h (-x)=countedRaw c h x := by
  unfold countedRaw burnolInnerGapForward
  congr 1
  apply tsum_congr
  intro n
  rw [neg_div,actual_tate_even]

private theorem counted_abs (c : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    countedRaw c h x=countedRaw c h |x| := by
  rcases le_total 0 x with positive|negative
  · rw [abs_of_nonneg positive]
  · rw [abs_of_nonpos negative,counted_even]

private theorem mean_profile (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (f : ℝ→ℂ)
    (same : ∀x:ℝ,x≠0→f x=differenceRaw c h x) :
    reciprocalMean c h=∫u:ℝ in (0:ℝ)..q,f u := by
  rw [reciprocalMean,tateRaw,tate_reciprocal_integral]
  have cutoff : EqOn (differenceRaw c h) ((Ioc (0:ℝ) q).indicator (differenceRaw c h)) (Ioi 0) := by
    intro x positive
    by_cases inside:x≤q
    · exact (indicator_of_mem (show x∈Ioc (0:ℝ) q from ⟨positive,inside⟩) _).symm
    · rw [indicator_of_notMem (show x∉Ioc (0:ℝ) q from fun member=>inside member.2),
        actual_difference_outer_zero c zero h nonnegative x]
      rw [abs_of_pos positive]
      exact (lt_of_not_ge inside).le
  rw [setIntegral_congr_fun measurableSet_Ioi cutoff,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]
  exact setIntegral_congr_fun measurableSet_Ioc (fun x hx=>(same x hx.1.ne').symm)

private theorem counted_quadrature (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (f : ℝ→ℂ)
    (same : ∀x:ℝ,x≠0→f x=differenceRaw c h x) (x : ℝ) (positive : 0<x) :
    countedRaw c h x=(x:ℂ)⁻¹*((∑n∈Finset.Icc 1 ⌊q/x⁻¹⌋₊,f ((n:ℝ)*x⁻¹))-
      (x:ℂ)*(∫u:ℝ in (0:ℝ)..q,f u)) := by
  let N:ℕ:=⌊q*x⌋₊
  have next:q*x<(N:ℝ)+1:=Nat.lt_floor_add_one _
  have covered:|x|≤4*(N+1:ℕ) := by rw [abs_of_pos positive];push_cast;nlinarith
  have source:=actual_finite_lattice c zero h nonnegative x positive.ne' (N+1) covered
  rw [Finset.sum_range_succ] at source
  have tail:q≤|((N+1:ℕ):ℝ)/x| := by
    rw [abs_of_nonneg (by positivity)]
    apply (le_div_iff₀ positive).mpr
    push_cast
    exact next.le
  norm_num only [Nat.cast_add,Nat.cast_one] at tail
  rw [actual_difference_outer_zero c zero h nonnegative _ tail,add_zero,abs_of_pos positive,
    mean_profile c zero h nonnegative f same] at source
  have index : ⌊q/x⁻¹⌋₊=N:=by rw [div_inv_eq_mul]
  have sum : (∑n∈Finset.range N,differenceRaw c h ((n+1)/x))=
      ∑n∈Finset.Icc 1 N,f ((n:ℝ)*x⁻¹) := by
    rw [show Finset.Icc 1 N=Finset.Ico 1 (N+1) from by
      ext n
      simp only [Finset.mem_Icc,Finset.mem_Ico]
      omega,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro n _
    have nonzero:((1+n:ℕ):ℝ)*x⁻¹≠0:=mul_ne_zero (by positivity) (inv_ne_zero positive.ne')
    rw [same _ nonzero]
    congr 1
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    ring
  rw [source,index,sum]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']

private theorem counted_tail_bound (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (f : ℝ→ℂ)
    (same : ∀x:ℝ,x≠0→f x=differenceRaw c h x) (regular : ContinuousOn f (Icc 0 q))
    (L B : ℝ) (lnonnegative : 0≤L) (bnonnegative : 0≤B)
    (lipschitz : ∀x∈Icc 0 q,∀y∈Icc 0 q,‖f y-f x‖≤L*‖y-x‖)
    (bounded : ∀x∈Icc 0 q,‖f x‖≤B) (x : ℝ) (nonzero : x≠0) :
    ‖countedRaw c h x‖≤(L*q+B)/|x| := by
  rw [counted_abs]
  have positive:0 < |x|:=abs_pos.mpr nonzero
  rw [counted_quadrature c zero h nonnegative f same _ positive,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_abs]
  have paid:=RegularQuadrature.quadrature_bound f regular L B lnonnegative bnonnegative lipschitz bounded
    |x|⁻¹ (inv_pos.mpr positive)
  rw [Complex.ofReal_inv,inv_inv] at paid
  exact (mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr positive.le)).trans_eq (by ring)

private theorem counted_measurable (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    Measurable (countedRaw c h) := by
  unfold countedRaw burnolInnerGapForward
  exact (Measurable.tsum (fun n=>measurable_const.mul
    ((actual_tate_measurable c h).comp (measurable_id.div_const _)))).sub_const _

private theorem counted_memLp (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (f : ℝ→ℂ)
    (same : ∀x:ℝ,x≠0→f x=differenceRaw c h x) (regular : ContinuousOn f (Icc 0 q))
    (L B : ℝ) (lnonnegative : 0≤L) (bnonnegative : 0≤B)
    (lipschitz : ∀x∈Icc 0 q,∀y∈Icc 0 q,‖f y-f x‖≤L*‖y-x‖)
    (bounded : ∀x∈Icc 0 q,‖f x‖≤B) : MemLp (countedRaw c h) 2 volume := by
  let bound:=L*q+B
  have boundNonnegative:0≤bound:=add_nonneg (mul_nonneg lnonnegative (by norm_num)) bnonnegative
  let dominant : ℝ→ℝ := fun x=>(symmetricInterval 4).indicator (fun _:ℝ=>‖reciprocalMean c h‖) x+
    bound*(if q < |x| then |x|⁻¹ else 0)
  have first:MemLp ((symmetricInterval (4:ℝ)).indicator (fun _:ℝ=>‖reciprocalMean c h‖)) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval 4) _ (Or.inr (by simp [symmetricInterval]))
  have tail:MemLp (fun x:ℝ=>if q < |x| then |x|⁻¹ else 0) 2 volume := by
    simpa only [pow_one] using innerGapWeight_memLp 1 (by decide)
  have source:MemLp dominant 2 volume:=first.add (tail.const_mul bound)
  apply source.mono (counted_measurable c h).aestronglyMeasurable
  filter_upwards with x
  by_cases inside:x∈symmetricInterval (4:ℝ)
  · rw [actual_counted_gap c zero h nonnegative x (abs_le.mpr inside),norm_neg]
    change ‖reciprocalMean c h‖≤‖(symmetricInterval 4).indicator (fun _:ℝ=>‖reciprocalMean c h‖) x+
      bound*(if q < |x| then |x|⁻¹ else 0)‖
    rw [indicator_of_mem inside,Real.norm_of_nonneg (by positivity)]
    exact le_add_of_nonneg_right (mul_nonneg boundNonnegative (by split_ifs <;> positivity))
  · have outside:4 < |x|:=lt_of_not_ge (fun small=>inside (abs_le.mp small))
    have nonzero:x≠0:=abs_pos.mp ((by norm_num : (0:ℝ)<4).trans outside)
    apply (counted_tail_bound c zero h nonnegative f same regular L B lnonnegative bnonnegative lipschitz bounded x nonzero).trans_eq
    change bound/|x|=‖(symmetricInterval 4).indicator (fun _:ℝ=>‖reciprocalMean c h‖) x+
      bound*(if q < |x| then |x|⁻¹ else 0)‖
    rw [indicator_of_notMem inside,if_pos (by linarith : q < |x|),zero_add,
      Real.norm_of_nonneg (mul_nonneg boundNonnegative (inv_nonneg.mpr (abs_nonneg x))),div_eq_mul_inv]

/-- The actual zero-generated quarter difference produces its complete L² co-sum. -/
theorem actual_counted_memLp (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) : MemLp (countedRaw c h) 2 volume := by
  let f : ℝ→ℂ := fun x=>if x=0 then OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source.positiveRaw c h 0 else differenceRaw c h x
  have same : ∀x:ℝ,x≠0→f x=differenceRaw c h x := by
    intro x nonzero
    exact if_neg nonzero
  have onQuarter : EqOn f (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source.positiveRaw c h) (Icc 0 q) := by
    intro x hx
    by_cases origin:x=0
    · subst x
      simp only [f,if_pos rfl]
    · rw [same x origin]
      exact (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source.actual_positive_raw c h nonnegative x
        (lt_of_le_of_ne hx.1 (Ne.symm origin)) hx.2).symm
  obtain ⟨L,lip⟩:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Source.actual_positive_lipschitz c zero h nonnegative
  have regular : ContinuousOn f (Icc 0 q):=lip.continuousOn.congr onQuarter
  obtain ⟨B,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn regular
  apply counted_memLp c zero h nonnegative f same regular L (max 0 B) L.coe_nonneg (le_max_left _ _)
  · intro x hx y hy
    rw [onQuarter hx,onQuarter hy]
    exact (lipschitzOnWith_iff_norm_sub_le.mp lip) hy hx
  · intro x hx
    exact (bounded x hx).trans (le_max_right _ _)

def countedValue (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) : BurnolL2 :=
  (actual_counted_memLp c zero h nonnegative).toLp (countedRaw c h)

theorem actual_counted_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) :
    (countedValue c zero h nonnegative : ℝ→ℂ)=ᵐ[volume] countedRaw c h :=
  (actual_counted_memLp c zero h nonnegative).coeFn_toLp

theorem actual_tate_realizes (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (tateSource c h) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (countedValue c zero h nonnegative)) test := by
  rw [actual_tate_copoisson_read c zero h nonnegative,
    Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [actual_counted_raw c zero h nonnegative] with x read
  rw [read]
  rfl

theorem actual_difference_realizes (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer.waveDifference c h) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 (countedValue c zero h nonnegative))) test := by
  have actual:=burnolRemainderRealization_fourier (tateSource c h) (countedValue c zero h nonnegative)
    (actual_tate_realizes c zero h nonnegative) test
  simpa only [tateSource,burnolTateReciprocalL2_involutive] using actual

theorem actual_counted_even (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) :
    reflectL2 (countedValue c zero h nonnegative)=countedValue c zero h nonnegative :=
  burnolReflectL2_eq_of_even_raw _ _ (actual_counted_raw c zero h nonnegative) (counted_even c h)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
