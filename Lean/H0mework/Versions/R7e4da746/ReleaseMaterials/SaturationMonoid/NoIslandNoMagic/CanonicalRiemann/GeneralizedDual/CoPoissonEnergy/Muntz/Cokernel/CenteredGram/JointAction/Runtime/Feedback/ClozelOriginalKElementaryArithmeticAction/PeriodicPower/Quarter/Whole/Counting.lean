import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open scoped Topology InnerProductSpace
open private half_mass tate_reciprocal_integral from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
local notation "q" => (1/4:ℝ)

def wholeTateRaw (c : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  burnolTateReciprocalRaw (quarterRaw c)

def wholeCountedRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolInnerGapForward (wholeTateRaw c) x-quarterMean c/4

theorem actual_tate_raw (c : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (quarterWave c):ℝ→ℂ)=ᵐ[volume]wholeTateRaw c := by
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (quarterWave c))
    ((Lp.memLp (quarterWave c)).ae_eq (actual_quarter_raw c)) (actual_quarter_raw c)
  exact (burnolTateReciprocalL2_coeFn (quarterWave c)).trans pulled

theorem actual_tate_measurable (c : BurnolCompletedMellinCoordinate) : Measurable (wholeTateRaw c) :=
  (Complex.measurable_ofReal.comp continuous_abs.measurable).inv.mul
    ((actual_quarter_measurable c).comp measurable_inv)

theorem actual_tate_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    wholeTateRaw c (-x)=wholeTateRaw c x := by
  unfold wholeTateRaw burnolTateReciprocalRaw
  rw [abs_neg,inv_neg,actual_quarter_even]

theorem actual_tate_gap (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    {x : ℝ} (inside : |x|≤4) : wholeTateRaw c x=0 := by
  by_cases atZero:x=0
  · subst x;simp [wholeTateRaw,burnolTateReciprocalRaw]
  · have positive:0 < |x|:=abs_pos.mpr atZero
    have outside:q≤|x⁻¹| := by
      rw [abs_inv]
      exact (le_inv_comm₀ (by norm_num : (0:ℝ)<q) positive).mpr (by simpa using inside)
    rw [wholeTateRaw,burnolTateReciprocalRaw,actual_quarter_outer_zero c zero _ outside,mul_zero]

theorem actual_reciprocal_mean (c : BurnolCompletedMellinCoordinate) :
    (∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*wholeTateRaw c u)=quarterMean c/4 := by
  rw [wholeTateRaw,tate_reciprocal_integral,half_mass]

/-- The original inner-gap producer acts on T H itself, retaining its complete Unit. -/
theorem actual_whole_copoisson_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolTateReciprocalL2 (quarterWave c)) test=
      ∫x:ℝ,test x*wholeCountedRaw c x := by
  have actual:=burnolRemainderSourceRead_innerGap_forward _ _ (actual_tate_measurable c)
    (actual_tate_raw c) (fun {_} small=>actual_tate_gap c zero (small.trans (by norm_num)))
    (actual_tate_even c) test
  simpa only [actual_reciprocal_mean,wholeCountedRaw] using actual

/-- This co-sum is the Fourier representative of the already generated whole source. -/
theorem actual_whole_fourier_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) :
    (fourierL2 (wholeValue c zero h positive):ℝ→ℂ)=ᵐ[volume]wholeCountedRaw c := by
  have sourceEven:=burnolReflectL2_eq_of_even_raw _ _ (actual_tate_raw c) (actual_tate_even c)
  have sourceGap:(burnolTateReciprocalL2 (quarterWave c):ℝ→ℂ)=ᵐ[
      volume.restrict (symmetricInterval q)]fun _=>0 := by
    filter_upwards [ae_restrict_of_ae (actual_tate_raw c),ae_restrict_mem (measurableSet_symmetricInterval q)]
      with x raw member
    exact raw.trans (actual_tate_gap c zero ((abs_le.mpr member).trans (by norm_num)))
  have realizes:∀test:SchwartzMap ℝ ℂ,
      burnolRemainderSourceRead (burnolTateReciprocalL2 (quarterWave c)) test=
        ∫x:ℝ,test x*(fourierL2 (wholeValue c zero h positive)) x := by
    intro test
    simpa only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply,smul_eq_mul]
      using actual_whole_tate_realizes c zero h positive test
  obtain ⟨raw,represents,_,target⟩:=burnolRemainderSourceRead_realization_ae _ _ sourceEven sourceGap realizes
  have same:raw=ᵐ[volume]wholeTateRaw c:=represents.symm.trans (actual_tate_raw c)
  have mean:(∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u)=quarterMean c/4 := by
    rw [←actual_reciprocal_mean c]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae same] with u actual
    rw [actual]
  filter_upwards [target,burnolInnerGapForward_ae_congr _ _ same] with x represented forward
  rw [represented,forward,mean]
  rfl

private theorem tate_channel (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (nonzero : x≠0) (n : ℕ) (positive : 0<n) :
    (n:ℂ)⁻¹*wholeTateRaw c (x/n)=((|x|:ℝ):ℂ)⁻¹*quarterRaw c (n/x) := by
  have realPositive:(0:ℝ)<n:=by exact_mod_cast positive
  have natNe:(n:ℂ)≠0:=by exact_mod_cast positive.ne'
  have absNe:((|x|:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)
  rw [wholeTateRaw,burnolTateReciprocalRaw,abs_div,abs_of_pos realPositive,inv_div,
    Complex.ofReal_div]
  push_cast
  field_simp

theorem actual_finite_lattice (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (x : ℝ) (nonzero : x≠0) (N : ℕ) (covered : |x|≤4*(N+1)) :
    wholeCountedRaw c x=((|x|:ℝ):ℂ)⁻¹*(∑n∈Finset.range N,quarterRaw c ((n+1)/x))-
      quarterMean c/4 := by
  unfold wholeCountedRaw burnolInnerGapForward
  congr 1
  rw [←Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
    (fun n:ℕ+=>((n:ℕ):ℂ)⁻¹*wholeTateRaw c (x/(n:ℕ)))]
  change (∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*wholeTateRaw c (x/(n+1:ℕ)))=_
  rw [tsum_eq_sum (s:=Finset.range N) (fun n outside=>by
    have bound:N≤n:=le_of_not_gt (fun member=>outside (Finset.mem_range.mpr member))
    have moved:|x/(n+1:ℕ)|≤4 := by
      have positive:(0:ℝ)<(n+1:ℕ):=by positivity
      rw [abs_div,abs_of_pos positive]
      apply (div_le_iff₀ positive).mpr
      have realBound:(N:ℝ)≤n:=by exact_mod_cast bound
      push_cast
      nlinarith
    rw [actual_tate_gap c zero moved,mul_zero])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [Nat.cast_add,Nat.cast_one] using tate_channel c x nonzero (n+1) (by omega)

theorem actual_positive_floor (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (x : ℝ) (positive : 0<x) :
    wholeCountedRaw c x=(x:ℂ)⁻¹*
      (∑n∈Finset.range ⌊q*x⌋₊,periodicRaw c ((n+1)/x))-quarterMean c/4 := by
  have covered:x≤4*((⌊q*x⌋₊:ℝ)+1) := by
    have bound:=Nat.lt_floor_add_one (q*x)
    nlinarith
  rw [actual_finite_lattice c zero x positive.ne' ⌊q*x⌋₊ (by simpa [abs_of_pos positive] using covered),
    abs_of_pos positive]
  congr 2
  apply Finset.sum_congr rfl
  intro n member
  have bound:(n:ℝ)+1≤(⌊q*x⌋₊:ℝ):=by exact_mod_cast (Finset.mem_range.mp member)
  have floor:((⌊q*x⌋₊:ℕ):ℝ)≤q*x:=Nat.floor_le (by positivity)
  have located:(n+1)/x∈symmetricInterval q := by
    constructor
    · have : (0:ℝ)≤(n+1)/x:=by positivity
      linarith
    · apply (div_le_iff₀ positive).mpr
      linarith
  exact indicator_of_mem located _

theorem actual_counted_gap (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (x : ℝ) (inside : |x|≤4) : wholeCountedRaw c x= -quarterMean c/4 := by
  by_cases nonzero:x=0
  · subst x
    simp [wholeCountedRaw,burnolInnerGapForward,wholeTateRaw,burnolTateReciprocalRaw,neg_div]
  · rw [actual_finite_lattice c zero x nonzero 0 (by simpa using inside)]
    simp [neg_div]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
