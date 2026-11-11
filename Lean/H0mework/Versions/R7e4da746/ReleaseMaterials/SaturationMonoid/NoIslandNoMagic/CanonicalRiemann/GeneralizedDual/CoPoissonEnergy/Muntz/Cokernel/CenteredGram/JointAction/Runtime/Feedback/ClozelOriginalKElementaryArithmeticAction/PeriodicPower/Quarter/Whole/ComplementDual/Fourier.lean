import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Fourier
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.WeightedCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Counting
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open scoped Topology InnerProductSpace FourierTransform
open private term_raw from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Counting
open private weightedRawTerm from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem phase_continuous (y:ℝ):Continuous (Constructor.phase y):=
  continuous_iff_continuousAt.mpr (fun x=>(Constructor.phase_derivative y x).continuousAt)

private theorem phase_bound (y x:ℝ):
    ‖Constructor.phase y x-1‖≤((2+2*Real.pi)*|y|)*|x|:=by
  simpa only [Constructor.phase,Real.rpow_one,abs_neg,abs_mul,mul_assoc] using
    phase_holder 1 (by norm_num) (by norm_num) (-(y*x))

private def differenceTestRaw (y x:ℝ):ℂ:=star (Constructor.phase y x-1)/((|x|:ℝ):ℂ)

private theorem difference_test_bound (y x:ℝ):
    ‖differenceTestRaw y x‖≤(2+2*Real.pi)*|y|:=by
  by_cases atZero:x=0
  · subst x
    simp only [differenceTestRaw,abs_zero,ofReal_zero,div_zero,norm_zero]
    positivity
  have positive:0 < |x|:=abs_pos.mpr atZero
  rw [differenceTestRaw,norm_div,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_abs]
  exact (div_le_iff₀ positive).mpr (phase_bound y x)

private theorem difference_test_memLp (y:ℝ):MemLp (differenceTestRaw y) 2 μq:=by
  have measurable:Measurable (differenceTestRaw y):=
    (((phase_continuous y).sub continuous_const).star).measurable.div
      (Complex.continuous_ofReal.comp continuous_abs).measurable
  exact MemLp.of_bound measurable.aestronglyMeasurable ((2+2*Real.pi)*|y|)
    (Eventually.of_forall (difference_test_bound y))

private def differenceTest (y:ℝ):Hq:=(difference_test_memLp y).toLp (differenceTestRaw y)

private theorem difference_test_raw (y:ℝ):
    (E (differenceTest y):ℝ→ℂ)=ᵐ[volume](symmetricInterval q).indicator (differenceTestRaw y):=by
  have localRead:∀ᵐx:ℝ∂volume,x∈symmetricInterval q→differenceTest y x=differenceTestRaw y x:=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (difference_test_memLp y).coeFn_toLp
  filter_upwards [burnolQuarterZeroExtension_coe (differenceTest y),localRead] with x extended read
  rw [extended]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,read inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

private theorem fourier_integral (raw:ℝ→ℂ) (y:ℝ):
    Constructor.fourierRaw raw y=∫x:ℝ,Constructor.phase y x*raw x ∂μq:=by
  rw [Constructor.fourierRaw_integral,intervalIntegral.integral_of_le (by norm_num : (-q:ℝ)≤q),
    ←integral_Icc_eq_integral_Ioc]
  rfl

private theorem phase_integrable (raw:ℝ→ℂ) (domain:Integrable raw μq) (y:ℝ):
    Integrable (fun x:ℝ=>Constructor.phase y x*raw x) μq:=by
  apply domain.bdd_mul (c:=1) (phase_continuous y).aestronglyMeasurable
  filter_upwards with x
  simp only [Constructor.phase,Circle.norm_coe,le_refl]

private theorem centered_fourier_read (raw:ℝ→ℂ) (domain:Integrable raw μq) (y:ℝ):
    (∫x:ℝ,(Constructor.phase y x-1)*raw x ∂μq)=
      Constructor.fourierRaw raw y-∫x:ℝ,raw x ∂μq:=by
  simp only [sub_mul,one_mul]
  rw [integral_sub (phase_integrable raw domain y) domain,fourier_integral]

private theorem counted_read (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (y:ℝ):
    inner ℂ (E (differenceTest y)) (dualCounting c.value c.belowOne)=
      Constructor.fourierRaw (fullFloorRaw c) y-∫x:ℝ,fullFloorRaw c x ∂μq:=by
  have integrand:(fun x:ℝ=>star (E (differenceTest y) x)*(dualCounting c.value c.belowOne) x)=ᵐ[volume]
      (symmetricInterval q).indicator (fun x:ℝ=>(Constructor.phase y x-1)*fullFloorRaw c x):=by
    filter_upwards [difference_test_raw y,actual_dual_counting_raw c.value c.belowOne,
      volume.ae_ne (0:ℝ)] with x test count nonzero
    rw [test,count,arithmeticRaw]
    by_cases inside:x∈symmetricInterval q
    · rw [indicator_of_mem inside,indicator_of_mem inside,differenceTestRaw,star_div₀,star_star,
        Complex.star_def,Complex.conj_ofReal]
      change (Constructor.phase y x-1)/((|x|:ℝ):ℂ)*(((|x|:ℝ):ℂ)*fullFloorRaw c x)=_
      field_simp [Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)]
    · rw [indicator_of_notMem inside,indicator_of_notMem inside,star_zero,zero_mul]
  rw [L2.inner_def]
  simp only [RCLike.inner_apply',←Complex.star_def]
  change (∫x:ℝ,star (E (differenceTest y) x)*(dualCounting c.value c.belowOne) x)=_
  rw [integral_congr_ae integrand,integral_indicator (measurableSet_symmetricInterval q)]
  exact centered_fourier_read (fullFloorRaw c)
    (((actual_full_floor_memLp c zero).restrict (symmetricInterval q)).integrable (by norm_num)) y

private theorem term_read (w:ℂ) (below:w.re<1) (y:ℝ) (n:ℕ):
    inner ℂ (E (differenceTest y)) (reverseTerm (dualWeighted w below) n)=
      (((n+1:ℕ):ℂ)⁻¹)*Constructor.fourierRaw (dualRaw w below) (y/(n+1:ℕ)):=by
  let N:ℝ:=(n+1:ℕ)
  have positive:0<N:=by dsimp only [N];positivity
  have large:1≤N:=by dsimp only [N];exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have localInside (x:ℝ) (inside:N*x∈symmetricInterval q):x∈symmetricInterval q:=by
    apply abs_le.mp
    have bound:|N*x|≤q:=abs_le.mpr inside
    rw [abs_mul,abs_of_pos positive] at bound
    exact (le_mul_of_one_le_left (abs_nonneg x) large).trans bound
  have integrand:(fun x:ℝ=>star (E (differenceTest y) x)*(reverseTerm (dualWeighted w below) n) x)=ᵐ[volume]
      fun x:ℝ=>(Constructor.phase y x-1)*(symmetricInterval q).indicator (dualRaw w below) (N*x):=by
    filter_upwards [difference_test_raw y,term_raw w below n,volume.ae_ne (0:ℝ)] with x test counted nonzero
    rw [test,counted,weightedRawTerm]
    change star ((symmetricInterval q).indicator (differenceTestRaw y) x)*
      (((|x|:ℝ):ℂ)*(symmetricInterval q).indicator (dualRaw w below) (N*x))=_
    by_cases inside:N*x∈symmetricInterval q
    · rw [indicator_of_mem (localInside x inside),indicator_of_mem inside,differenceTestRaw,
        star_div₀,star_star,Complex.star_def,Complex.conj_ofReal]
      field_simp [Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)]
    · rw [indicator_of_notMem inside,mul_zero,mul_zero,mul_zero]
  let f:ℝ→ℂ:=fun u=>(Constructor.phase (y/N) u-1)*(symmetricInterval q).indicator (dualRaw w below) u
  have changed:(fun x:ℝ=>(Constructor.phase y x-1)*(symmetricInterval q).indicator (dualRaw w below) (N*x))=
      fun x:ℝ=>f (N*x):=by
    funext x
    dsimp only [f,Constructor.phase]
    congr 3
    field_simp
  have integralF:(∫u:ℝ,f u)=Constructor.fourierRaw (dualRaw w below) (y/N):=by
    have point:f=(symmetricInterval q).indicator (fun u=>(Constructor.phase (y/N) u-1)*dualRaw w below u):=by
      funext u
      by_cases inside:u∈symmetricInterval q
      · dsimp only [f]
        rw [indicator_of_mem inside,indicator_of_mem inside]
      · simp only [f,indicator_of_notMem inside,mul_zero]
    rw [point,integral_indicator (measurableSet_symmetricInterval q),
      centered_fourier_read (dualRaw w below) (actual_dual_integrable w below),actual_dual_mean,sub_zero]
  rw [L2.inner_def]
  simp only [RCLike.inner_apply',←Complex.star_def]
  change (∫x:ℝ,star (E (differenceTest y) x)*(reverseTerm (dualWeighted w below) n) x)=_
  rw [integral_congr_ae integrand,changed,MeasureTheory.Measure.integral_comp_mul_left,integralF,
    abs_of_pos (inv_pos.mpr positive),Complex.real_smul,Complex.ofReal_inv]
  simp only [N,Complex.ofReal_natCast]

/-- The whole Fourier contact includes the real origin mass discarded by the finite programmes. -/
theorem actual_count_fourier_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (y:ℝ):
    HasSum (fun n:ℕ=>(((n+1:ℕ):ℂ)⁻¹)*
      Constructor.fourierRaw (dualRaw c.value c.belowOne) (y/(n+1:ℕ)))
      (Constructor.fourierRaw (fullFloorRaw c) y-∫x:ℝ,fullFloorRaw c x ∂μq):=by
  have sum:HasSum (reverseTerm (dualWeighted c.value c.belowOne)) (dualCounting c.value c.belowOne):=
    (actual_reverse_summable (dualWeighted c.value c.belowOne)).of_norm.hasSum
  have read:=sum.mapL (innerSL ℂ (E (differenceTest y)))
  simp only [innerSL_apply_apply] at read
  rw [counted_read c zero y] at read
  exact read.congr_fun (fun n=>(term_read c.value c.belowOne y n).symm)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Fourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
