import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.GlobalLipschitz
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Schwartz
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.GlobalLipschitz
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open scoped Topology InnerProductSpace Convolution ContDiff
local notation "q" => (1/4:ℝ)

def radius (N : ℕ) : ℝ := (16*((N:ℝ)+1))⁻¹

theorem radius_positive (N : ℕ) : 0<radius N := by unfold radius;positivity

theorem radius_bound (N : ℕ) : radius N≤1/16 := by
  rw [radius,one_div]
  exact (inv_le_inv₀ (by positivity : (0:ℝ)<16*((N:ℝ)+1)) (by norm_num : (0:ℝ)<16)).mpr
    (by nlinarith [Nat.cast_nonneg (α:=ℝ) N])

theorem radius_tendsto : Tendsto radius atTop (𝓝 0) := by
  have same : radius=(fun N:ℕ=>(1/16:ℝ)*((N:ℝ)+1)⁻¹) := by
    funext N
    unfold radius
    rw [mul_inv_rev]
    ring
  rw [same]
  simpa only [mul_zero,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (1/16:ℝ)

def ramp (N : ℕ) (x : ℝ) : ℝ := max 0 (min 1 ((|x|-2*radius N)/radius N))

private theorem ramp_bounds (N : ℕ) (x : ℝ) : 0≤ramp N x ∧ ramp N x≤1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

private theorem ramp_inner (N : ℕ) (x : ℝ) (inside : |x|≤2*radius N) : ramp N x=0 := by
  unfold ramp
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) (radius_positive N).le)

private theorem ramp_outer (N : ℕ) (x : ℝ) (outside : 3*radius N≤|x|) : ramp N x=1 := by
  unfold ramp
  rw [min_eq_left ((le_div_iff₀ (radius_positive N)).mpr (by linarith))]
  norm_num

private theorem ramp_even (N : ℕ) (x : ℝ) : ramp N (-x)=ramp N x := by simp only [ramp,abs_neg]

private theorem ramp_difference (N : ℕ) (x y : ℝ) :
    |ramp N x-ramp N y|≤|x-y|/radius N := by
  have clip:LipschitzWith 1 (fun t:ℝ=>max 0 (min 1 t)) := by
    simpa only [min_comm,id_eq] using (LipschitzWith.id.min_const 1).const_max 0
  have source:=clip.dist_le_mul ((|x|-2*radius N)/radius N) ((|y|-2*radius N)/radius N)
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at source
  change |ramp N x-ramp N y|≤_ at source
  apply source.trans
  rw [←sub_div,sub_sub_sub_cancel_right,abs_div,abs_of_pos (radius_positive N)]
  exact div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y) (radius_positive N).le

def rampSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  ramp N x • directRaw c h x

def sourceLipschitz (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) : NNReal :=
  (actual_direct_global_lipschitz c zero h nonnegative).choose

private theorem source_lipschitz (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) : LipschitzWith (sourceLipschitz c zero h nonnegative) (directRaw c h) :=
  (actual_direct_global_lipschitz c zero h nonnegative).choose_spec

private theorem source_growth (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (x : ℝ) :
    ‖directRaw c h x‖≤(sourceLipschitz c zero h nonnegative:ℝ)*|x| := by
  have paid:=(source_lipschitz c zero h nonnegative).norm_sub_le x 0
  simpa only [actual_direct_origin,sub_zero,Real.norm_eq_abs] using paid

private theorem ramp_source_inside (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ)
    (x : ℝ) (inside : |x|≤2*radius N) : rampSource c h N x=0 := by
  rw [rampSource,ramp_inner N x inside,zero_smul]

private theorem ramp_source_outside (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ) (outside : q≤|x|) : rampSource c h N x=0 := by
  rw [rampSource,actual_direct_outer_zero c zero h nonnegative x outside,smul_zero]

private theorem ramp_source_lipschitz (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) :
    LipschitzWith (4*sourceLipschitz c zero h nonnegative) (rampSource c h N) := by
  let L:=sourceLipschitz c zero h nonnegative
  have localBound (x y : ℝ) (inside : |x|≤3*radius N) :
      ‖rampSource c h N x-rampSource c h N y‖≤(4*(L:ℝ))*|x-y| := by
    have field:‖directRaw c h x‖≤(L:ℝ)*(3*radius N):=
      (source_growth c zero h nonnegative x).trans (mul_le_mul_of_nonneg_left inside L.coe_nonneg)
    have difference:= (source_lipschitz c zero h nonnegative).norm_sub_le x y
    rw [Real.norm_eq_abs] at difference
    have scalar:=ramp_difference N x y
    have rampNonnegative:0≤ramp N y:=(ramp_bounds N y).1
    have rampBound:ramp N y≤1:=(ramp_bounds N y).2
    have split:rampSource c h N x-rampSource c h N y=
        (ramp N x-ramp N y) • directRaw c h x+
          ramp N y • (directRaw c h x-directRaw c h y) := by
      unfold rampSource
      module
    rw [split]
    calc
      _≤|ramp N x-ramp N y| *‖directRaw c h x‖+
          ramp N y*‖directRaw c h x-directRaw c h y‖ := by
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg rampNonnegative] using norm_add_le
          ((ramp N x-ramp N y) • directRaw c h x)
          (ramp N y • (directRaw c h x-directRaw c h y))
      _≤(|x-y|/radius N)*((L:ℝ)*(3*radius N))+1*((L:ℝ)*|x-y|) :=
        add_le_add (mul_le_mul scalar field (norm_nonneg _)
          (div_nonneg (abs_nonneg _) (radius_positive N).le))
          (mul_le_mul rampBound difference (norm_nonneg _) (by norm_num))
      _=(4*(L:ℝ))*|x-y| := by field_simp [(radius_positive N).ne'];ring
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  change ‖rampSource c h N x-rampSource c h N y‖≤(4*(L:ℝ))*‖x-y‖
  rw [Real.norm_eq_abs]
  by_cases left:|x|≤3*radius N
  · exact localBound x y left
  by_cases right:|y|≤3*radius N
  · rw [norm_sub_rev]
    exact (localBound y x right).trans_eq (by rw [abs_sub_comm])
  · rw [rampSource,rampSource,ramp_outer N x (le_of_not_ge left),
      ramp_outer N y (le_of_not_ge right),one_smul,one_smul]
    have paid:=(source_lipschitz c zero h nonnegative).norm_sub_le x y
    rw [Real.norm_eq_abs] at paid
    exact paid.trans (by nlinarith [mul_nonneg L.coe_nonneg (abs_nonneg (x-y))])

private theorem ramp_approximation (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ) :
    ‖rampSource c h N x-directRaw c h x‖≤3*(sourceLipschitz c zero h nonnegative:ℝ)*radius N := by
  by_cases outside:3*radius N≤|x|
  · rw [rampSource,ramp_outer N x outside,one_smul,sub_self,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (sourceLipschitz c zero h nonnegative).coe_nonneg) (radius_positive N).le
  · have bound:|ramp N x-1|≤1 := by
      rw [abs_of_nonpos (by linarith [(ramp_bounds N x).2])]
      linarith [(ramp_bounds N x).1]
    rw [rampSource,show ramp N x • directRaw c h x-directRaw c h x=
      (ramp N x-1) • directRaw c h x by module,norm_smul,Real.norm_eq_abs]
    calc
      _≤1*((sourceLipschitz c zero h nonnegative:ℝ)*|x|):=
        mul_le_mul bound (source_growth c zero h nonnegative x) (norm_nonneg _) (by norm_num)
      _≤3*(sourceLipschitz c zero h nonnegative:ℝ)*radius N := by
        nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge outside)
          (sourceLipschitz c zero h nonnegative).coe_nonneg]

def bump (N : ℕ) : ContDiffBump (0:ℝ) :=
  ⟨radius N/2,radius N,half_pos (radius_positive N),half_lt_self (radius_positive N)⟩

def smoothRaw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) : ℝ→ℂ :=
  (bump N).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] rampSource c h N

private theorem smooth_contDiff (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) : ContDiff ℝ ∞ (smoothRaw c h N) :=
  (bump N).hasCompactSupport_normed.contDiff_convolution_left _ (bump N).contDiff_normed
    (ramp_source_lipschitz c zero h nonnegative N).continuous.locallyIntegrable

private theorem smooth_exists (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ) :
    Integrable (fun u:ℝ=>(bump N).normed volume u • rampSource c h N (x-u)) :=
  by
    have source:ConvolutionExistsAt ((bump N).normed volume) (rampSource c h N) x
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := (bump N).hasCompactSupport_normed.convolutionExists_left
      (μ:=volume) (ContinuousLinearMap.lsmul ℝ ℝ) (bump N).continuous_normed
      (ramp_source_lipschitz c zero h nonnegative N).continuous.locallyIntegrable x
    exact source

private theorem smooth_inner_zero (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ)
    (x : ℝ) (inside : |x|≤radius N) : smoothRaw c h N x=0 := by
  have original:rampSource c h N x=0:=ramp_source_inside c h N x (by linarith [radius_positive N])
  have same:= (bump N).normed_convolution_eq_right (μ:=volume) (g:=rampSource c h N) (x₀:=x) (by
    intro y hy
    rw [original]
    apply ramp_source_inside
    have close:|y-x|<radius N:=hy
    have triangle:|y|≤|y-x|+|x|:=by
      simpa only [Real.norm_eq_abs,sub_add_cancel] using norm_add_le (y-x) x
    linarith)
  exact same.trans original

private theorem smooth_outer_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ)
    (outside : q+radius N≤|x|) : smoothRaw c h N x=0 := by
  have original:rampSource c h N x=0:=ramp_source_outside c zero h nonnegative N x (by linarith [radius_positive N])
  have same:= (bump N).normed_convolution_eq_right (μ:=volume) (g:=rampSource c h N) (x₀:=x) (by
    intro y hy
    rw [original]
    apply ramp_source_outside c zero h nonnegative N
    have close:|y-x|<radius N:=hy
    have triangle:|x|≤|y-x|+|y|:=by
      simpa only [Real.norm_eq_abs,sub_add_cancel,abs_sub_comm] using norm_add_le (x-y) y
    linarith)
  exact same.trans original

private theorem smooth_compact (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) : HasCompactSupport (smoothRaw c h N) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(-1:ℝ)) (b:=1))
  intro x nonzero
  apply abs_le.mp
  by_contra outside
  exact nonzero (smooth_outer_zero c zero h nonnegative N x (by linarith [radius_bound N]))

/-- The source is an actual normalized bump convolution, with its vanishing inner interval retained. -/
def schwartzApprox (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) : SchwartzMap ℝ ℂ :=
  (smooth_compact c zero h nonnegative N).toSchwartzMap (smooth_contDiff c zero h nonnegative N)

private theorem smooth_lipschitz (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) :
    LipschitzWith (4*sourceLipschitz c zero h nonnegative) (smoothRaw c h N) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  let C:ℝ:=4*(sourceLipschitz c zero h nonnegative:ℝ)
  have source:∀u:ℝ,‖rampSource c h N (x-u)-rampSource c h N (y-u)‖≤C*‖x-y‖ := by
    intro u
    have actual:=(ramp_source_lipschitz c zero h nonnegative N).norm_sub_le (x-u) (y-u)
    simpa only [sub_sub_sub_cancel_right,NNReal.coe_mul,NNReal.coe_ofNat] using actual
  change ‖(∫u:ℝ,(bump N).normed volume u • rampSource c h N (x-u))-
    (∫u:ℝ,(bump N).normed volume u • rampSource c h N (y-u))‖≤C*‖x-y‖
  rw [←integral_sub (smooth_exists c zero h nonnegative N x) (smooth_exists c zero h nonnegative N y)]
  have integrable:=((smooth_exists c zero h nonnegative N x).sub (smooth_exists c zero h nonnegative N y)).norm
  calc
    _≤∫u:ℝ,‖(bump N).normed volume u • rampSource c h N (x-u)-
        (bump N).normed volume u • rampSource c h N (y-u)‖ := norm_integral_le_integral_norm _
    _≤∫u:ℝ,(bump N).normed volume u*(C*‖x-y‖) := by
      apply integral_mono_ae integrable ((bump N).integrable_normed.mul_const _)
      filter_upwards with u
      rw [Pi.sub_apply,←smul_sub,norm_smul,Real.norm_of_nonneg ((bump N).nonneg_normed u)]
      exact mul_le_mul_of_nonneg_left (source u) ((bump N).nonneg_normed u)
    _=C*‖x-y‖ := by rw [integral_mul_const,(bump N).integral_normed,one_mul]

theorem actual_schwartz_global_lipschitz (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) :
    LipschitzWith (4*sourceLipschitz c zero h nonnegative) (schwartzApprox c zero h nonnegative N) :=
  smooth_lipschitz c zero h nonnegative N

theorem actual_schwartz_inner_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ) (inside : |x|≤radius N) :
    schwartzApprox c zero h nonnegative N x=0 := smooth_inner_zero c h N x inside

theorem actual_schwartz_outer_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ) (outside : q+radius N≤|x|) :
    schwartzApprox c zero h nonnegative N x=0 := smooth_outer_zero c zero h nonnegative N x outside

theorem actual_schwartz_linear_bound (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ) :
    ‖schwartzApprox c zero h nonnegative N x‖≤(4*(sourceLipschitz c zero h nonnegative:ℝ))*|x| := by
  have paid:=(actual_schwartz_global_lipschitz c zero h nonnegative N).norm_sub_le x 0
  rw [actual_schwartz_inner_zero c zero h nonnegative N 0 (by simpa using (radius_positive N).le),
    sub_zero,sub_zero,Real.norm_eq_abs] at paid
  exact paid

theorem actual_schwartz_even (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ) :
    schwartzApprox c zero h nonnegative N (-x)=schwartzApprox c zero h nonnegative N x := by
  change (∫u:ℝ,(bump N).normed volume u • rampSource c h N (-x-u))=
    ∫u:ℝ,(bump N).normed volume u • rampSource c h N (x-u)
  rw [←integral_neg_eq_self (fun u:ℝ=>(bump N).normed volume u • rampSource c h N (-x-u))]
  apply integral_congr_ae
  filter_upwards with u
  rw [(bump N).normed_neg,show -x-(-u)= -(x-u) by ring,rampSource,rampSource,ramp_even,actual_direct_even]

theorem actual_schwartz_approximation (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) (x : ℝ) :
    ‖schwartzApprox c zero h nonnegative N x-directRaw c h x‖≤
      (7*(sourceLipschitz c zero h nonnegative:ℝ))*radius N := by
  let L:=sourceLipschitz c zero h nonnegative
  have close:= (bump N).dist_normed_convolution_le
    (μ:=volume) (g:=rampSource c h N) (x₀:=x)
    (ramp_source_lipschitz c zero h nonnegative N).continuous.aestronglyMeasurable (ε:=(4*(L:ℝ))*radius N) (by
      intro y hy
      have source:=(ramp_source_lipschitz c zero h nonnegative N).dist_le_mul y x
      have bound:dist y x≤radius N:=hy.le
      exact source.trans (mul_le_mul_of_nonneg_left bound (by positivity)))
  rw [dist_eq_norm] at close
  have source:=ramp_approximation c zero h nonnegative N x
  change ‖smoothRaw c h N x-directRaw c h x‖≤_
  calc
    _=‖(smoothRaw c h N x-rampSource c h N x)+(rampSource c h N x-directRaw c h x)‖ := by
      congr 1
      abel
    _≤‖smoothRaw c h N x-rampSource c h N x‖+‖rampSource c h N x-directRaw c h x‖ := norm_add_le _ _
    _≤_ := (add_le_add close source).trans_eq (by dsimp only [L];ring)

theorem actual_schwartz_tendsto (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (x : ℝ) :
    Tendsto (fun N:ℕ=>schwartzApprox c zero h nonnegative N x) atTop (𝓝 (directRaw c h x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _=>norm_nonneg _) (fun N=>actual_schwartz_approximation c zero h nonnegative N x)
    (by simpa only [mul_zero] using radius_tendsto.const_mul (7*(sourceLipschitz c zero h nonnegative:ℝ)))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Schwartz
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
