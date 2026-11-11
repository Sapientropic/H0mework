import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
open scoped Topology InnerProductSpace ContDiff ENNReal
open private pweight pweight_summable channel channel_summable forward_reindex from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open private local_growth from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "S"=>burnolMeanZeroTruncatedFourier
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem moment_integrable (state:Hq) (n:ℕ):
    Integrable (fun x:ℝ=>‖x‖^n*‖state x‖) μq:=by
  have source:=(Lp.memLp state).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  apply (source.norm.const_mul (q^n)).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) n) (norm_nonneg _))]
  have bounded:‖x‖≤q:=by simpa only [symmetricInterval,mem_Icc,Real.norm_eq_abs,abs_le] using inside
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) bounded n) (norm_nonneg _)

theorem actual_quarter_fourier_contDiff (state:Hq):
    ContDiff ℝ ∞ (burnolRadiusTruncatedFourierRaw q state):=by
  have source:=VectorFourier.contDiff_fourierIntegral (innerSL ℝ) (N:=⊤)
    (fun n _=>moment_integrable state n)
  unfold burnolRadiusTruncatedFourierRaw
  have bilinear:(innerₗ ℝ)=(innerSL ℝ).toLinearMap₁₂:=by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [innerₗ_apply_apply,ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,innerSL_apply_apply]
  rw [bilinear]
  exact source

theorem actual_return_contDiff (state:M):ContDiff ℝ ∞ (burnolMeanZeroFourierRaw state):=
  (actual_quarter_fourier_contDiff (state:Hq)).sub contDiff_const

private def slopeTerm (c:BurnolCompletedMellinCoordinate) (n:ℕ) (x:ℝ):ℂ:=
  (((n+1:ℕ):ℂ)⁻¹)^2*regularSlope c (x/(n+1:ℕ))

def bankSlope (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=∑'n:ℕ,slopeTerm c n x

private theorem scaled_inside (n:ℕ) (x:ℝ) (inside:x∈Icc (0:ℝ) q):
    x/(n+1:ℕ)∈Icc (0:ℝ) q:=by
  have one:(1:ℝ)≤(n+1:ℕ):=by exact_mod_cast (by omega : 1≤n+1)
  exact ⟨div_nonneg inside.1 (by positivity),(div_le_self inside.1 one).trans inside.2⟩

private theorem term_derivative (c:BurnolCompletedMellinCoordinate) (n:ℕ) (x:ℝ)
    (inside:x∈Ioo (0:ℝ) q):
    HasDerivAt (channel (regularLocal c) n) (slopeTerm c n x) x:=by
  have derivative:=((actual_regular_derivative c (x/(n+1:ℕ))
    (scaled_inside n x ⟨inside.1.le,inside.2.le⟩)).scomp x
      ((hasDerivAt_id x).div_const ((n+1:ℕ):ℝ))).const_mul (((n+1:ℕ):ℂ)⁻¹)
  have read:channel (regularLocal c) n=ᶠ[𝓝 x]
      fun y:ℝ=>(((n+1:ℕ):ℂ)⁻¹)*regularRaw c (y/(n+1:ℕ)):=by
    filter_upwards [Ioo_mem_nhds inside.1 inside.2] with y near
    have positive:0<y/(n+1:ℕ):=div_pos near.1 (by positivity)
    have below:y/(n+1:ℕ)<q:=
      (scaled_inside n y ⟨near.1.le,near.2.le⟩).2.lt_of_ne (by
        have smaller: y/(n+1:ℕ)≤y:=div_le_self near.1.le (by norm_cast;omega)
        linarith [near.2])
    simp only [channel,regularLocal,abs_of_pos positive,min_eq_right below.le]
  apply (derivative.congr_of_eventuallyEq read).congr_deriv
  dsimp only [slopeTerm]
  simp only [one_div,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
  ring

private theorem slope_envelope (c:BurnolCompletedMellinCoordinate):
    ∃B:ℝ,0≤B∧∀x∈Icc (0:ℝ) q,‖regularSlope c x‖≤B:=by
  obtain ⟨B,bound⟩:=isCompact_Icc.exists_bound_of_continuousOn (actual_regular_slope_continuous c)
  exact ⟨max 0 B,le_max_left _ _,fun x hx=>(bound x hx).trans (le_max_right _ _)⟩

private theorem slope_term_bound (c:BurnolCompletedMellinCoordinate) (B:ℝ)
    (bound:∀x∈Icc (0:ℝ) q,‖regularSlope c x‖≤B) (n:ℕ) (x:ℝ) (inside:x∈Icc (0:ℝ) q):
    ‖slopeTerm c n x‖≤B*pweight n:=by
  rw [slopeTerm,norm_mul,norm_pow,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (bound _ (scaled_inside n x inside)) (by positivity)).trans_eq
  unfold pweight
  ring

theorem actual_bank_slope_continuous (c:BurnolCompletedMellinCoordinate):
    ContinuousOn (bankSlope c) (Icc (0:ℝ) q):=by
  obtain ⟨B,_,bound⟩:=slope_envelope c
  apply continuousOn_tsum _ (pweight_summable.mul_left B) (slope_term_bound c B bound)
  intro n
  exact continuousOn_const.mul ((actual_regular_slope_continuous c).comp
    (continuous_id.div_const _).continuousOn (fun x hx=>scaled_inside n x hx))

theorem actual_bank_derivative (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (x:ℝ) (inside:x∈Ioo (0:ℝ) q):HasDerivAt (quarterBankRaw c) (bankSlope c x) x:=by
  obtain ⟨B,_,bound⟩:=slope_envelope c
  obtain ⟨L,_,lip⟩:=actual_regular_local_lipschitz c
  have generated:=hasDerivAt_tsum_of_isPreconnected (pweight_summable.mul_left B)
    isOpen_Ioo (convex_Ioo (0:ℝ) q).isPreconnected
    (term_derivative c) (fun n y hy=>slope_term_bound c B bound n y ⟨hy.1.le,hy.2.le⟩)
    (by norm_num : (q/2:ℝ)∈Ioo (0:ℝ) q)
    ((channel_summable (regularLocal c) L (local_growth c zero L lip) (q/2)).of_norm) inside
  have field:quarterBankRaw c=(fun y:ℝ=>∑'n:ℕ,channel (regularLocal c) n y):=by
    funext y
    exact forward_reindex (regularLocal c) y
  rw [field]
  exact generated

def inverseSlope (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (x:ℝ):ℂ:=
  bankSlope c x+deriv (burnolMeanZeroFourierRaw (S (sourceInverse c zero))) x

theorem actual_inverse_derivative (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (x:ℝ) (inside:x∈Ioo (0:ℝ) q):HasDerivAt (inverseRaw c zero) (inverseSlope c zero x) x:=by
  exact ((actual_bank_derivative c zero x inside).sub_const _).add
    ((actual_return_contDiff (S (sourceInverse c zero))).differentiable (by norm_num) x).hasDerivAt

theorem actual_inverse_slope_continuous (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    ContinuousOn (inverseSlope c zero) (Icc (0:ℝ) q):=
  (actual_bank_slope_continuous c).add
    ((actual_return_contDiff (S (sourceInverse c zero))).continuous_deriv (by norm_num)).continuousOn

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
