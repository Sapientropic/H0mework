import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Whole
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open scoped Topology InnerProductSpace
open private pweight pweight_summable channel channel_summable forward_reindex from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "P0"=>Constructor.zeroMean

theorem actual_regular_local_lipschitz (c:BurnolCompletedMellinCoordinate):
    ∃L:ℝ,0≤L∧∀x y:ℝ,‖regularLocal c y-regularLocal c x‖≤L*|y-x|:=by
  obtain ⟨L,B,nonnegative,_,bound,_⟩:=actual_regular_bounds c
  refine ⟨L,nonnegative,fun x y=>?_⟩
  have clamped:|min q (|y|)-min q (|x|)|≤|y-x|:=by
    apply (abs_min_sub_min_le_max q |y| q |x|).trans
    rw [sub_self,abs_zero,max_eq_right (abs_nonneg _)]
    exact abs_abs_sub_abs_le_abs_sub y x
  exact (bound _ ⟨le_min (by norm_num) (abs_nonneg x),min_le_left _ _⟩
    _ ⟨le_min (by norm_num) (abs_nonneg y),min_le_left _ _⟩).trans
      (by rw [Real.norm_eq_abs];exact mul_le_mul_of_nonneg_left clamped nonnegative)

def quarterBankRaw (c:BurnolCompletedMellinCoordinate):ℝ→ℂ:=burnolInnerGapForward (regularLocal c)

private theorem local_growth (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (L:ℝ) (bound:∀x y:ℝ,‖regularLocal c y-regularLocal c x‖≤L*|y-x|):
    ∀x:ℝ,‖regularLocal c x‖≤L*|x|:=by
  have origin:regularLocal c 0=0:=by
    rw [regularLocal,abs_zero,min_eq_right (by norm_num : (0:ℝ)≤q),
      OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail.actual_regular_origin c zero]
  intro x
  simpa only [origin,sub_zero] using bound 0 x

theorem actual_quarter_bank_lipschitz (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    ∃L:ℝ,0≤L∧∀x y:ℝ,‖quarterBankRaw c y-quarterBankRaw c x‖≤L*|y-x|:=by
  obtain ⟨L,nonnegative,bound⟩:=actual_regular_local_lipschitz c
  have growth:=local_growth c zero L bound
  refine ⟨L*(∑'n:ℕ,pweight n),mul_nonneg nonnegative
    (tsum_nonneg (fun n=>by unfold pweight;positivity)),fun x y=>?_⟩
  have sx:Summable (fun n:ℕ=>channel (regularLocal c) n x):=(channel_summable _ L growth x).of_norm
  have sy:Summable (fun n:ℕ=>channel (regularLocal c) n y):=(channel_summable _ L growth y).of_norm
  have one (n:ℕ):‖channel (regularLocal c) n y-channel (regularLocal c) n x‖≤
      (L*|y-x|)*pweight n:=by
    have positive:(0:ℝ)<(n+1:ℕ):=by positivity
    rw [channel,channel,←mul_sub,norm_mul,norm_inv,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left (bound (x/(n+1:ℕ)) (y/(n+1:ℕ)))
      (inv_nonneg.mpr positive.le)).trans_eq
    rw [←sub_div,abs_div,abs_of_pos positive,pweight]
    field_simp
  simp only [quarterBankRaw,forward_reindex]
  rw [←sy.tsum_sub sx]
  calc
    _≤∑'n:ℕ,‖channel (regularLocal c) n y-channel (regularLocal c) n x‖:=
      norm_tsum_le_tsum_norm (sy.sub sx).norm
    _≤∑'n:ℕ,(L*|y-x|)*pweight n:=
      Summable.tsum_le_tsum one (sy.sub sx).norm (pweight_summable.mul_left _)
    _=_:=by rw [tsum_mul_left];ring

theorem actual_quarter_bank_continuous (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Continuous (quarterBankRaw c):=by
  obtain ⟨L,nonnegative,bound⟩:=actual_quarter_bank_lipschitz c zero
  have lip:LipschitzWith ⟨L,nonnegative⟩ (quarterBankRaw c):=by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,Real.dist_eq]
    exact bound y x
  exact lip.continuous

theorem actual_quarter_bank_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (forwardQuarter c zero:ℝ→ℂ)=ᵐ[μq]quarterBankRaw c:=by
  filter_upwards [actual_forward_quarter_raw c zero,ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (volume.ae_ne q),ae_restrict_of_ae (volume.ae_ne (-q))]
    with x raw inside right left
  rw [raw]
  change burnolInnerGapForward (regularCompactRaw c) x=burnolInnerGapForward (regularLocal c) x
  apply tsum_congr
  intro n
  congr 1
  have positive:(0:ℝ)<(n:ℕ):=by exact_mod_cast n.pos
  have atLeast:(1:ℝ)≤(n:ℕ):=by exact_mod_cast n.property
  have small:|x|<q:=abs_lt.mpr ⟨lt_of_le_of_ne inside.1 (Ne.symm left),lt_of_le_of_ne inside.2 right⟩
  have moved:|x/(n:ℕ)|<q:=by
    rw [abs_div,abs_of_pos positive]
    exact (div_le_self (abs_nonneg x) atLeast).trans_lt small
  exact indicator_of_mem (show x/(n:ℕ)∈Ioo (-q) q from abs_lt.mp moved) _

def inverseRaw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (x:ℝ):ℂ:=
  quarterBankRaw c x-burnolQuarterMeanCoefficient (forwardQuarter c zero)+
    burnolMeanZeroFourierRaw (S (sourceInverse c zero)) x

/-- The original block inverse supplies the actual representative; no regularity is assumed of an arbitrary mean-zero input. -/
theorem actual_inverse_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (sourceInverse c zero:ℝ→ℂ)=ᵐ[μq]inverseRaw c zero:=by
  have equation:sourceInverse c zero-S (S (sourceInverse c zero))=P0 (forwardQuarter c zero):=by
    change (burnolMeanZeroOneMinusSquare*burnolMeanZeroBlockInverse) (P0 (forwardQuarter c zero))=_
    rw [burnolMeanZeroBlockInverse_right]
    rfl
  have split:sourceInverse c zero=P0 (forwardQuarter c zero)+S (S (sourceInverse c zero)):=by
    exact sub_eq_iff_eq_add.mp equation
  have cast:((sourceInverse c zero):Hq)=(P0 (forwardQuarter c zero):Hq)+(S (S (sourceInverse c zero)):Hq):=
    congrArg (fun v:M=>(v:Hq)) split
  have centered:(P0 (forwardQuarter c zero):Hq)=forwardQuarter c zero-
      burnolQuarterMeanCoefficient (forwardQuarter c zero) • intervalConstant q:=
    burnolMeanZeroProjection_eq_sub_constant _
  rw [cast,centered]
  filter_upwards [Lp.coeFn_add
    (forwardQuarter c zero-burnolQuarterMeanCoefficient (forwardQuarter c zero) • intervalConstant q)
    (S (S (sourceInverse c zero)):Hq),
    Lp.coeFn_sub (forwardQuarter c zero)
      (burnolQuarterMeanCoefficient (forwardQuarter c zero) • intervalConstant q),
    Lp.coeFn_smul (burnolQuarterMeanCoefficient (forwardQuarter c zero)) (intervalConstant q),
    intervalConstant_coeFn q,actual_quarter_bank_raw c zero,
    burnolMeanZeroFourier_ae_raw (S (sourceInverse c zero))]
    with x added subtracted scalar constant forward square
  rw [added,Pi.add_apply,subtracted,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,
    constant,mul_one,forward,square]
  rfl

theorem actual_inverse_continuous (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Continuous (inverseRaw c zero):=
  ((actual_quarter_bank_continuous c zero).sub continuous_const).add
    ((burnolRadiusTruncatedFourierRaw_continuous _).sub continuous_const)

theorem actual_inverse_bounded (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    ∃B:ℝ,0≤B∧∀x∈Icc (-q) q,‖inverseRaw c zero x‖≤B:=by
  obtain ⟨B,bound⟩:=isCompact_Icc.exists_bound_of_continuousOn (actual_inverse_continuous c zero).continuousOn
  exact ⟨max 0 B,le_max_left _ _,fun x hx=>(bound x hx).trans (le_max_right _ _)⟩

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
