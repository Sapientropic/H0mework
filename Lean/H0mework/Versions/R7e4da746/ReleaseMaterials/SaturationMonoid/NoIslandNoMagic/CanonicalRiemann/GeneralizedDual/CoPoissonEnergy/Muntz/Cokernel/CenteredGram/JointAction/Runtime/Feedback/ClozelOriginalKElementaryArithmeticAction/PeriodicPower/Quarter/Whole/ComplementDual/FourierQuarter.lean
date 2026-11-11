import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Fourier OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice
open scoped Topology InnerProductSpace ENNReal
open private phase_bound phase_integrable centered_fourier_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Fourier
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Rq" => burnolQuarterRestriction
local notation "Cq" => intervalConstant q
local notation "BI" => burnolMeanZeroBlockInverse
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def sourceL1Norm (c:BurnolCompletedMellinCoordinate):ℝ:=
  ∫x:ℝ,‖dualRaw c.value c.belowOne x‖ ∂μq

def frequencyBound (c:BurnolCompletedMellinCoordinate):ℝ:=
  (2+2*Real.pi)*q*sourceL1Norm c

private theorem frequency_nonnegative (c:BurnolCompletedMellinCoordinate):0≤frequencyBound c:=by
  dsimp only [frequencyBound,sourceL1Norm]
  positivity

private theorem actual_fourier_linear_bound (c:BurnolCompletedMellinCoordinate) (y:ℝ):
    ‖Constructor.fourierRaw (dualRaw c.value c.belowOne) y‖≤frequencyBound c*|y|:=by
  have domain:=actual_dual_integrable c.value c.belowOne
  have normDomain:=((phase_integrable _ domain y).sub domain).norm
  have read:=centered_fourier_read _ domain y
  rw [actual_dual_mean,sub_zero] at read
  rw [←read]
  calc
    _≤∫x:ℝ,‖(Constructor.phase y x-1)*dualRaw c.value c.belowOne x‖ ∂μq:=norm_integral_le_integral_norm _
    _≤∫x:ℝ,((2+2*Real.pi)*|y| *q)*‖dualRaw c.value c.belowOne x‖ ∂μq:=by
      apply integral_mono_ae (normDomain.congr (Eventually.of_forall (fun x=>by
        simp only [Pi.sub_apply];congr 1;ring))) (domain.norm.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((phase_bound y x).trans
        (mul_le_mul_of_nonneg_left (abs_le.mpr inside) (by positivity))) (norm_nonneg _)
    _=frequencyBound c*|y|:=by rw [integral_const_mul];dsimp only [frequencyBound,sourceL1Norm];ring

def quarterTerm (c:BurnolCompletedMellinCoordinate) (n:ℕ):Hq:=
  Constructor.compact (fun y:ℝ=>(((n+1:ℕ):ℂ)⁻¹)*
    Constructor.fourierRaw (dualRaw c.value c.belowOne) (y/(n+1:ℕ)))
    (continuous_const.mul ((actual_fourier_continuous _ (actual_dual_integrable c.value c.belowOne)).comp
      (continuous_id.div_const _)))

theorem actual_quarter_term_raw (c:BurnolCompletedMellinCoordinate) (n:ℕ):
    (quarterTerm c n:ℝ→ℂ)=ᵐ[μq]fun y:ℝ=>(((n+1:ℕ):ℂ)⁻¹)*
      Constructor.fourierRaw (dualRaw c.value c.belowOne) (y/(n+1:ℕ)):=Constructor.compact_read _ _

private theorem quarter_term_bound (c:BurnolCompletedMellinCoordinate) (n:ℕ):
    ∀ᵐy:ℝ∂μq,‖quarterTerm c n y‖≤(frequencyBound c*q)*((n+1:ℕ):ℝ)^(-(2:ℝ)):=by
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  filter_upwards [actual_quarter_term_raw c n,ae_restrict_mem (measurableSet_symmetricInterval q)] with y raw inside
  rw [raw,norm_mul,norm_inv,Complex.norm_natCast]
  have bound:=actual_fourier_linear_bound c (y/(n+1:ℕ))
  rw [abs_div,abs_of_pos positive] at bound
  calc
    _≤(((n+1:ℕ):ℝ)⁻¹)*(frequencyBound c*(|y|/(n+1:ℕ))):=
      mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr positive.le)
    _≤(((n+1:ℕ):ℝ)⁻¹)*(frequencyBound c*(q/(n+1:ℕ))):=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (abs_le.mpr inside) positive.le)
          (frequency_nonnegative c)) (inv_nonneg.mpr positive.le)
    _=_:=by rw [Real.rpow_neg positive.le,Real.rpow_two,←inv_pow];ring

theorem actual_quarter_summable (c:BurnolCompletedMellinCoordinate):
    Summable (fun n:ℕ=>‖quarterTerm c n‖):=by
  have power:Summable (fun n:ℕ=>(n:ℝ)^(-(2:ℝ))):=
    Real.summable_nat_rpow.mpr (by norm_num)
  have shifted:Summable (fun n:ℕ=>((n+1:ℕ):ℝ)^(-(2:ℝ))):=(summable_nat_add_iff 1).mpr power
  let A:ℝ:=(measureUnivNNReal μq:ℝ)^((2:ℝ≥0∞).toReal⁻¹)*(frequencyBound c*q)
  apply (shifted.mul_left A).of_nonneg_of_le (fun n=>norm_nonneg _)
  intro n
  have nonnegative:0≤frequencyBound c*q*((n+1:ℕ):ℝ)^(-(2:ℝ)):=by
    have source:=frequency_nonnegative c
    positivity
  have actual:=Lp.norm_le_of_ae_bound nonnegative (quarter_term_bound c n)
  exact actual.trans_eq (by dsimp only [A];ring)

/-- The actual Fourier quarter, with its origin Unit retained, is a strongly summed Hq source. -/
theorem actual_quarter_hasSum (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    HasSum (quarterTerm c)
      (Rq (fourierL2 (fullFloorValue c zero))-
        (2*deriv (poleFreeSource c) 1/(1-star c.value)) • Cq):=by
  have summable:Summable (quarterTerm c):=(actual_quarter_summable c).of_norm
  have sumRaw:=Lp.hasSum_coeFn_tsum
    (tsum_enorm_ne_top_iff_summable_norm.mpr (actual_quarter_summable c))
  have terms:∀ᵐx:ℝ∂μq,∀n:ℕ,quarterTerm c n x=
      (((n+1:ℕ):ℂ)⁻¹)*Constructor.fourierRaw (dualRaw c.value c.belowOne) (x/(n+1:ℕ)):=
    ae_all_iff.mpr (actual_quarter_term_raw c)
  have restricted:(Rq (fourierL2 (fullFloorValue c zero)):ℝ→ℂ)=ᵐ[μq]countFourierRaw c zero:=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (fourierL2 (fullFloorValue c zero))).trans
      (ae_restrict_of_ae (actual_L2_fourier_raw c zero))
  have same:(∑'n:ℕ,quarterTerm c n)=Rq (fourierL2 (fullFloorValue c zero))-
      (2*deriv (poleFreeSource c) 1/(1-star c.value)) • Cq:=by
    apply Lp.ext
    filter_upwards [sumRaw,terms,restricted,
      Lp.coeFn_sub (Rq (fourierL2 (fullFloorValue c zero)))
        ((2*deriv (poleFreeSource c) 1/(1-star c.value)) • Cq),
      Lp.coeFn_smul (2*deriv (poleFreeSource c) 1/(1-star c.value)) Cq,intervalConstant_coeFn q]
      with x actual pointRead frequency subtracted scalar constant
    rw [subtracted,Pi.sub_apply,frequency,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one]
    have actualPrice:=actual_complete_fourier_source c zero x
    exact (actual.congr_fun (fun n=>(pointRead n).symm)).unique actualPrice
  rw [←same]
  exact summable.hasSum

/-- The source bank is fed to the original P0 and BI; the actual mass is killed only by P0. -/
theorem actual_inverse_quarter_hasSum (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    HasSum (fun n:ℕ=>BI (Constructor.zeroMean (quarterTerm c n)))
      (BI (Constructor.zeroMean (Rq (fourierL2 (fullFloorValue c zero))))) :=by
  have source:=(actual_quarter_hasSum c zero).mapL (burnolMeanZeroBlockInverse.comp Constructor.zeroMean)
  simp only [ContinuousLinearMap.comp_apply,map_sub,map_smul,Constructor.zeroMean_constant,smul_zero,
    sub_zero,map_zero] at source
  exact source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
