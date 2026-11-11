import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.FourierContact
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Completion
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "F"=>fourierL2
local notation "Rq"=>burnolQuarterRestriction
local notation "Eq"=>burnolQuarterZeroExtension
local notation "Cq"=>intervalConstant q

theorem actual_counted_quarter_dilation (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (nn:0≤h) (t:ℝ) (nonnegative:0≤t):
    Rq (burnolMultiplicativeDilation (-t) (countedValue c zero h nn))=
      ((Real.exp (-t/2):ℂ)*(-reciprocalMean c h)) • Cq:=by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp (-t)*x) volume volume:=by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ:=(volume:Measure ℝ)) (Real.exp_ne_zero (-t))
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolMultiplicativeDilation (-t) (countedValue c zero h nn)),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (-t) (countedValue c zero h nn)),
    ae_restrict_of_ae (scale.ae (actual_counted_raw c zero h nn)),
    ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul ((Real.exp (-t/2):ℂ)*(-reciprocalMean c h)) Cq,
    intervalConstant_coeFn q] with x restriction dilation source inside scalar constant
  have bound:|Real.exp (-t)*x|≤4:=by
    rw [abs_mul,abs_of_pos (Real.exp_pos (-t))]
    have small:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)
    have localBound:=mul_le_mul_of_nonneg_right small (abs_nonneg x)
    have quarter:=abs_le.mpr inside
    nlinarith
  change Rq (burnolMultiplicativeDilation (-t) (countedValue c zero h nn)) x=_ at restriction
  rw [restriction,dilation,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one]
  change (Real.exp (-t/2):ℂ)*(countedValue c zero h nn) (Real.exp (-t)*x)=_
  rw [source,actual_counted_gap c zero h nn _ bound]

def quarterFourierRead:BurnolL2→L[ℂ]Hq:=
  burnolQuarterRestriction.comp fourierL2.toContinuousLinearEquiv.toContinuousLinearMap

def ratio (c:BurnolCompletedMellinCoordinate) (h:ℝ):ℂ:=
  inverseClock c h*(Real.exp (-h/2):ℂ)

theorem actual_ratio_contraction (c:BurnolCompletedMellinCoordinate) (h:ℝ) (positive:0<h):
    ‖ratio c h‖<1:=by
  have source:=actual_clock_contraction c h positive
  have bounded:Real.exp (-h/2)≤1:=Real.exp_le_one_iff.mpr (by linarith)
  unfold ratio
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left bounded (norm_nonneg _)).trans_lt (by simpa only [mul_one] using source)

theorem actual_piece_fourier_contact (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h) (n:ℕ):
    quarterFourierRead (valuePiece c zero h positive.le n)=
      ((ratio c h)^n*(inverseClock c h*reciprocalMean c h)) • Cq:=by
  change Rq (F (valuePiece c zero h positive.le n))=_
  rw [valuePiece,map_smul,fourierL2_burnolMultiplicativeDilation,fourierL2_fourierL2,
    actual_counted_even,map_smul,actual_counted_quarter_dilation c zero h positive.le
      ((n:ℝ)*h) (mul_nonneg (Nat.cast_nonneg _) positive.le),smul_smul]
  congr 1
  have phase:(Real.exp (-((n:ℝ)*h)/2):ℂ)=(Real.exp (-h/2):ℂ)^n:=by
    rw [←Complex.ofReal_pow,←Real.exp_nat_mul]
    congr 2
    ring
  rw [phase,ratio,mul_pow,pow_succ]
  ring

private theorem normalized_mean (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    inverseClock c h*reciprocalMean c h=(ratio c h-1)*quarterMean c/4:=by
  have inverse:inverseClock c h*Complex.exp ((star c.value-1/2)*(h:ℂ))=1:=by
    rw [inverseClock,←Complex.exp_add,neg_add_cancel,Complex.exp_zero]
  rw [actual_reciprocal_mean]
  unfold ratio
  linear_combination -(quarterMean c/4)*inverse

theorem actual_whole_fourier_quarter (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    Rq (F (wholeValue c zero h positive))=(-quarterMean c/4) • Cq:=by
  have mapped:=quarterFourierRead.hasSum (actual_value_completion c zero h positive)
  have ratioSmall:=actual_ratio_contraction c h positive
  have nonzero:1-ratio c h≠0:=by
    intro same
    have atOne:ratio c h=1:=(sub_eq_zero.mp same).symm
    rw [atOne,norm_one] at ratioSmall
    exact (lt_irrefl (1:ℝ)) ratioSmall
  have geometric:= (hasSum_geometric_of_norm_lt_one ratioSmall).mul_right
    (inverseClock c h*reciprocalMean c h)
  have value:(1-ratio c h)⁻¹*(inverseClock c h*reciprocalMean c h)=-quarterMean c/4:=by
    rw [normalized_mean]
    field_simp [nonzero]
    ring
  rw [value] at geometric
  have bank:=geometric.smul_const Cq
  have same:HasSum (fun n:ℕ=>quarterFourierRead (valuePiece c zero h positive.le n))
      ((-quarterMean c/4) • Cq):=by
    simpa only [actual_piece_fourier_contact c zero h positive] using bank
  exact mapped.unique same

theorem actual_whole_fourier_sine_contact (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    Rq (F (wholeValue c zero h positive))=
      (-(1/(2*(Real.pi:ℂ)))*HurwitzZeta.sinZeta q (star c.value+1)) • Cq:=by
  rw [actual_whole_fourier_quarter,quarterMean,OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mean.Source.actual_quarter_mean]
  congr 1
  ring

theorem actual_original_fourier_B_contact (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (F (Eq (burnolRieszSingleFourierSource d:Hq))) (wholeValue c zero h positive)=0:=by
  have even:reflectL2 (Eq (burnolRieszSingleFourierSource d:Hq))=
      Eq (burnolRieszSingleFourierSource d:Hq):=by
    change reflectL2 (burnolRadiusZeroExtension q (burnolRieszSingleFourierSource d:Hq))=_
    rw [burnolRadiusZeroExtension_reflect,burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  have unitary:=fourierL2.inner_map_map (F (Eq (burnolRieszSingleFourierSource d:Hq)))
    (wholeValue c zero h positive)
  rw [fourierL2_fourierL2,even] at unitary
  rw [←unitary,show Eq=burnolQuarterRestriction.adjoint from rfl,
    ContinuousLinearMap.adjoint_inner_left,actual_whole_fourier_quarter,inner_smul_right]
  have mean:inner ℂ Cq (burnolRieszSingleFourierSource d:Hq)=0:=
    (Submodule.mem_orthogonal _ _).mp (burnolRieszSingleFourierSource d).property _
      (Submodule.mem_span_singleton_self _)
  rw [inner_eq_zero_symm.mp mean,mul_zero]

theorem actual_original_K_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (burnolCompletedMellinRieszVector d:BurnolL2) (wholeValue c zero h positive)=
      inner ℂ (gapState d) (wholeValue c zero h positive)+
      inner ℂ (Eq (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource d):Hq))
        (wholeValue c zero h positive):=by
  have source:=congrArg (fun state:BurnolL2=>inner ℂ state (wholeValue c zero h positive))
    (gapState_eq_kernel_add_correction d)
  rw [inner_add_left,sourceCorrection,inner_sub_left,
    actual_original_fourier_B_contact c d zero h positive] at source
  linear_combination -source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.FourierContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
