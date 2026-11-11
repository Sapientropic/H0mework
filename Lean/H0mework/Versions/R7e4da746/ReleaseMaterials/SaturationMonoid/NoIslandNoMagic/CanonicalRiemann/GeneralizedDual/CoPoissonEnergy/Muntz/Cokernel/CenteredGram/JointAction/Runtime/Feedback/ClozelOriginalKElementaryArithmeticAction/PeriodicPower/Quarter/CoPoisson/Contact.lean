import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Contact
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Completion
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "μq" => volume.restrict (symmetricInterval q)

def windowRead (c : BurnolCompletedMellinCoordinate) (h : ℝ) (test : Hq) : ℂ :=
  ∫x:ℝ in symmetricInterval q,star (test x)*burnolInnerGapForward (directRaw c h) x

private theorem window_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (test : Hq) :
    inner ℂ test (Rq (fourierL2 (countedValue c zero h nonnegative))+directMean c h • intervalConstant q)=
      windowRead c h test := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (Rq (fourierL2 (countedValue c zero h nonnegative)))
      (directMean c h • intervalConstant q),
    Lp.coeFn_smul (directMean c h) (intervalConstant q),intervalConstant_coeFn q,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (fourierL2 (countedValue c zero h nonnegative)),
    ae_restrict_of_ae (actual_difference_forward_raw c zero h nonnegative)]
    with x added scalar constant restricted source
  change Rq (fourierL2 (countedValue c zero h nonnegative)) x=
    fourierL2 (countedValue c zero h nonnegative) x at restricted
  change inner ℂ (test x) ((Rq (fourierL2 (countedValue c zero h nonnegative))+
    directMean c h • intervalConstant q:Hq) x)=_
  rw [added,Pi.add_apply,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one,restricted,source]
  simp only [RCLike.inner_apply,directField,sub_add_cancel,starRingEnd_apply]
  exact mul_comm _ _

/-- The full direct arithmetic field is read on the original compact test, before its mean is removed. -/
theorem actual_compact_clock_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (test : Hq) :
    inner ℂ (E test) (burnolMultiplicativeDilation h (wholeValue c zero h positive)-
      Complex.exp ((star c.value-1/2)*(h:ℂ)) • wholeValue c zero h positive)=
      windowRead c h test-directMean c h*inner ℂ test (intervalConstant q) := by
  rw [actual_whole_clock c zero h positive]
  have adjoint:inner ℂ (E test) (fourierL2 (countedValue c zero h positive.le))=
      inner ℂ test (Rq (fourierL2 (countedValue c zero h positive.le))) :=
    ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _
  rw [adjoint]
  have actual:=window_read c zero h positive.le test
  rw [inner_add_right,inner_smul_right] at actual
  linear_combination actual

theorem actual_meanZero_clock_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (test : M) :
    inner ℂ (E (test:Hq)) (burnolMultiplicativeDilation h (wholeValue c zero h positive)-
      Complex.exp ((star c.value-1/2)*(h:ℂ)) • wholeValue c zero h positive)=
      windowRead c h (test:Hq) := by
  have meanZero:inner ℂ (intervalConstant q) (test:Hq)=0:=
    (Submodule.mem_orthogonal _ _).mp test.property _ (Submodule.mem_span_singleton_self _)
  have other:inner ℂ (test:Hq) (intervalConstant q)=0 := by
    rw [inner_eq_zero_symm]
    exact meanZero
  rw [actual_compact_clock_read c zero h positive,other,mul_zero,sub_zero]

theorem actual_original_b_clock (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) :
    inner ℂ (E (burnolRieszSingleFourierSource c:Hq))
      (burnolMultiplicativeDilation h (wholeValue c zero h positive)-
        Complex.exp ((star c.value-1/2)*(h:ℂ)) • wholeValue c zero h positive)=
      windowRead c h (burnolRieszSingleFourierSource c:Hq) :=
  actual_meanZero_clock_read c zero h positive (burnolRieszSingleFourierSource c)

theorem actual_original_Sb_clock (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) :
    inner ℂ (E (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c):Hq))
      (burnolMultiplicativeDilation h (wholeValue c zero h positive)-
        Complex.exp ((star c.value-1/2)*(h:ℂ)) • wholeValue c zero h positive)=
      windowRead c h (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c):Hq) :=
  actual_meanZero_clock_read c zero h positive
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c))

def scaledWindowRead (c : BurnolCompletedMellinCoordinate) (h t : ℝ) (test : Hq) : ℂ :=
  ∫x:ℝ in symmetricInterval q,star (test x)*((Real.exp (t/2):ℂ)*directField c h (Real.exp t*x))

private theorem dilated_restriction_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (t : ℝ) :
    (Rq (burnolMultiplicativeDilation t (fourierL2 (countedValue c zero h nonnegative))):ℝ→ℂ)=ᵐ[μq]
      (fun x:ℝ=>(Real.exp (t/2):ℂ)*directField c h (Real.exp t*x)) := by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp t*x) volume volume:=by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ:=(volume:Measure ℝ)) (Real.exp_ne_zero t)
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolMultiplicativeDilation t (fourierL2 (countedValue c zero h nonnegative))),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn t (fourierL2 (countedValue c zero h nonnegative))),
    ae_restrict_of_ae (scale.ae (actual_difference_forward_raw c zero h nonnegative))]
    with x restricted dilation source
  change Rq (burnolMultiplicativeDilation t (fourierL2 (countedValue c zero h nonnegative))) x=_ at restricted
  rw [restricted,dilation]
  change (Real.exp (t/2):ℂ)*(fourierL2 (countedValue c zero h nonnegative)) (Real.exp t*x)=_
  rw [source]

theorem actual_scaled_window_integrable (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (t : ℝ) (test : Hq) :
    IntegrableOn (fun x:ℝ=>star (test x)*((Real.exp (t/2):ℂ)*directField c h (Real.exp t*x))) (symmetricInterval q) :=
  (Lp.memLp test).star.integrable_mul ((Lp.memLp
    (Rq (burnolMultiplicativeDilation t (fourierL2 (countedValue c zero h nonnegative))))).ae_eq
      (dilated_restriction_raw c zero h nonnegative t))

theorem actual_scaled_window_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (t : ℝ) (test : Hq) :
    inner ℂ (E test) (burnolMultiplicativeDilation t (fourierL2 (countedValue c zero h nonnegative)))=
      scaledWindowRead c h t test := by
  have adjoint:inner ℂ (E test) (burnolMultiplicativeDilation t (fourierL2 (countedValue c zero h nonnegative)))=
      inner ℂ test (Rq (burnolMultiplicativeDilation t (fourierL2 (countedValue c zero h nonnegative)))) :=
    ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction _ _
  rw [adjoint,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [dilated_restriction_raw c zero h nonnegative t] with x source
  change inner ℂ (test x)
    (Rq (burnolMultiplicativeDilation t (fourierL2 (countedValue c zero h nonnegative))) x)=_
  rw [source]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  exact mul_comm _ _

/-- The absolute whole-value contact is generated by the same strong programme, with every scaled window retained. -/
theorem actual_compact_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (test : Hq) :
    HasSum (fun n:ℕ=>-(inverseClock c h)^(n+1)*scaledWindowRead c h ((n:ℝ)*h) test)
      (inner ℂ (E test) (wholeValue c zero h positive)) := by
  have generated:=(innerSL ℂ (E test)).hasSum (actual_value_completion c zero h positive)
  change HasSum (fun n:ℕ=>inner ℂ (E test) (valuePiece c zero h positive.le n))
    (inner ℂ (E test) (wholeValue c zero h positive)) at generated
  simpa only [valuePiece,inner_smul_right,actual_scaled_window_read c zero h positive.le]
    using generated

theorem actual_original_Sb_price (c d : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) :
    HasSum (fun n:ℕ=>-(inverseClock c h)^(n+1)*scaledWindowRead c h ((n:ℝ)*h)
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource d):Hq))
      (inner ℂ (E (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource d):Hq))
        (wholeValue c zero h positive)) :=
  actual_compact_price c zero h positive
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource d):Hq)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Contact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
