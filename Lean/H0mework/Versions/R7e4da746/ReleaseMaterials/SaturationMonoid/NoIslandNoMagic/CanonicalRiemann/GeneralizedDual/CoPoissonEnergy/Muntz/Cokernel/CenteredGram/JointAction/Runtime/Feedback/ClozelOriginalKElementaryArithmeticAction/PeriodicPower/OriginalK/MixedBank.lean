import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.Alias
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativeContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Inverse

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.MixedBank
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszSource.Translator
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward InverseAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativeContact
open OriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.Alias
open scoped Topology InnerProductSpace
open private return_fourier_continuous from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.Alias
open private integer_sum window_norm_summable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
open private counting_sub from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WholeSourceWindow
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "P0" => Constructor.zeroMean
local notation "BI" => burnolMeanZeroBlockInverse
local notation "ell" => CenteredCountingDual.logarithm
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)

/-- The full original K alias and its A boundary term form one source before counting. -/
def mixedLocal (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ :=
  kernelAlias c (min q |x|)-Kernel.A c*(box (min q |x|)-box 0)

private theorem kernel_alias_continuous (c:BurnolCompletedMellinCoordinate):
    ContinuousOn (kernelAlias c) (symmetricInterval q) := by
  have original:ContinuousOn (aliasRaw c) (symmetricInterval q):=
    (actual_alias_raw_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2])
  apply (((original.sub continuousOn_const).sub (return_fourier_continuous c).continuousOn).add
    continuousOn_const).congr
  intro x hx
  exact actual_kernel_alias_read c x (abs_le.mpr hx)

theorem actual_mixed_local_continuous (c:BurnolCompletedMellinCoordinate):
    Continuous (mixedLocal c) := by
  have aliasPart:Continuous (fun x:ℝ=>kernelAlias c (min q |x|)):=
    (kernel_alias_continuous c).comp_continuous (continuous_const.min continuous_abs)
      (fun x=>⟨by have h:=le_min (by norm_num : (0:ℝ)≤q) (abs_nonneg x);linarith,
        min_le_left _ _⟩)
  exact aliasPart.sub (continuous_const.mul
    (((burnolRadiusTruncatedFourierRaw_continuous _).comp (continuous_const.min continuous_abs)).sub
      continuous_const))

def mixedQuarter (c:BurnolCompletedMellinCoordinate):Hq :=
  Constructor.compact (mixedLocal c) (actual_mixed_local_continuous c)

theorem actual_mixed_quarter_raw (c:BurnolCompletedMellinCoordinate):
    (mixedQuarter c:ℝ→ℂ)=ᵐ[μq]mixedLocal c:=Constructor.compact_read _ _

private theorem smooth_absolute (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    InverseTail.smoothFourier c |x|=InverseTail.smoothFourier c x := by
  have even:InverseTail.smoothFourier c (-x)=InverseTail.smoothFourier c x := by
    rw [ProlateKernel.original_return_kernel,ProlateKernel.original_return_kernel]
    apply integral_congr_ae
    filter_upwards with y
    simp only [ProlateKernel.kernel,Complex.ofReal_neg,mul_neg,neg_mul,Complex.cos_neg]
  rcases le_or_gt 0 x with nonnegative|negative
  · rw [abs_of_nonneg nonnegative]
  · rw [abs_of_neg negative,even]

/-- This identity identifies the independently generated K field with the actual Whole input. -/
theorem actual_regular_quarter_split (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    regularQuarter c zero=ForcingTail.forcingRemainderState c+
      WholeSourceWindow.smoothState c+mixedQuarter c := by
  apply Lp.ext
  filter_upwards [actual_regular_quarter_raw c zero,
    ForcingTail.forcingRemainderState_ae_raw c,WholeSourceWindow.smoothState_ae_raw c,
    actual_mixed_quarter_raw c,
    Lp.coeFn_add (ForcingTail.forcingRemainderState c+WholeSourceWindow.smoothState c) (mixedQuarter c),
    Lp.coeFn_add (ForcingTail.forcingRemainderState c) (WholeSourceWindow.smoothState c),
    ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (volume.ae_ne q),
    ae_restrict_of_ae (volume.ae_ne (-q))]
    with x raw forcing returned mixed outer inner inside upper lower
  rw [raw,outer,Pi.add_apply,inner,Pi.add_apply,forcing,returned,mixed]
  have strict:x∈Ioo (-q) q:=⟨lt_of_le_of_ne inside.1 (Ne.symm lower),lt_of_le_of_ne inside.2 upper⟩
  rw [regularCompactRaw,indicator_of_mem strict,regularLocal,min_eq_right (abs_le.mpr inside),
    actual_original_regular_field c zero |x| (by simpa only [abs_abs] using abs_le.mpr inside)]
  have forcingAbsolute:ForcingTail.forcingRemainder c |x|=ForcingTail.forcingRemainder c x:=by
    simp only [ForcingTail.forcingRemainder,ForcingTail.edgeRemainder,abs_abs]
  rw [forcingAbsolute,smooth_absolute,mixedLocal,min_eq_right (abs_le.mpr inside)]
  ring

private theorem cubic_norm_summable (state:Hq) (C:ℝ)
    (bound:∀a:ℝ,1≤a→‖countingWindow a state‖≤C*a⁻¹^3):
    Summable (fun n:ℕ=>‖countingWindow (n:ℝ) state‖) := by
  have powers:Summable (fun n:ℕ=>(n:ℝ)⁻¹^3):=by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by norm_num : 1<(3:ℕ)))
  apply (powers.mul_left C).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro n
  by_cases atZero:n=0
  · simp [atZero,countingWindow]
  · exact bound n (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr atZero)

private theorem forcing_norm_summable (c:BurnolCompletedMellinCoordinate):
    Summable (fun n:ℕ=>‖countingWindow (n:ℝ) (ForcingTail.forcingRemainderState c)‖):=
  cubic_norm_summable _ _ (WholeSourceWindow.forcing_window_norm_bound c)

private theorem smooth_norm_summable (c:BurnolCompletedMellinCoordinate):
    Summable (fun n:ℕ=>‖countingWindow (n:ℝ) (WholeSourceWindow.smoothState c)‖):=
  cubic_norm_summable _ _ (WholeSourceWindow.smooth_window_norm_bound c)

theorem actual_mixed_norm_summable (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Summable (fun n:ℕ=>‖countingWindow (n:ℝ) (mixedQuarter c)‖) := by
  have source:mixedQuarter c=regularQuarter c zero-ForcingTail.forcingRemainderState c-
      WholeSourceWindow.smoothState c := by rw [actual_regular_quarter_split];module
  have dominant:=((window_norm_summable c zero).add (forcing_norm_summable c)).add (smooth_norm_summable c)
  apply dominant.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro n
  rw [source,counting_sub,counting_sub]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)

def mixedValue (c:BurnolCompletedMellinCoordinate):Hq :=
  ∑'n:ℕ,countingWindow (n:ℝ) (mixedQuarter c)

def mixedBank (c:BurnolCompletedMellinCoordinate):M:=P0 (mixedValue c)

/-- The complete mean-zero source includes the new K bank before the original logarithmic fee. -/
theorem actual_complete_forward_bank (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    P0 (forwardQuarter c zero)=CountingForcing.integerSource c+
      ReturnedArithmeticKernel.integerSource c+mixedBank c := by
  have source:mixedQuarter c=regularQuarter c zero-ForcingTail.forcingRemainderState c-
      WholeSourceWindow.smoothState c := by rw [actual_regular_quarter_split];module
  have complete:mixedValue c=forwardQuarter c zero-
      (∑'n:ℕ,countingWindow (n:ℝ) (ForcingTail.forcingRemainderState c))-
      (∑'n:ℕ,countingWindow (n:ℝ) (WholeSourceWindow.smoothState c)) := by
    unfold mixedValue
    simp_rw [source,counting_sub]
    rw [Summable.tsum_sub ((window_norm_summable c zero).of_norm.sub
        (forcing_norm_summable c).of_norm) (smooth_norm_summable c).of_norm,
      Summable.tsum_sub (window_norm_summable c zero).of_norm (forcing_norm_summable c).of_norm,
      integer_sum]
  rw [mixedBank,complete,map_sub,map_sub]
  change P0 (forwardQuarter c zero)=CountingForcing.integerSource c+
    ReturnedArithmeticKernel.integerSource c+
    (P0 (forwardQuarter c zero)-CountingForcing.integerSource c-ReturnedArithmeticKernel.integerSource c)
  module

theorem actual_complete_counting_exchange (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    P0 (forwardQuarter c zero)-P0 (Rq (AmbientCounting.value c))=
      mixedBank c+fourierMean c • ell := by
  rw [actual_complete_forward_bank,ReturnedArithmeticKernel.original_forward c zero]
  module

/-- The original inverse now consumes the full K lattice bank and the original Fourier mean together. -/
theorem actual_original_inverse_bank (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    sourceInverse c zero=BI (P0 (Rq (AmbientCounting.value c))+
      mixedBank c+fourierMean c • ell) := by
  unfold sourceInverse
  congr 1
  have read:=actual_complete_counting_exchange c zero
  calc
    _=(mixedBank c+fourierMean c • ell)+P0 (Rq (AmbientCounting.value c)):=sub_eq_iff_eq_add.mp read
    _=_:=by module

def mixedRawTerm (c:BurnolCompletedMellinCoordinate) (n:ℕ) (x:ℝ):ℂ :=
  ((n+1:ℕ):ℂ)⁻¹*((∑'k:ℤ,kernelAliasTerm c k (|x|/(n+1:ℕ)))-
    Kernel.A c*(box (|x|/(n+1:ℕ))-box 0))

/-- All additive aliases and the A box share the same actual multiplicative clock. -/
theorem actual_mixed_programme (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    ∀ᵐx:ℝ∂μq,HasSum (fun n:ℕ=>mixedRawTerm c n x) (mixedValue c x) := by
  have normSum:=actual_mixed_norm_summable c zero
  have normShift:Summable (fun n:ℕ=>‖countingWindow ((n+1:ℕ):ℝ) (mixedQuarter c)‖):=
    (summable_nat_add_iff 1).mpr normSum
  have pointwise:=Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr normShift)
  have shift:(∑'n:ℕ,countingWindow ((n+1:ℕ):ℝ) (mixedQuarter c))=mixedValue c := by
    have source:=normSum.of_norm.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one,Nat.cast_zero,
      show countingWindow (0:ℝ) (mixedQuarter c)=0 by simp [countingWindow],zero_add] at source
    exact source
  have terms:∀ᵐx:ℝ∂μq,∀n:ℕ,
      (countingWindow ((n+1:ℕ):ℝ) (mixedQuarter c):Hq) x=mixedRawTerm c n x := by
    rw [ae_all_iff]
    intro n
    have source:=countingWindow_raw ((n+1:ℕ):ℝ) (by positivity) (mixedQuarter c)
      (mixedLocal c) (actual_mixed_quarter_raw c)
    filter_upwards [source,ae_restrict_mem (measurableSet_symmetricInterval q)] with x read inside
    have one:(1:ℝ)≤(n+1:ℕ):=by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have positive:(0:ℝ)<(n+1:ℕ):=by positivity
    have moved:|x/(n+1:ℕ)|≤q := by
      rw [abs_div,abs_of_pos positive,div_le_iff₀ positive]
      have bounded:=abs_le.mpr inside
      nlinarith
    rw [read,countingRaw,indicator_of_mem (show x/(n+1:ℕ)∈symmetricInterval q from abs_le.mp moved),mixedLocal,min_eq_right moved]
    simp only [abs_div,abs_of_pos positive,Complex.ofReal_natCast,mixedRawTerm,kernelAlias]
  filter_upwards [pointwise,terms] with x series read
  rw [shift] at series
  exact series.congr_fun (fun n=>(read n).symm)

private theorem mean_zero_test (test:M) (state:Hq):
    inner ℂ (test:Hq) (P0 state:Hq)=inner ℂ (test:Hq) state := by
  rw [Constructor.zeroMean_read,inner_sub_right,inner_smul_right]
  have orthogonal:inner ℂ (test:Hq) (intervalConstant q)=0 := by
    apply inner_eq_zero_symm.mp
    exact (Submodule.mem_orthogonal _ _).mp test.property _ (Submodule.mem_span_singleton_self _)
  rw [orthogonal,mul_zero,sub_zero]

theorem actual_native_joint_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (test:M):
    inner ℂ (test:Hq) (forwardQuarter c zero)=
      inner ℂ (test:Hq) (Rq (AmbientCounting.value c))+
      inner ℂ (test:Hq) (mixedBank c:Hq)+
      fourierMean c*inner ℂ (test:Hq) (ell:Hq) := by
  have read:=congrArg (fun state:M=>inner ℂ (test:Hq) (state:Hq))
    (actual_complete_counting_exchange c zero)
  simp only [Submodule.coe_sub,Submodule.coe_add,Submodule.coe_smul,inner_sub_right,
    inner_add_right,inner_smul_right,mean_zero_test] at read
  linear_combination read

/-- The original counted b slot reads the full mixed bank, including its original log mean. -/
theorem actual_B_mixed_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    inner ℂ (CountingDual.value d) (regularSource c zero)=
      inner ℂ (burnolRieszSingleFourierSource d:Hq) (Rq (AmbientCounting.value c))+
      inner ℂ (burnolRieszSingleFourierSource d:Hq) (mixedBank c:Hq)+
      fourierMean c*inner ℂ (burnolRieszSingleFourierSource d:Hq) (ell:Hq) := by
  rw [←actual_B_contact]
  exact actual_native_joint_price c zero _

theorem actual_Sb_mixed_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    inner ℂ (ReturnCounting.value d) (regularSource c zero)=
      inner ℂ (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource d):Hq)
        (Rq (AmbientCounting.value c))+
      inner ℂ (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource d):Hq) (mixedBank c:Hq)+
      fourierMean c*inner ℂ (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource d):Hq) (ell:Hq) := by
  rw [←actual_Sb_contact]
  exact actual_native_joint_price c zero _

end OriginalKElementaryArithmeticAction.PeriodicPower.OriginalK.MixedBank
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
