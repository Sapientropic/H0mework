import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingFirstCell

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.NativeRegular
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open scoped Topology ContDiff
open private regularRaw regularSlope regular_derivative regular_continuous regular_slope_continuous raw_split
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action
open private periodic_measurable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "μq"=>volume.restrict (symmetricInterval q)

def nativeRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  regularRaw c x+ForcingMeanZero.mean c-Constructor.secondReturnRaw c x

def nativeSlope (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  regularSlope c x-deriv (Constructor.secondReturnRaw c) x

/-- Both singular forcing occurrences cancel on this actual source before any graph domain is claimed. -/
theorem actual_native_raw_difference (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    nativeRaw c x=periodicRaw c x-burnolRieszSingleFourierSourceRaw c x:=by
  have split:=raw_split c x
  rw [burnolRieszSingleFourierSourceRaw,ForcingMeanZero.forcingRaw_eq]
  unfold nativeRaw
  change regularRaw c x+ForcingMeanZero.mean c-
    burnolMeanZeroFourierRaw (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource c)) x=_
  linear_combination -split

theorem actual_native_compact_raw (c:BurnolCompletedMellinCoordinate):
    (nativeCompact c:ℝ→ℂ)=ᵐ[μq]nativeRaw c:=by
  filter_upwards [Lp.coeFn_sub (periodicQuarter c) (burnolRieszSingleFourierSource c:Hq),
    actual_periodic_quarter_raw c,burnolRieszSingleFourierSource_ae_raw c]
    with x subtraction wave source
  change (periodicQuarter c-(burnolRieszSingleFourierSource c:Hq):Hq) x=_
  rw [subtraction,Pi.sub_apply,wave,source,←actual_native_raw_difference]

theorem actual_native_continuous (c:BurnolCompletedMellinCoordinate):
    ContinuousOn (nativeRaw c) (Icc (0:ℝ) q):=by
  have regular:ContinuousOn (regularRaw c) (Icc (0:ℝ) q):=
    (regular_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2])
  exact (regular.add continuousOn_const).sub
    (actual_return_contDiff (Constructor.returnState c)).continuous.continuousOn

theorem actual_native_slope_continuous (c:BurnolCompletedMellinCoordinate):
    ContinuousOn (nativeSlope c) (Icc (0:ℝ) q):=by
  have regular:ContinuousOn (regularSlope c) (Icc (0:ℝ) q):=
    (regular_slope_continuous c).mono (by intro x hx;constructor <;> linarith [hx.1,hx.2])
  exact regular.sub ((actual_return_contDiff (Constructor.returnState c)).continuous_deriv (by norm_num)).continuousOn

theorem actual_native_derivative (c:BurnolCompletedMellinCoordinate) (x:ℝ) (inside:x∈Ioc (0:ℝ) q):
    HasDerivAt (nativeRaw c) (nativeSlope c x) x:=by
  have regular:=regular_derivative c x (by constructor <;> linarith [inside.1,inside.2])
  exact (regular.add_const _).sub
    (((actual_return_contDiff (Constructor.returnState c)).differentiable (by norm_num)) x).hasDerivAt

theorem actual_native_measurable (c:BurnolCompletedMellinCoordinate):Measurable (nativeRaw c):=by
  have b:Measurable (burnolRieszSingleFourierSourceRaw c):=by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (burnolRieszSingleFourierSourceRaw_continuousAt c
      (by simpa only [mem_compl_iff,mem_singleton_iff] using outside)).continuousWithinAt
  have same:nativeRaw c=fun x:ℝ=>periodicRaw c x-burnolRieszSingleFourierSourceRaw c x:=
    funext (actual_native_raw_difference c)
  rw [same]
  exact (periodic_measurable c).sub b

theorem actual_native_even (c:BurnolCompletedMellinCoordinate) (x:ℝ):nativeRaw c (-x)=nativeRaw c x:=by
  rw [actual_native_raw_difference,actual_native_raw_difference,OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action.actual_periodic_even,
    OriginalRieszFinitePairing.source_raw_even]

theorem actual_native_absolute (c:BurnolCompletedMellinCoordinate) (x:ℝ):nativeRaw c |x|=nativeRaw c x:=by
  by_cases positive:0≤x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive),actual_native_even]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.NativeRegular
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
