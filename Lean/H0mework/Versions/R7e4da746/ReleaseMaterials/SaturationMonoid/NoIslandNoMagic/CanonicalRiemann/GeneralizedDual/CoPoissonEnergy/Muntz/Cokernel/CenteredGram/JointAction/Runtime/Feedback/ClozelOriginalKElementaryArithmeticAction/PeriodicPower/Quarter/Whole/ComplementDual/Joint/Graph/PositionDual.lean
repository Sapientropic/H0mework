import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open scoped Topology InnerProductSpace
open private mean_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "leading" => ForcingPrimitive.leadingCoefficient

theorem actual_dual_correction_point (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (inside:x∈Icc (-q) q):
    correctionRaw c.value c.belowOne x=
      leading c*burnolMeanZeroFourierRaw (logBFirst c 0) x-burnolRieszReturnRaw c x:=by
  have same:(correction c.value c.belowOne:Hq)=
      leading c • (S (logBFirst c 0):Hq)-(S (burnolRieszSingleFourierSource c):Hq):=
    congrArg (fun a:BurnolQuarterMeanZeroCarrier=>(a:Hq)) (actual_original_dual_correction c)
  have source:=actual_correction_raw c.value c.belowOne
  rw [same] at source
  have raw:(fun x:ℝ=>correctionRaw c.value c.belowOne x)=ᵐ[μq]
      (fun x:ℝ=>leading c*burnolMeanZeroFourierRaw (logBFirst c 0) x-burnolRieszReturnRaw c x):=by
    filter_upwards [source,Lp.coeFn_sub (leading c • (S (logBFirst c 0):Hq))
      (S (burnolRieszSingleFourierSource c):Hq),
      Lp.coeFn_smul (leading c) (S (logBFirst c 0):Hq),
      burnolMeanZeroFourier_ae_raw (logBFirst c 0),
      burnolMeanZeroFourier_ae_raw (burnolRieszSingleFourierSource c)]
      with y original subtracted scalar logRaw bRaw
    rw [subtracted,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,logRaw,bRaw] at original
    exact original.symm
  exact MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (-q:ℝ)≠q) raw
    (actual_correction_continuous c.value c.belowOne).continuousOn
    ((continuous_const.mul ((burnolRadiusTruncatedFourierRaw_continuous _).sub continuous_const)).sub
      (burnolRieszReturnRaw_continuous c)).continuousOn inside

/-- The independent dual and original K position leg are restrictions of the same actual inverse source. -/
theorem actual_dual_original_position (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (positive:0<x) (inside:x≤q):
    dualRaw c.value c.belowOne x=positionSource c x+
      leading c*burnolMeanZeroFourierRaw (logBFirst c 0) x:=by
  rw [dualRaw,seedRaw,powerRaw,abs_of_pos positive,mul_sub,mean_power,
    actual_dual_correction_point c x ⟨by linarith,inside⟩]
  change (1/2:ℂ)*(x:ℂ)^(-star c.value)-GapEuler.gapMean q c+
    (leading c*burnolMeanZeroFourierRaw (logBFirst c 0) x-burnolRieszReturnRaw c x)=
    ((1/2:ℂ)*(x:ℂ)^(-star c.value)-GapEuler.gapMean q c-burnolRieszReturnRaw c x)+_
  ring

def logReturnFloor (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  ∑n∈DualSourceRaw.channels x,burnolMeanZeroFourierRaw (logBFirst c 0) ((n:ℝ)*|x|)

/-- The complete original grid couples C to the counted original position source; every integer remains. -/
theorem actual_counted_position_source (c:BurnolCompletedMellinCoordinate) (x:ℝ):
    fullFloorRaw c x=PositionCounting.eventRaw c x+leading c*logReturnFloor c x:=by
  classical
  by_cases zero:x=0
  · subst x
    simp [fullFloorRaw,floorRaw,PositionCounting.eventRaw,logReturnFloor,DualSourceRaw.channels]
  have even:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Even.actual_dual_even
  have point (n:ℕ) (member:n∈DualSourceRaw.channels x):
      dualRaw c.value c.belowOne ((n:ℝ)*x)=positionSource c ((n:ℝ)*|x|)+
        leading c*burnolMeanZeroFourierRaw (logBFirst c 0) ((n:ℝ)*|x|):=by
    have index:0<n:=(Finset.mem_Icc.mp member).1
    have nPositive:(0:ℝ)<n:=by exact_mod_cast index
    have size:(n:ℝ)*|x|≤q:=by
      have bounded: (n:ℝ)≤q/|x|:=(Nat.le_floor_iff' (by omega:n≠0)).mp (Finset.mem_Icc.mp member).2
      exact (le_div_iff₀ (abs_pos.mpr zero)).mp bounded
    have toAbs:dualRaw c.value c.belowOne ((n:ℝ)*x)=dualRaw c.value c.belowOne ((n:ℝ)*|x|):=by
      by_cases positive:0≤x
      · rw [abs_of_nonneg positive]
      · rw [abs_of_neg (lt_of_not_ge positive),mul_neg]
        simpa only [mul_neg,neg_neg] using even c.value c.belowOne ((n:ℝ)*(-x))
          ⟨le_trans (by norm_num : (-q:ℝ)≤0) (mul_nonneg nPositive.le (neg_nonneg.mpr (le_of_not_ge positive))),
           by simpa only [abs_of_neg (lt_of_not_ge positive)] using size⟩
    rw [toAbs]
    exact actual_dual_original_position c _ (mul_pos nPositive (abs_pos.mpr zero)) size
  change (∑n∈DualSourceRaw.channels x,dualRaw c.value c.belowOne ((n:ℝ)*x))=_
  rw [Finset.sum_congr rfl point,Finset.sum_add_distrib,←Finset.mul_sum]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
