import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PowerHead
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
open private tateTail_read from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitFourier.DyadicSource
open private original_unit_fourier_gap from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource
local notation "q"=>(1/4:ℝ)
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

def powerRaw (c : BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval q).indicator (SingularCounting.powerRaw c)

def powerSource (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (SingularCounting.powerL2 c)

def powerValue (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -fourierL2 (burnolUnitTailResponse (barC c) 4)

theorem actual_power_raw (c : BurnolCompletedMellinCoordinate) :
    (powerSource c:ℝ→ℂ)=ᵐ[volume]powerRaw c := by
  have inside:∀ᵐx∂volume,x∈symmetricInterval q→SingularCounting.powerL2 c x=SingularCounting.powerRaw c x :=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (SingularCounting.power_coeFn c)
  filter_upwards [burnolQuarterZeroExtension_coe (SingularCounting.powerL2 c),inside] with x extended raw
  change burnolQuarterZeroExtension (SingularCounting.powerL2 c) x=_
  rw [extended]
  by_cases member:x∈symmetricInterval q
  · rw [indicator_of_mem member,powerRaw,indicator_of_mem member,raw member]
  · rw [indicator_of_notMem member,powerRaw,indicator_of_notMem member]

/-- The compact singular power is the negative Tate image of the original complete Unit tail. -/
theorem actual_power_tate_source (c : BurnolCompletedMellinCoordinate) :
    powerSource c= -burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail (barC c) 4 (by norm_num)) := by
  apply Lp.ext
  have tail:=tateTail_read (barC c) 4 (by norm_num)
  norm_num only [show (4:ℝ)⁻¹=q by norm_num] at tail
  filter_upwards [actual_power_raw c,Lp.coeFn_neg (burnolTateReciprocalL2
    (burnolRadiusNormalizedUnitTail (barC c) 4 (by norm_num))),tail,
    volume.ae_ne q,volume.ae_ne (-q)] with x source negative tate notPlus notMinus
  rw [source,negative,Pi.neg_apply,tate]
  have notBoundary:|x|≠q := by
    intro equality
    rcases eq_or_eq_neg_of_abs_eq equality with atPlus|atMinus
    · exact notPlus atPlus
    · exact notMinus (by linarith)
  by_cases inside:|x|<q
  · rw [powerRaw,indicator_of_mem (show x∈symmetricInterval q from abs_le.mp inside.le),if_pos inside]
    simp only [SingularCounting.powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,neg_neg]
  · have outside:x∉symmetricInterval q:=fun member=>inside (lt_of_le_of_ne (abs_le.mpr member) notBoundary)
    rw [powerRaw,indicator_of_notMem outside,if_neg inside,neg_zero]

/-- This is the actual full co-Poisson realization, before taking any quarter restriction. -/
theorem actual_power_realizes (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (powerSource c) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (powerValue c)) test := by
  rw [actual_power_tate_source,←burnolRemainderSourceReadCLM_apply,map_neg,
    burnolRemainderSourceReadCLM_apply]
  have realized:=burnolRemainderRealization_fourier
    (burnolRadiusNormalizedUnitTail (barC c) 4 (by norm_num)) (burnolUnitTailResponse (barC c) 4)
    (burnolUnitTailResponse_realizes (barC c) 4 (by norm_num) (by norm_num)) test
  rw [realized,powerValue,map_neg,neg_apply]

private theorem coordinate_eq {a b : BurnolCompletedMellinCoordinate} (same : a.value=b.value) : a=b := by
  cases a
  cases b
  cases same
  rfl

private theorem conjugate_zero (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    riemannZeta (barC c).value=0 := by
  simpa only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_def,zero,map_zero] using riemannZeta_conj c.value

private theorem power_coefficient (c : BurnolCompletedMellinCoordinate) :
    -(-(4:ℂ)^(1-star c.value)/(1-star c.value))=
      -(q:ℂ)^(star c.value-1)/(star c.value-1) := by
  have reciprocal:(4:ℂ)^(1-star c.value)=(q:ℂ)^(star c.value-1) := by
    rw [show (q:ℂ)=((4:ℝ):ℂ)⁻¹ by norm_num,
      Complex.inv_cpow_ofReal_nonneg (by norm_num),←Complex.cpow_neg]
    congr 1
    ring
  rw [reciprocal,show 1-star c.value= -(star c.value-1) by ring,div_neg]
  ring

theorem actual_power_value_quarter (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    burnolQuarterRestriction (powerValue c)=
      (-(q:ℂ)^(star c.value-1)/(star c.value-1)) • intervalConstant q := by
  let observation:=burnolPaZeroObservation (barC c) (conjugate_zero c zero)
  let half:OriginalKCombCalculation.Half observation:=⟨(barC c).rightHalf⟩
  have same:burnolDivisionZeroCompletedMellinCoordinate observation half.down=barC c := by
    apply coordinate_eq
    rfl
  have gap:=original_unit_fourier_gap observation
    (burnolPaZeroObservation_nontrivial (barC c) (conjugate_zero c zero)) half
  rw [same] at gap
  rw [powerValue,map_neg,gap,←neg_smul]
  change (-(-(4:ℂ)^(1-star c.value)/(1-star c.value))) • intervalConstant q=_
  rw [power_coefficient]

theorem actual_power_value_raw_quarter (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    (powerValue c:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]
      fun _=> -(q:ℂ)^(star c.value-1)/(star c.value-1) := by
  have gap:=actual_power_value_quarter c zero
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (powerValue c),
    Lp.coeFn_smul (-(q:ℂ)^(star c.value-1)/(star c.value-1)) (intervalConstant q),intervalConstant_coeFn q]
    with x restricted scalar constant
  have read:=congrArg (fun value:BurnolQuarterIntervalL2=>value x) gap
  change burnolQuarterRestriction (powerValue c) x=(powerValue c) x at restricted
  rw [restricted,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one] at read
  exact read

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PowerHead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
