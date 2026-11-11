import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "BI" => burnolMeanZeroBlockInverse
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem dual_smooth_split (w:ℂ) (below:w.re<1):
    smooth (dualRaw w below) (actual_dual_integrable w below)=firstSource w below+S (correction w below):=by
  have bDomain:Integrable (correctionRaw w below) μq:=(actual_correction_continuous w below).integrableOn_Icc
  change smooth (fun x=>seedRaw w x+correctionRaw w below x)
    ((actual_seed_integrable w below).add bDomain)=_
  rw [actual_smooth_add _ _ (actual_seed_integrable w below) bDomain,
    actual_smooth_congr (correctionRaw w below) (correction w below)
      bDomain ((Lp.memLp (correction w below:Hq)).integrable (by norm_num))
      (actual_correction_raw w below).symm,actual_smooth_state]
  rfl

private theorem correction_smooth_dual (w:ℂ) (below:w.re<1):
    S (smooth (dualRaw w below) (actual_dual_integrable w below))=correction w below:=by
  rw [dual_smooth_split,map_add]
  linear_combination (norm:=module) -(actual_correction_equation w below)

private theorem smooth_dual_inverse (w:ℂ) (below:w.re<1):
    smooth (dualRaw w below) (actual_dual_integrable w below)=BI (firstSource w below):=by
  have equation:L (smooth (dualRaw w below) (actual_dual_integrable w below))=firstSource w below:=by
    change smooth (dualRaw w below) (actual_dual_integrable w below)-
      S (S (smooth (dualRaw w below) (actual_dual_integrable w below)))=_
    rw [correction_smooth_dual,dual_smooth_split]
    module
  have recovered:=congrArg BI equation
  change (BI*L) (smooth (dualRaw w below) (actual_dual_integrable w below))=BI (firstSource w below) at recovered
  have left:BI*L=1:=Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  rwa [left,one_apply_eq_self] at recovered

private theorem seed_quarter_balance (c:BurnolCompletedMellinCoordinate):
    Constructor.compact (Constructor.fourierRaw (seedRaw c.value))
        (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne))+
      Rq (ForcingWhole.whole c)=
      ForcingPrimitive.leadingCoefficient c • SingularCounting.powerL2 c:=by
  apply Lp.ext
  have force:(Rq (ForcingWhole.whole c):ℝ→ℂ)=ᵐ[μq]ForcingWhole.raw c:=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (ForcingWhole.whole c)).trans
      (ae_restrict_of_ae (ForcingWhole.whole_read c))
  filter_upwards [Lp.coeFn_add
      (Constructor.compact (Constructor.fourierRaw (seedRaw c.value))
        (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne))) (Rq (ForcingWhole.whole c)),
    Constructor.compact_read (Constructor.fourierRaw (seedRaw c.value))
      (actual_fourier_continuous _ (actual_seed_integrable c.value c.belowOne)),force,
    Lp.coeFn_smul (ForcingPrimitive.leadingCoefficient c) (SingularCounting.powerL2 c),
    SingularCounting.power_coeFn c,ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
    with x added seed forcing scalar power nonzero
  rw [added,Pi.add_apply,seed,forcing,scalar,Pi.smul_apply,smul_eq_mul,power]
  simpa only [SingularCounting.powerRaw,add_comm] using actual_seed_fourier_balance_abs c x nonzero

/-- Both actual Fourier faces generate the original forcing at the same legal parameter. -/
theorem actual_original_first_source (c:BurnolCompletedMellinCoordinate):
    firstSource c.value c.belowOne=
      ForcingPrimitive.leadingCoefficient c • centeredLogColumn c 0-
        burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula c):=by
  have source:=congrArg Constructor.zeroMean (seed_quarter_balance c)
  rw [map_add,map_smul] at source
  change firstSource c.value c.belowOne+
      burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula c)=
      ForcingPrimitive.leadingCoefficient c • centeredLogColumn c 0 at source
  linear_combination (norm:=module) source

/-- This is the original L1 dual's full smoothed face, not an illegal complementary L2 column. -/
theorem actual_original_dual_fourier_source (c:BurnolCompletedMellinCoordinate):
    smooth (dualRaw c.value c.belowOne) (actual_dual_integrable c.value c.belowOne)=
      ForcingPrimitive.leadingCoefficient c • logBFirst c 0-burnolRieszSingleFourierSource c:=by
  rw [smooth_dual_inverse,actual_original_first_source,map_sub,map_smul]
  rfl

theorem actual_original_dual_correction (c:BurnolCompletedMellinCoordinate):
    correction c.value c.belowOne=
      ForcingPrimitive.leadingCoefficient c • S (logBFirst c 0)-S (burnolRieszSingleFourierSource c):=by
  rw [←correction_smooth_dual,actual_original_dual_fourier_source,map_sub,map_smul]

private theorem original_correction_fourier (c:BurnolCompletedMellinCoordinate):
    Constructor.fourierRaw (correction c.value c.belowOne:Hq)=
      ForcingPrimitive.leadingCoefficient c • Constructor.fourierRaw (S (logBFirst c 0):Hq)-
        Constructor.fourierRaw (S (burnolRieszSingleFourierSource c):Hq):=by
  let reader:Hq→ₗ[ℂ](ℝ→ℂ):={
    toFun:=burnolRadiusTruncatedFourierRaw q
    map_add':=burnolRadiusTruncatedFourierRaw_add
    map_smul':=burnolRadiusTruncatedFourierRaw_smul }
  have state:=congrArg (fun a:M=>(a:Hq)) (actual_original_dual_correction c)
  have source:=congrArg reader state
  change reader (correction c.value c.belowOne:Hq)=
    reader (ForcingPrimitive.leadingCoefficient c • (S (logBFirst c 0):Hq)-
      (S (burnolRieszSingleFourierSource c):Hq)) at source
  rw [map_sub,map_smul] at source
  exact source

/-- The actual original B and log return feet replace the whole same-N inverse bank. -/
theorem actual_complete_native_programme (c:BurnolCompletedMellinCoordinate) (N:ℕ) (y:ℝ):
    programme c N y=
      (∑n∈Finset.range N,(((n+1:ℕ):ℂ)⁻¹)*Constructor.fourierRaw (seedRaw c.value) (y/(n+1:ℕ)))+
      ForcingPrimitive.leadingCoefficient c*
        (∑n∈Finset.range N,(((n+1:ℕ):ℂ)⁻¹)*Constructor.fourierRaw (S (logBFirst c 0):Hq) (y/(n+1:ℕ)))-
      (∑n∈Finset.range N,(((n+1:ℕ):ℂ)⁻¹)*
        Constructor.fourierRaw (S (burnolRieszSingleFourierSource c):Hq) (y/(n+1:ℕ))):=by
  rw [actual_complete_finite_programme]
  simp only [original_correction_fourier,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_sub,Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  have same:(∑n∈Finset.range N,(((n+1:ℕ):ℂ)⁻¹)*
      (ForcingPrimitive.leadingCoefficient c*Constructor.fourierRaw (S (logBFirst c 0):Hq) (y/(n+1:ℕ))))=
      ∑n∈Finset.range N,ForcingPrimitive.leadingCoefficient c*
        ((((n+1:ℕ):ℂ)⁻¹)*Constructor.fourierRaw (S (logBFirst c 0):Hq) (y/(n+1:ℕ))):=by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [same]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
