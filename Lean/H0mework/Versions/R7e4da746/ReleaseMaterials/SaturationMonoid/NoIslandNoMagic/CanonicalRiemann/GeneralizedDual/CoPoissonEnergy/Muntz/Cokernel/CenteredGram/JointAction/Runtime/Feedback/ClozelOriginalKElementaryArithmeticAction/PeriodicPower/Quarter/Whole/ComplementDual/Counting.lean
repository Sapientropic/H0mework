import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.WeightedCounting
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Counting
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.WeightedCounting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology InnerProductSpace
open private weightedRawTerm raw_sum from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension

def dualWeighted (w:ℂ) (below:w.re<1):Hq:=
  weightedQuarter (dualRaw w below) (actual_dual_weighted_memLp w below)

def dualCounting (w:ℂ) (below:w.re<1):BurnolL2:=reverseCount (dualWeighted w below)

private theorem extension_raw (w:ℂ) (below:w.re<1):
    (E (dualWeighted w below):ℝ→ℂ)=ᵐ[volume]
      (symmetricInterval q).indicator (fun x:ℝ=>((|x|:ℝ):ℂ)*dualRaw w below x):=by
  have localRead:∀ᵐx:ℝ∂volume,x∈symmetricInterval q→
      dualWeighted w below x=((|x|:ℝ):ℂ)*dualRaw w below x:=by
    exact (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
      (actual_weighted_raw (dualRaw w below) (actual_dual_weighted_memLp w below))
  filter_upwards [burnolQuarterZeroExtension_coe (dualWeighted w below),localRead]
    with x extended read
  rw [extended]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,read inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

private theorem term_raw (w:ℂ) (below:w.re<1) (n:ℕ):
    (reverseTerm (dualWeighted w below) n:ℝ→ℂ)=ᵐ[volume]
      weightedRawTerm (dualRaw w below) n:=by
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  have native:=DualSourceRaw.channel_coeFn _ _ (extension_raw w below) ((n+1:ℕ):ℝ) positive
  filter_upwards [native,Lp.coeFn_smul (((n+1:ℕ):ℂ)⁻¹)
    (ContinuousChannels.channel 1 (n+1:ℕ) (E (dualWeighted w below)))] with x counted scalar
  change reverseTerm (dualWeighted w below) n x=_ at scalar
  rw [scalar,Pi.smul_apply,smul_eq_mul,counted,weightedRawTerm]
  by_cases inside:((n+1:ℕ):ℝ)*x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,abs_mul,abs_of_pos positive,Complex.ofReal_mul]
    simp only [Complex.ofReal_natCast]
    field_simp
  · rw [indicator_of_notMem inside,indicator_of_notMem inside,mul_zero,mul_zero]

/-- The singular dual is represented by the original finite floor grid after its real weight. -/
theorem actual_dual_counting_raw (w:ℂ) (below:w.re<1):
    (dualCounting w below:ℝ→ℂ)=ᵐ[volume]arithmeticRaw (dualRaw w below):=by
  have summation:=Lp.hasSum_coeFn_tsum
    (tsum_enorm_ne_top_iff_summable_norm.mpr (actual_reverse_summable (dualWeighted w below)))
  have terms:∀ᵐx:ℝ∂volume,∀n:ℕ,reverseTerm (dualWeighted w below) n x=
      weightedRawTerm (dualRaw w below) n x:=ae_all_iff.mpr (term_raw w below)
  filter_upwards [summation,terms] with x sum read
  have actual:=sum.congr_fun (fun n=>(read n).symm)
  exact actual.tsum_eq.symm.trans (raw_sum (dualRaw w below) x)

theorem actual_dual_counting_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (w:ℂ) (below:w.re<1):
    inner ℂ (dualCounting w below) (E (normalizedRegular c zero))=
      ∫x:ℝ,star (dualRaw w below x)*quarterBankRaw c x ∂μq:=
  actual_l1_weighted_native_price (dualRaw w below) (actual_dual_integrable w below)
    (actual_dual_weighted_memLp w below) c zero

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Counting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
