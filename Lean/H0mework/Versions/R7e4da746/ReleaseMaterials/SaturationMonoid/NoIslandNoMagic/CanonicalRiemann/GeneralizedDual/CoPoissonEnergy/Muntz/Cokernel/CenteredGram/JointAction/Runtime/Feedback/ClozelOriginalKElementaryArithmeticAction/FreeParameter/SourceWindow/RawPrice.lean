import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.TopRead

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalUnitMellinSource.Band
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2
local notation "R" => burnolQuarterRestriction
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
open private top_quarter from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.TopRead

/-- The actual Tate Jacobian and the actual factor-16 dilation are retained in this raw read. -/
theorem actual_radius_fourier_raw (coordinate:BurnolCompletedMellinCoordinate) (h:ℝ) :
    (F (OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest coordinate h):ℝ→ℂ)=ᵐ[volume]
      fun x=>(((4*|x|:ℝ):ℂ)⁻¹)*movedTest coordinate h ((16:ℝ)*x)⁻¹ := by
  change (F (shiftedUnitTest coordinate h):ℝ→ℂ)=ᵐ[volume] _
  rw [actual_shifted_test_fourier]
  have pull:=(Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
    (r:=Real.exp (Real.log 16)) (Real.exp_ne_zero _)).ae
    (burnolTateReciprocalL2_coeFn (movedTest coordinate h))
  filter_upwards [burnolMultiplicativeDilation_coeFn (Real.log 16)
    (burnolTateReciprocalL2 (movedTest coordinate h)),pull] with x dilation read
  rw [dilation]
  change (Real.exp (Real.log 16/2):ℂ)*burnolTateReciprocalL2 (movedTest coordinate h)
    (Real.exp (Real.log 16)*x)=_
  rw [show burnolTateReciprocalL2 (movedTest coordinate h) (Real.exp (Real.log 16)*x)=
    burnolTateReciprocalRaw (movedTest coordinate h) (Real.exp (Real.log 16)*x) from read]
  rw [Real.exp_half,Real.exp_log (by norm_num:(0:ℝ)<16)]
  have squareRoot:Real.sqrt (16:ℝ)=4 := by
    rw [show (16:ℝ)=4^2 by norm_num,Real.sqrt_sq (by norm_num:(0:ℝ)≤4)]
  rw [squareRoot]
  simp only [burnolTateReciprocalRaw,abs_mul,abs_of_pos (by norm_num:(0:ℝ)<16)]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,mul_inv_rev]
  norm_num
  ring

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "d" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => unitPower observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

def fullTopRaw (x:ℝ) : ℂ :=
  bandMean d m+((|x|:ℝ):ℂ)^((d).value-1)*
    ((if q < |x| then bandCoefficient m*(bandLog |x|)^m else 0)-2*e)

private theorem actual_top_quarter_raw :
    ∀ᵐ x:ℝ ∂volume, |x|≤q → F (U m) x=
      bandMean d m+(-2*e)*((|x|:ℝ):ℂ)^((d).value-1) := by
  have paid:=top_quarter observation nontrivial half
  have read : (F (U m):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]
      fun x=>bandMean d m+(-2*e)*((|x|:ℝ):ℂ)^((d).value-1) := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (F (U m)),
      Lp.coeFn_add (bandMean d m • intervalConstant q) ((-2*e) • SingularCounting.powerL2 (barC d)),
      Lp.coeFn_smul (bandMean d m) (intervalConstant q),intervalConstant_coeFn q,
      Lp.coeFn_smul (-2*e) (SingularCounting.powerL2 (barC d)),SingularCounting.power_coeFn (barC d)]
      with x restricted added scalar constant powerScalar power
    have source:=congrArg (fun v:BurnolQuarterIntervalL2=>v x) paid
    change R (F (U m)) x=F (U m) x at restricted
    rw [restricted,added,Pi.add_apply,scalar,powerScalar,Pi.smul_apply,Pi.smul_apply,
      smul_eq_mul,smul_eq_mul,constant,mul_one,power] at source
    simpa only [SingularCounting.powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] using source
  have whole:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp read
  filter_upwards [whole] with x read inside
  exact read (abs_le.mp inside)

/-- The exact Xi-order Fourier source is explicit on the entire actual transformed-test window. -/
theorem actual_full_top_raw :
    ∀ᵐ x:ℝ ∂volume, |x|<2*q → F (U m) x=fullTopRaw observation half x := by
  filter_upwards [actual_top_quarter_raw observation nontrivial half,
    actual_top_band_raw observation nontrivial half] with x quarter band below
  by_cases inside:|x|≤q
  · rw [quarter inside,fullTopRaw,if_neg (not_lt_of_ge inside)]
    ring
  · have after:q < |x|:=lt_of_not_ge inside
    rw [band after below,topBandRaw,fullTopRaw,if_pos after]

/-- The complete original transformed top price is a literal finite integral of the original K difference. -/
theorem actual_radius_top_raw_price (coordinate:BurnolCompletedMellinCoordinate) (h:ℝ)
    (nonnegative:0≤h) (bound:q*Real.exp h<2*q) :
    inner ℂ (OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest coordinate h) (U m)=
      ∫ x:ℝ, if |x|≤q*Real.exp h then
        star ((((4*|x|:ℝ):ℂ)⁻¹)*movedTest coordinate h ((16:ℝ)*x)⁻¹)*fullTopRaw observation half x
        else 0 := by
  rw [←fourierL2.inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actual_radius_fourier_raw coordinate h,
    actual_transformed_outside coordinate h nonnegative,
    actual_full_top_raw observation nontrivial half] with x original outside top
  simp only [RCLike.inner_apply,starRingEnd_apply]
  change q*Real.exp h < |x| → F (OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest coordinate h) x=0 at outside
  by_cases inside:|x|≤q*Real.exp h
  · rw [if_pos inside,top (inside.trans_lt bound),original,mul_comm]
  · rw [if_neg inside,outside (lt_of_not_ge inside),star_zero,mul_zero]

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
