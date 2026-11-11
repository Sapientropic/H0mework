import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalUnitMellinSource.Band
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2
local notation "R" => burnolQuarterRestriction
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
open private original_fourier_step bandMean_succ from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.BandSource

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "d" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => unitPower observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

private theorem top_fourier_even : reflectL2 (F (U m))=F (U m) := by
  have positive:0<m:=generatedRiemannXiZeroOrder_pos observation nontrivial
  have before:m-1<m:=by omega
  have previous:=unitPower_physical observation nontrivial half (m-1) before
  have even:reflectL2 (U (m-1))=U (m-1):=mem_evenL2ClosedFace_iff.mp previous.2
  have next:m-1+1=m:=by omega
  have step:=original_fourier_step observation half (m-1)
  rw [next] at step
  rw [step,sourceVolterraResolvent_reflect,←fourierL2_reflectL2_commute,even]

def topBandRaw (x:ℝ) : ℂ :=
  bandMean d m+((|x|:ℝ):ℂ)^((d).value-1)*
    (bandCoefficient m*(bandLog |x|)^m-2*e)

/-- Both halves of the actual first cell have the full mean, logarithmic term, and Xi top. -/
theorem actual_top_band_raw :
    ∀ᵐ x:ℝ ∂volume, q < |x| → |x|<2*q → F (U m) x=topBandRaw observation half x := by
  have direct:=actual_top_fourier_first_cell observation nontrivial half
  have opposite:=negMeasurePreserving.quasiMeasurePreserving.ae direct
  have parity:=Lp.coeFn_compMeasurePreserving (F (U m)) negMeasurePreserving
  change (reflectL2 (F (U m)):ℝ→ℂ)=ᵐ[volume] fun x=>F (U m) (-x) at parity
  rw [top_fourier_even observation nontrivial half] at parity
  filter_upwards [direct,opposite,parity] with x pos neg reflected lower upper
  by_cases sign:0≤x
  · rw [abs_of_nonneg sign] at lower upper
    simpa only [topBandRaw,abs_of_nonneg sign] using pos lower upper
  · have negative:x<0:=lt_of_not_ge sign
    rw [abs_of_neg negative] at lower upper
    rw [reflected]
    simpa only [topBandRaw,abs_of_neg negative] using neg lower upper

private theorem top_quarter :
    R (F (U m))=bandMean d m • intervalConstant q+
      (-2*e) • SingularCounting.powerL2 (barC d) := by
  have paid:=OriginalKFiniteOrderRelease.UnitMellin.QuarterMeansSource.actual_top_fourier_quarter_power
    observation nontrivial half
  have positive:0<m:=generatedRiemannXiZeroOrder_pos observation nontrivial
  have next:m-1+1=m:=by omega
  have scalar:=bandMean_succ d (m-1)
  rw [next] at scalar
  rw [scalar]
  exact paid

def fullTopBandPrice (test:BurnolL2) (h:ℝ) : ℂ :=
  ∫ x:ℝ, if q < |x| ∧ |x|≤q*Real.exp h then
    star (F test x)*topBandRaw observation half x else 0

private theorem supported_top_pair (test:BurnolL2) (h:ℝ) (bound:q*Real.exp h<2*q)
    (outside:∀ᵐ x:ℝ ∂volume,q*Real.exp h < |x| → F test x=0) :
    inner ℂ test (U m)=
      bandMean d m*inner ℂ (R (F test)) (intervalConstant q)+
      (-2*e)*inner ℂ (R (F test)) (SingularCounting.powerL2 (barC d))+
      fullTopBandPrice observation half test h := by
  let f:=F test
  let v:=F (U m)
  have quarter:inner ℂ (originalPhysicalCutoff q f) v=inner ℂ (R f) (R v):=
    ContinuousLinearMap.adjoint_inner_left R v (R f)
  have band:inner ℂ (f-originalPhysicalCutoff q f) v=fullTopBandPrice observation half test h := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f (originalPhysicalCutoff q f),originalPhysicalCutoff_coeFn q f,
      actual_top_band_raw observation nontrivial half,outside] with x difference cutoff profile exterior
    simp only [RCLike.inner_apply,starRingEnd_apply]
    rw [difference,Pi.sub_apply,cutoff,mul_comm (v x)]
    change star (f x-(symmetricInterval q).indicator (f:ℝ→ℂ) x)*v x=
      if q < |x| ∧ |x|≤q*Real.exp h then star (f x)*topBandRaw observation half x else 0
    by_cases inner:q≥|x|
    · have within:x∈symmetricInterval q:=abs_le.mp inner
      rw [indicator_of_mem within,sub_self,star_zero,zero_mul,
        if_neg (fun inside=>not_lt_of_ge inner inside.1)]
    · have after:q < |x|:=lt_of_not_ge inner
      have beyond:x∉symmetricInterval q:=fun inside=>not_le_of_gt after (abs_le.mpr inside)
      rw [indicator_of_notMem beyond,sub_zero]
      by_cases inside:|x|≤q*Real.exp h
      · rw [if_pos ⟨after,inside⟩,profile after (inside.trans_lt bound)]
      · rw [if_neg (fun both=>inside both.2),exterior (lt_of_not_ge inside),star_zero,zero_mul]
  calc
    inner ℂ test (U m)=inner ℂ f v := (fourierL2.inner_map_map test (U m)).symm
    _=inner ℂ (originalPhysicalCutoff q f) v+inner ℂ (f-originalPhysicalCutoff q f) v := by
      rw [←inner_add_left,add_sub_cancel]
    _=_ := by
      rw [quarter,band]
      change inner ℂ (R f) (R (F (U m)))+_= _
      rw [top_quarter observation nontrivial half,inner_add_right,inner_smul_right,inner_smul_right]

/-- The original fixed consumer's transformed test has this complete actual Xi-order price. -/
theorem actual_radius_top_pair (coordinate:BurnolCompletedMellinCoordinate) (h:ℝ)
    (nonnegative:0≤h) (bound:q*Real.exp h<2*q) :
    inner ℂ (OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest coordinate h) (U m)=
      bandMean d m*inner ℂ (R (F (OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest coordinate h))) (intervalConstant q)+
      (-2*e)*inner ℂ (R (F (OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest coordinate h))) (SingularCounting.powerL2 (barC d))+
      fullTopBandPrice observation half (OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest coordinate h) h := by
  exact supported_top_pair observation nontrivial half _ h bound
    (actual_transformed_outside coordinate h nonnegative)

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
